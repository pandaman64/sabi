theory Rustv
  imports Simpl.Vcg Simpl.Simpl_Heap
begin

datatype rust_error = invalid_ref

type_synonym tag = nat
datatype val = int_val int
record tagged_ref = 
  pointer :: ref
  tag :: tag

record globals_ram =
  memory :: "val list"
  tags :: "tag list list" (* `tag set list list` in the presence of shared pointer *)
  issued_tags :: "tag list"

fun wf_tags :: "tag list list \<Rightarrow> bool" where
  "wf_tags [] = True" |
  "wf_tags ([] # _) = False" |
  "wf_tags (_ # t) = wf_tags t"
lemma wf_tags_spec: "wf_tags ts \<longleftrightarrow> (\<forall>t \<in> set ts. t \<noteq> [])"
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)

  have 1: "wf_tags (a # ts) \<Longrightarrow> (\<forall>t \<in> set (a # ts). t \<noteq> [])"
  proof (cases "a # ts" rule: wf_tags.elims(2))
    show "wf_tags (a # ts) \<Longrightarrow> wf_tags (a # ts)" by simp
  next
    fix v tail

    assume "wf_tags ts"
    then have "\<forall>t \<in> set ts. t \<noteq> []" using Cons.IH by auto
    moreover assume "a = v # tail"
    thus ?thesis using calculation by auto
  qed

  have 2: "(\<forall>t \<in> set (a # ts). t \<noteq> []) \<Longrightarrow> wf_tags (a # ts)"
    using Cons.IH wf_tags.elims(3) by fastforce

  show ?case using 1 2 by (rule iffI)
qed

lemma [simp, intro]: "\<lbrakk>wf_tags ts; x \<noteq> []\<rbrakk> \<Longrightarrow> wf_tags (ts @ [x])"
proof (induction ts)
  case Nil
  then show ?case by (simp add: wf_tags_spec)
next
  case (Cons a ts)
  then show ?case by (simp add: wf_tags_spec)
qed

fun collect_tags :: "tag list list \<Rightarrow> tag set" where
  "collect_tags ts = foldr (\<lambda>ts accum. set ts \<union> accum) ts {}"
lemma collect_tags_spec: "t \<in> collect_tags ts \<longleftrightarrow> (\<exists>i < length ts. t \<in> set (ts ! i))"
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons h ts)
  have 1: "collect_tags (h # ts) = set h \<union> collect_tags ts" by simp

  show ?case
  proof
    assume "t \<in> collect_tags (h # ts)"
    then have 2: "t \<in> set h \<or> t \<in> collect_tags ts" using 1 by simp
    thus "\<exists>i < length (h # ts). t \<in> set ((h # ts) ! i)"
    proof (cases rule: disjE[OF 2])
      case 1
      then show ?thesis by auto
    next
      case 2
      then show ?thesis using Cons.IH by auto
    qed
  next
    assume "\<exists>i < length (h # ts). t \<in> set ((h # ts) ! i)"
    then obtain i where
      3: "i < length (h # ts)" and
      4: "t \<in> set ((h # ts) ! i)"
      by auto
    thus "t \<in> collect_tags (h # ts)"
    proof (cases "i = 0")
      case True
      then show ?thesis using 4 by auto
    next
      case False
      then have "t \<in> set (ts ! (i - 1))" using 4 by auto
      then show ?thesis using 3 Cons.IH \<open>i \<noteq> 0\<close> by auto
    qed
  qed
qed

lemma collect_tags_update[simp, intro]: "t \<in> collect_tags (ts[p := x]) \<Longrightarrow> t \<in> collect_tags ts \<or> t \<in> set x"
  by (metis collect_tags_spec length_list_update nth_list_update nth_list_update_neq)

lemma [simp, intro]: "collect_tags (ts @ [t]) = set t \<union> (collect_tags ts)"
proof (induction ts)
qed auto

lemma [simp, intro]: "finite (collect_tags ts)"
proof (induction ts)
qed simp+

fun wf_heap :: "'a globals_ram_scheme \<Rightarrow> bool" where
  "wf_heap s \<longleftrightarrow>
    length (memory s) = length (tags s)
    \<and> wf_tags (tags s)
    \<and> collect_tags (tags s) \<subseteq> set (issued_tags s)"

(* when we use a unique reference, invalidate all children *)
fun invalidate_children :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> 'a globals_ram_scheme" where
  "invalidate_children r s = 
    (let p = Rep_ref (pointer r);
         ts = tags s ! p;
         ts' = takeWhile ((\<noteq>) (tag r)) ts @ [tag r] in
    s\<lparr> tags := (tags s)[p := ts'] \<rparr>)"

lemma "\<lbrakk>invalidate_children r s = s'; Rep_ref (pointer r) < length (tags s)\<rbrakk>
  \<Longrightarrow> last ((tags s') ! Rep_ref (pointer r)) = tag r"
  apply (erule invalidate_children.elims)
  by (simp add: Let_def)
lemma "\<lbrakk>invalidate_children r s = s'; Rep_ref (pointer r) < length (tags s)\<rbrakk>
  \<Longrightarrow> tag r \<notin> set (butlast ((tags s') ! Rep_ref (pointer r)))"
  apply (erule invalidate_children.elims)
  apply (simp add: Let_def)
  apply auto
  apply (drule set_takeWhileD)
  by auto

lemma invalidate_children_memory[intro]:
  "invalidate_children r s = s' \<Longrightarrow> memory s' = memory s"
  apply (erule invalidate_children.elims)
  by (simp add: Let_def)

fun memwrite
  :: "tagged_ref \<Rightarrow> val \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> 'a globals_ram_scheme"
  where
  "memwrite p v s =
    (let memory = memory s in
    let memory' = memory[Rep_ref (pointer p) := v] in
    s\<lparr> memory := memory' \<rparr>)"

lemma memwrite_written[simp]:
  fixes p v s s'
  assumes "s' = memwrite p v s"
          "Rep_ref (pointer p) < length (memory s)"
  shows "(memory s') ! Rep_ref (pointer p) = v"
  by (simp add: assms(1) assms(2))
lemma memwrite_not_written[simp]:
  fixes p p' v s s'
  assumes "s' = memwrite p v s"
          "pointer p \<noteq> pointer p'"
  shows "(memory s') ! Rep_ref (pointer p') = (memory s) ! Rep_ref (pointer p')"
  by (simp add: Rep_ref_inject assms(2) assms(1))
lemma memwrite_tags:
  fixes p v s s'
  assumes "s' = memwrite p v s"
  shows "tags s' = tags s"
  by (simp add: assms)

fun new_tag :: "'a globals_ram_scheme \<Rightarrow> tag" where
  "new_tag s = fold (\<lambda>t accum. max t accum) (issued_tags s) 0 + 1"

fun_cases new_tag_elims: "new_tag s = t"

lemma [simp, intro]: "new_tag s = t \<Longrightarrow> t \<notin> set (issued_tags s)"
  apply (erule new_tag_elims)
  by (metis List.finite_set Max.set_eq_fold Max_ge insert_iff lessI list.set(2) not_le)

lemma
  assumes
    "wf_heap s"
    "new_tag s = t"
    "r < length (tags s)"
  shows "t \<notin> set (tags s ! r)"
proof -
  have "t \<notin> set (issued_tags s)" using assms by auto
  then have "t \<notin> collect_tags (tags s)" using assms by auto
  then have "\<not>(\<exists>i < length (tags s). t \<in> set ((tags s) ! i))"
    using collect_tags_spec by auto
  thus ?thesis using assms by auto
qed

fun writable :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> bool" where
  "writable r s = 
    (let p = Rep_ref (pointer r) in
    let t = tag r in
    p < length (memory s) \<and> t \<in> set (tags s ! p))"

lemma writable_update[simp]: "writable r (memwrite r' v s) = writable r s"
  by auto

lemma writable_invalidated[intro]: "writable r s \<Longrightarrow> writable r (invalidate_children r s)"
  apply (simp add: Let_def)
  apply auto
  by (metis in_set_conv_decomp length_list_update 
      nth_equalityI nth_list_update_eq nth_list_update_neq)

fun new_pointer :: "'a globals_ram_scheme \<Rightarrow> ref" where
  "new_pointer s = Abs_ref (length (memory s))"

fun heap_new :: "val \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> tagged_ref * 'a globals_ram_scheme" where
  "heap_new v s = 
    (let p = new_pointer s;
         t = new_tag s in
    (\<lparr> pointer = p, tag = t \<rparr>,
     s\<lparr> memory := memory s @ [v], tags := tags s @ [[t]], issued_tags := issued_tags s @ [t]\<rparr>))"

fun_cases heap_new_elims: "heap_new v s = (r, s')"

lemma heap_new_writable: "\<lbrakk>wf_heap s; heap_new v s = (r', s')\<rbrakk> \<Longrightarrow> writable r' s'"
  apply (erule heap_new_elims)
  by (simp add: Let_def Abs_ref_inverse ref_def)

lemma heap_new_wf_heap_update: "\<lbrakk>wf_heap s; heap_new v s = (r', s')\<rbrakk> \<Longrightarrow> wf_heap s'"
  apply (erule heap_new_elims)
  by (auto simp add: Let_def simp del: collect_tags.simps)

fun reborrow :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> tagged_ref * 'a globals_ram_scheme" where
  "reborrow r s =
    (let p = Rep_ref (pointer r) in
    let t = new_tag s in
    let tags = (tags s)[p := (tags s) ! p @ [t]] in
    (\<lparr> pointer = pointer r, tag = t \<rparr>, s\<lparr> tags := tags, issued_tags := issued_tags s @ [t] \<rparr>))"

fun_cases reborrow_elims: "reborrow r s = (r', s')"

lemma reborrow_pointer: "reborrow r s = (r', s') \<Longrightarrow> pointer r' = pointer r"
  apply (erule reborrow_elims)
  by (auto simp: Let_def)

lemma "\<lbrakk>wf_heap s; writable r s; reborrow r s = (r', s')\<rbrakk> \<Longrightarrow> wf_heap s'"
  apply (erule reborrow_elims)
  apply (auto simp add: Let_def simp del: collect_tags.simps)
   apply (metis Nil_is_append_conv basic_trans_rules(31) insertE
          not_Cons_self set_update_subset_insert wf_tags_spec)
  apply auto
  by (metis UnE basic_trans_rules(31) collect_tags.simps collect_tags_spec collect_tags_update
      empty_iff insertE list.set(1) list.set(2) set_append)

lemma "\<lbrakk>wf_heap s; writable r s; reborrow r s = (r', s')\<rbrakk> \<Longrightarrow> writable r s'"
  apply (erule reborrow_elims)
  by (simp add: Let_def)

record deriv_env = globals_ram +
  p :: tagged_ref
  x :: tagged_ref

definition deriv_body :: "(deriv_env, 'p, rust_error) com" where
  "deriv_body = Guard invalid_ref {s. writable (p s) s} 
    (Seq (Basic (\<lambda>s. invalidate_children (p s) s))
         (Basic (\<lambda>s. (memwrite (p s) (int_val 101) s))))"

lemma partial: "\<Gamma> \<turnstile> {s. writable (p s) s} deriv_body {s. memory s ! (Rep_ref (pointer (p s))) = int_val 101}"
  unfolding deriv_body_def
  apply (hoare_rule HoarePartial.Guard)
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (simp add: Let_def)
  by auto

lemma "\<Gamma> \<turnstile>\<^sub>t {s. writable (p s) s} deriv_body {s. memory s ! (Rep_ref (pointer (p s))) = int_val 101}"
  unfolding deriv_body_def
  apply (hoare_rule HoareTotal.Guard)
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (simp add: Let_def)
  by auto

lemma "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^sub>t 
  {s. s = \<sigma> \<and> writable (p s) s}
  deriv_body
  {s. memory s = (memory \<sigma>)[Rep_ref (pointer (p \<sigma>)) := int_val 101]}"
  unfolding deriv_body_def
  apply (hoare_rule HoareTotal.Guard)
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (simp add: Let_def)
  by auto

lemma "\<Gamma> \<turnstile>\<^sub>t {s. writable (p s) s \<and> wf_heap s} deriv_body {s. writable (p s) s}"
  unfolding deriv_body_def
  apply vcg_step
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (simp add: Let_def)
  by auto

definition reb_body :: "(deriv_env, 'p, rust_error) com" where
  "reb_body = Guard invalid_ref {s. writable (p s) s}
    (Seq (Basic (\<lambda>s. invalidate_children (p s) s))
         (Basic (\<lambda>s.
           (let (p', s') = reborrow (p s) s in
           s'\<lparr> x := p' \<rparr>))))"

lemma "\<Gamma> \<turnstile>\<^sub>t 
  {s. writable (p s) s \<and> wf_heap s}
  reb_body
  {s. writable (x s) s}"
  unfolding reb_body_def
  apply vcg_step
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (simp add: Let_def)
  by auto

record no_alias_env = globals_ram +
  x :: tagged_ref (* locals are represented by owning pointer *)
  ref1 :: tagged_ref
  ref2 :: tagged_ref

definition no_alias_body :: "(no_alias_env, 'p, rust_error) com" where
  "no_alias_body =
    (Seq (Basic (\<lambda>s. (let (r, s') = heap_new (int_val 100) s in
                     s'\<lparr> x := r \<rparr>)))

    (Seq (Guard invalid_ref {s. writable (x s) s}
           (Seq (Basic (\<lambda>s. invalidate_children (x s) s))
                (Basic (\<lambda>s.
                  (let (r, s') = reborrow (x s) s in
                  s'\<lparr> ref1 := r \<rparr>)))))
    (Seq (Guard invalid_ref {s. writable (ref1 s) s}
           (Seq (Basic (\<lambda>s. invalidate_children (ref1 s) s))
                (Basic (\<lambda>s. memwrite (ref1 s) (int_val 200) s))))

    (Seq (Guard invalid_ref {s. writable (x s) s}
           (Seq (Basic (\<lambda>s. invalidate_children (x s) s))
                (Basic (\<lambda>s.
                  (let (r, s') = reborrow (x s) s in
                  s'\<lparr> ref2 := r \<rparr>)))))
         (Guard invalid_ref {s. writable (ref2 s) s}
           (Seq (Basic (\<lambda>s. invalidate_children (ref2 s) s))
                (Basic (\<lambda>s. memwrite (ref2 s) (int_val 300) s))))
    ))))"

(* Termination *)
lemma "\<Gamma> \<turnstile>\<^sub>t {s. wf_heap s} no_alias_body {s. True}"
  unfolding no_alias_body_def
  apply vcg_step
       prefer 2
       apply vcg_step
       apply vcg_step
      apply vcg_step
     apply vcg_step
      prefer 2
      apply vcg_step
      apply vcg_step
     apply vcg_step
    apply vcg_step
     prefer 2
     apply vcg_step
     apply vcg_step
    apply vcg_step
   apply vcg_step
    prefer 2
    apply vcg_step
    apply vcg_step
   apply vcg_step
  apply vcg_step
  apply vcg_step
  apply (simp add: Let_def Abs_ref_inverse ref_def)
  by auto

(* Termination, by full VCG *)
lemma "\<Gamma> \<turnstile>\<^sub>t {s. wf_heap s} no_alias_body {s. True}"
  unfolding no_alias_body_def
  apply vcg
  by (auto simp: Let_def Abs_ref_inverse ref_def)

(* Spec of the program *)
lemma "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s}
  no_alias_body
  {s. (let p = Rep_ref (pointer (x s)) in
      memory s ! p = int_val 300 \<and>
      writable (x s) s \<and> \<not>writable (ref1 s) s \<and> writable (ref2 s) s)}"
  unfolding no_alias_body_def
  apply vcg
  by (auto simp: Let_def Abs_ref_inverse ref_def simp del: collect_tags.simps)

end
