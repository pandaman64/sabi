theory Rustv
  imports Simpl.Vcg
begin

datatype rust_error = invalid_ref

datatype pointer = ptr_val nat
datatype tag = tag_val nat
datatype val = int_val int
record tagged_ref = 
  pointer :: pointer
  tag :: tag

fun the_ptr :: "pointer \<Rightarrow> nat" where
  "the_ptr (ptr_val p) = p"

fun the_tag :: "tag \<Rightarrow> nat" where
  "the_tag (tag_val t) = t"

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

lemma wf_tags_update:
  assumes
    "wf_tags tag_stack"
    "ts \<noteq> []"
  shows
    "wf_tags (tag_stack[p := ts])"
  using assms(1) assms(2) set_update_subset_insert wf_tags_spec by fastforce

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

(* sometimes collect_tags.simps confuses the automatic reasoner *)
declare collect_tags.simps[simp del]

lemma collect_tags_update[simp, intro]:
  "t \<in> collect_tags (ts[p := x]) \<Longrightarrow> t \<in> collect_tags ts \<or> t \<in> set x"
  by (metis collect_tags_spec length_list_update nth_list_update nth_list_update_neq)

lemma [simp, intro]: "collect_tags (ts @ [t]) = set t \<union> (collect_tags ts)"
proof (induction ts)
qed (auto simp add: collect_tags.simps)

lemma [simp, intro]: "finite (collect_tags ts)"
proof (induction ts)
qed (simp add: collect_tags.simps)+

fun wf_heap :: "'a globals_ram_scheme \<Rightarrow> bool" where
  "wf_heap s \<longleftrightarrow>
    length (memory s) = length (tags s)
    \<and> wf_tags (tags s)
    \<and> collect_tags (tags s) \<subseteq> set (issued_tags s)"

(* when we use a unique reference, invalidate all children *)
fun invalidate_children :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> 'a globals_ram_scheme" where
  "invalidate_children r s = 
    (let p = the_ptr (pointer r);
         ts = tags s ! p;
         ts' = dropWhile ((\<noteq>) (tag r)) ts in
    s\<lparr> tags := (tags s)[p := ts'] \<rparr>)"

fun_cases invalidate_childrenE: "invalidate_children r s = s'"

lemma dropWhile_hd_eq[simp, intro]: "x \<in> set xs \<Longrightarrow> hd (dropWhile ((\<noteq>) x) xs) = x"
proof (induction xs)
qed auto

lemma dropWhile_in[simp, intro]: "x \<in> set xs \<Longrightarrow> x \<in> set (dropWhile ((\<noteq>) x) xs)"
proof (induction xs)
qed auto

lemma "\<lbrakk>invalidate_children r s = s'; the_ptr (pointer r) < length (tags s); tag r \<in> set ((tags s') ! the_ptr (pointer r))\<rbrakk>
  \<Longrightarrow> hd ((tags s') ! the_ptr (pointer r)) = tag r"
  apply (erule invalidate_childrenE)
  by (simp add: Let_def set_dropWhileD)

lemma invalidate_children_memory[intro]:
  "invalidate_children r s = s' \<Longrightarrow> memory s' = memory s"
  apply (erule invalidate_children.elims)
  by (simp add: Let_def)

fun memwrite
  :: "tagged_ref \<Rightarrow> val \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> 'a globals_ram_scheme"
  where
  "memwrite p v s =
    (let memory = memory s in
    let memory' = memory[the_ptr (pointer p) := v] in
    s\<lparr> memory := memory' \<rparr>)"

lemma memwrite_written[simp]:
  fixes p v s s'
  assumes "s' = memwrite p v s"
          "the_ptr (pointer p) < length (memory s)"
  shows "(memory s') ! the_ptr (pointer p) = v"
  by (simp add: assms(1) assms(2))
lemma memwrite_not_written[simp]:
  fixes p p' v s s'
  assumes "s' = memwrite p v s"
          "pointer p \<noteq> pointer p'"
        shows "(memory s') ! the_ptr (pointer p') = (memory s) ! the_ptr (pointer p')"
  apply (simp add: assms(1))
  by (metis assms(2) nth_list_update_neq the_ptr.elims)
lemma memwrite_tags:
  fixes p v s s'
  assumes "s' = memwrite p v s"
  shows "tags s' = tags s"
  by (simp add: assms)

fun max_list :: "nat list \<Rightarrow> nat" where
  "max_list [] = 0" |
  "max_list (x # xs) = max x (max_list xs)"

lemma max_list_ge: "\<forall>x \<in> set xs. max_list xs \<ge> x"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x' xs)
  then show ?case by auto
qed

lemma suc_max_list_gt: "\<forall>x \<in> set xs. Suc (max_list xs) > x"
  using max_list_ge by fastforce

fun new_tag :: "'a globals_ram_scheme \<Rightarrow> tag" where
  "new_tag s = tag_val (Suc (max_list (map the_tag (issued_tags s))))"

fun_cases new_tag_elims: "new_tag s = t"

lemma new_tag_gt: "\<forall>t \<in> set (issued_tags s). the_tag (new_tag s) > the_tag t"
  using suc_max_list_gt by simp

lemma new_tag_notin[simp, intro]: "new_tag s = t \<Longrightarrow> t \<notin> set (issued_tags s)"
  using new_tag_gt by blast

lemma new_tag_notin_at:
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
    (let p = the_ptr (pointer r) in
    let t = tag r in
    p < length (memory s) \<and> t \<in> set (tags s ! p))"

lemma writable_update[simp]: "writable r (memwrite r' v s) = writable r s"
  by auto

lemma writable_invalidated[intro]: "writable r s \<Longrightarrow> writable r (invalidate_children r s)"
  apply (simp add: Let_def)
  apply auto
  by (metis dropWhile_in list_update_beyond not_le nth_list_update_eq)

fun new_pointer :: "'a globals_ram_scheme \<Rightarrow> pointer" where
  "new_pointer s = ptr_val (length (memory s))"

fun heap_new :: "val \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> tagged_ref * 'a globals_ram_scheme" where
  "heap_new v s = 
    (let p = new_pointer s;
         t = new_tag s in
    (\<lparr> pointer = p, tag = t \<rparr>,
     s\<lparr> memory := memory s @ [v], tags := tags s @ [[t]], issued_tags := t # issued_tags s \<rparr>))"

fun_cases heap_new_elims: "heap_new v s = (r, s')"

lemma heap_new_writable: "\<lbrakk>wf_heap s; heap_new v s = (r', s')\<rbrakk> \<Longrightarrow> writable r' s'"
  apply (erule heap_new_elims)
  by (simp add: Let_def)

lemma heap_new_wf_heap_update: "\<lbrakk>wf_heap s; heap_new v s = (r', s')\<rbrakk> \<Longrightarrow> wf_heap s'"
  apply (erule heap_new_elims)
  by (auto simp add: Let_def)

fun reborrow :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> tagged_ref * 'a globals_ram_scheme" where
  "reborrow r s =
    (let p = the_ptr (pointer r) in
    let t = new_tag s in
    let tags = (tags s)[p := t # ((tags s) ! p)] in
    (\<lparr> pointer = pointer r, tag = t \<rparr>, s\<lparr> tags := tags, issued_tags := t # issued_tags s \<rparr>))"

fun_cases reborrow_elims: "reborrow r s = (r', s')"

lemma reborrow_pointer: "reborrow r s = (r', s') \<Longrightarrow> pointer r' = pointer r"
  apply (erule reborrow_elims)
  by (auto simp: Let_def)

lemma reborrow_update_heap: "\<lbrakk>wf_heap s; writable r s; reborrow r s = (r', s')\<rbrakk> \<Longrightarrow> wf_heap s'"
  apply (erule reborrow_elims)
  apply (auto simp add: Let_def)
  using wf_tags_update apply simp
  by (meson collect_tags_spec collect_tags_update in_mono set_ConsD)

lemma reborrow_writable: "\<lbrakk>wf_heap s; writable r s; reborrow r s = (r', s')\<rbrakk> \<Longrightarrow> writable r s'"
  apply (erule reborrow_elims)
  by (simp add: Let_def)

end
