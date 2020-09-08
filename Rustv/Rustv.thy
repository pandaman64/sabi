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

datatype ref_kind = Unique | SharedReadWrite | SharedReadOnly
type_synonym 'a stack = "'a list"

record globals_ram =
  memory :: "val list"
  tags :: "(ref_kind * tag set) stack list"
  issued_tags :: "tag list"

inductive wf_reborrow :: "(ref_kind * tag set) stack \<Rightarrow> bool" where
  (* An allocation root is a Unique reference (Box) *)
  BorrowRoot: "wf_reborrow [(Unique, {t})]" |

  (* Reborrowing from a Unique reference *)
  ReborrowUniqueUnique:
    "wf_reborrow ((Unique, {t}) # tail) \<Longrightarrow> wf_reborrow ((Unique, {t'}) # (Unique, {t}) # tail)" |
  ReborrowUniqueSRW:
    "wf_reborrow ((Unique, {t}) # tail) \<Longrightarrow> wf_reborrow ((SharedReadWrite, ts) # (Unique, {t}) # tail)" |
  ReborrowUniqueSRO:
    "wf_reborrow ((Unique, {t}) # tail) \<Longrightarrow> wf_reborrow ((SharedReadOnly, ts) # (Unique, {t}) # tail)" |

  (* Reborrowing from a SharedReadWrite *)
  ReborrowSRWUnique:
    "wf_reborrow ((SharedReadWrite, ts) # tail)
 \<Longrightarrow> wf_reborrow ((Unique, {t'}) # (SharedReadWrite, ts) # tail)" |
  ReborrowSRWSRW:
    "wf_reborrow ((SharedReadWrite, ts) # tail)
 \<Longrightarrow> wf_reborrow ((SharedReadWrite, insert t ts) # tail)" |
  ReborrowSRWSRO:
    "wf_reborrow ((SharedReadWrite, ts) # tail)
 \<Longrightarrow> wf_reborrow ((SharedReadOnly, ts') # (SharedReadWrite, ts) # tail)" |

  (* Reborrowing from a SharedReadOnly gives only a shared reference *)
  ReborrowSROSRO:
    "wf_reborrow ((SharedReadOnly, ts) # tail)
 \<Longrightarrow> wf_reborrow ((SharedReadOnly, insert t ts) # tail)"

inductive_cases wf_reborrow_elims: "wf_reborrow stack"

lemma wf_reborrow_nonempty:
  assumes "wf_reborrow stack"
  shows "stack \<noteq> []"
using assms proof (rule wf_reborrow_elims)
qed auto

lemma wf_reborrow_root: "wf_reborrow stack \<Longrightarrow> \<exists>t. last stack = (Unique, {t})"
proof (induction rule: wf_reborrow.induct)
qed auto

lemma unique_ref_head:
  assumes "wf_reborrow ((Unique, ts) # end)"
  shows "\<exists>t. ts = {t}"
using assms proof (rule wf_reborrow_elims)
qed auto

lemma unique_ref:
  assumes
    "wf_reborrow stack"
    "(Unique, ts) \<in> set stack"
  shows "\<exists>t. ts = {t}"
using assms(1) assms(2) proof (induction rule: wf_reborrow.induct)
qed auto

lemma wf_reborrow_pop:
  assumes
    "wf_reborrow stack"
    "stack = st1 # st2 # rest"
  shows "wf_reborrow (st2 # rest)"
using assms proof (induction arbitrary: st1 rule: wf_reborrow.induct)
qed auto

lemma wf_reborrow_pop':
  fixes top rest
  assumes
    "wf_reborrow (top # rest)"
    "rest \<noteq> []"
  shows "wf_reborrow rest"
using assms proof (induction "(top # rest)" arbitrary: top rule: wf_reborrow.induct)
qed auto

fun stack_finite :: "(ref_kind * tag set) stack \<Rightarrow> bool" where
  "stack_finite [] = True" |
  "stack_finite (s # stack) = (finite (snd s) \<and> stack_finite stack)"

lemma stack_finite_spec: "stack_finite stack \<longleftrightarrow> (\<forall>s \<in> set stack. finite (snd s))"
proof (induction stack)
qed auto

fun wf_tags :: "(ref_kind * tag set) stack list \<Rightarrow> bool" where
  "wf_tags [] = True" |
  "wf_tags (stack # ts) = (wf_reborrow stack \<and> stack_finite stack \<and> wf_tags ts)"

lemma wf_tags_spec:
  "wf_tags ts \<longleftrightarrow> (\<forall>stack \<in> set ts. wf_reborrow stack \<and> stack_finite stack)"
proof (induction ts)
qed auto

lemma list_update_forall:
  "\<lbrakk>\<forall>x \<in> set xs. P x; P x'\<rbrakk> \<Longrightarrow> \<forall>x \<in> set (xs[p := x']). P x"
  using set_update_subset_insert by fastforce

lemma wf_tags_update:
  assumes
    "wf_tags ts"
    "wf_reborrow stack"
    "stack_finite stack"
  shows "wf_tags (ts[p := stack])"
  using assms set_update_subset_insert wf_tags_spec by fastforce

fun collect_tags_stack :: "(ref_kind * tag set) stack \<Rightarrow> tag set" where
  "collect_tags_stack stack = \<Union>(set (map snd stack))"

fun collect_tags :: "(ref_kind * tag set) stack list \<Rightarrow> tag set" where
  "collect_tags [] = {}" |
  "collect_tags (stack # ts) = collect_tags_stack stack \<union> collect_tags ts"
lemma collect_tags_spec:
  "t \<in> collect_tags ts \<longleftrightarrow> (\<exists>stack \<in> set ts. \<exists>entry \<in> set (map snd stack). t \<in> entry)"
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons stack ts)
  show ?case
  proof
    assume "t \<in> collect_tags (stack # ts)"
    then have "t \<in> \<Union>(set (map snd stack)) \<or> t \<in> collect_tags ts" by simp
    then show "\<exists>s \<in> set (stack # ts). \<exists>entry \<in> set (map snd s). t \<in> entry"
    proof (rule disjE)
      assume "t \<in> \<Union>(set (map snd stack))"
      then show ?thesis by simp
    next
      assume "t \<in> collect_tags ts"
      then show ?thesis by (simp add: Cons.IH)
    qed
  next
    assume "\<exists>stack \<in> set (stack # ts). \<exists>entry \<in> set (map snd stack). t \<in> entry"
    then obtain s entry where
      1: "s \<in> set (stack # ts)" and
      2: "entry \<in> set (map snd s)" and
      3: "t \<in> entry"
      by auto

    have "s = stack \<or> s \<in> set ts" using 1 by auto
    then show "t \<in> collect_tags (stack # ts)"
    proof (rule disjE)
      assume "s = stack"
      then have "\<exists>entry \<in> set (map snd stack). t \<in> entry" using 2 3 by auto
      then show ?thesis by simp
    next
      assume "s \<in> set ts"
      then have "\<exists>s \<in> set ts. \<exists>entry \<in> set (map snd s). t \<in> entry"
        using 2 3 by auto
      then show ?thesis by (simp add: Cons.IH)
    qed
  qed
qed

lemma collect_tags_spec':
  "t \<in> collect_tags ts \<longleftrightarrow> (\<exists>stack \<in> set ts. t \<in> collect_tags_stack stack)"
  using collect_tags_spec by fastforce

lemma collect_tags_update[simp, intro]:
  "t \<in> collect_tags (ts[p := stack]) \<Longrightarrow> t \<in> collect_tags ts \<or> t \<in> collect_tags_stack stack"
  using collect_tags_spec set_update_subset_insert subset_code(1) by fastforce

lemma collect_tags_last[simp, intro]:
  "collect_tags (ts @ [stack]) = collect_tags_stack stack \<union> (collect_tags ts)"
proof (induction ts)
qed auto

lemma collect_tags_stack_finite:
  assumes "stack_finite stack"
  shows "finite (collect_tags_stack stack)"
  using assms stack_finite_spec by auto

lemma collect_tags_finite[simp, intro]: "wf_tags ts \<Longrightarrow> finite (collect_tags ts)"
proof (induction ts)
  case (Cons stack ts)
  then have "stack_finite stack \<and> finite (collect_tags ts)" by auto
  then show ?case using collect_tags_stack_finite by auto
qed auto

fun wf_heap :: "'a globals_ram_scheme \<Rightarrow> bool" where
  "wf_heap s \<longleftrightarrow>
    length (memory s) = length (tags s)
    \<and> wf_tags (tags s)
    \<and> collect_tags (tags s) \<subseteq> set (issued_tags s)"

(* when we use a unique reference, invalidate all children *)
fun invalidate_children :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> 'a globals_ram_scheme" where
  "invalidate_children r s =
    (let p = the_ptr (pointer r);
         stack = tags s ! p;
         stack' = dropWhile (\<lambda>entry. (tag r) \<notin> snd entry) stack in
    s\<lparr> tags := (tags s)[p := stack'] \<rparr>)"

fun_cases invalidate_childrenE: "invalidate_children r s = s'"

lemma hd_dropWhile_stack:
  assumes
    "dropWhile (\<lambda>entry. (tag r) \<notin> snd entry) stack = stack'"
    "\<exists>entry \<in> set stack. (tag r) \<in> snd entry"
  shows "tag r \<in> snd (hd stack')"
  by (metis assms(1) assms(2) dropWhile_eq_Nil_conv hd_dropWhile)

lemma dropWhile_stack_reborrow:
  "wf_reborrow stack \<and> dropWhile P stack \<noteq> [] \<Longrightarrow> wf_reborrow (dropWhile P stack)"
proof (induction stack)
  case Nil
  then show ?case using wf_reborrow_nonempty by simp
next
  case (Cons top rest)

  show ?case
  proof (cases "P top")
    case True
    moreover have "dropWhile P rest \<noteq> []" using Cons.prems calculation by auto
    moreover have "rest \<noteq> []" using calculation by auto
    moreover have "wf_reborrow rest" using calculation Cons.prems wf_reborrow_pop' by auto
    ultimately show ?thesis using Cons.IH by auto
  next
    case False
    then have "dropWhile P (top # rest) = top # rest" by simp
    then show ?thesis using Cons.prems by simp
  qed
qed
(*
lemma invalidate_wf_tags:
  assumes
    "invalidate_children r s = s'"
    "\<exists>entry \<in> set ((tags s) ! the_ptr (pointer r)). (tag r) \<in> snd entry"
    "wf_tags (tags s)"
  shows "wf_tags (tags s')"
  sorry

lemma
  assumes
    "invalidate_children r s = s'"
    "wf_tags (tags s)"
    "the_ptr (pointer r) < length (tags s)"
    "tag r \<in> collect_tag_stack ((tags s') ! the_ptr (pointer r))"
  shows "tag r \<in> snd (hd ((tags s') ! the_ptr (pointer r)))"
  using assms(1) apply (rule invalidate_childrenE)
  apply (simp add: Let_def)
  by (simp add: Let_def set_dropWhileD) *)

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
  shows "t \<notin> collect_tags_stack (tags s ! r)"
proof -
  have "t \<notin> set (issued_tags s)" using assms by auto
  then have "t \<notin> collect_tags (tags s)" using assms by auto
  thus ?thesis using assms using collect_tags_spec' nth_mem by blast
qed

fun writable_stack :: "tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> bool" where
  "writable_stack t [] \<longleftrightarrow> False" |
  "writable_stack t ((Unique, ts) # stack) \<longleftrightarrow> t \<in> ts \<or> writable_stack t stack" |
  "writable_stack t ((SharedReadWrite, ts) # stack) \<longleftrightarrow> t \<in> ts \<or> writable_stack t stack" |
  "writable_stack t ((SharedReadOnly, ts) # stack) \<longleftrightarrow> writable_stack t stack"

fun writable :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> bool" where
  "writable r s =
    (let p = the_ptr (pointer r) in
    let t = tag r in
    p < length (memory s) \<and> writable_stack t (tags s ! p))"

lemma writable_update[simp]: "writable r (memwrite r' v s) = writable r s"
  by simp

lemma writable_invalidated[intro]: "writable r s \<Longrightarrow> writable r (invalidate_children r s)"
  apply (simp add: Let_def)
  apply (auto simp add: nth_list_update_eq)
  by (metis dropWhile_in list_update_beyond not_le nth_list_updateeq)

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
  by (meson collect_tags_spec collect_tags_update in_mono set_CosD)

lemma reborrow_writable: "\<lbrakk>wf_heap s; writable r s; reborrow r s = (r', s')\<rbrakk> \<Longrightarrow> writable r s'"
  apply (erule reborrow_elims)
  by (simp add: Let_def)

end
