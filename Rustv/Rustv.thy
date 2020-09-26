theory Rustv
  imports Simpl.Vcg Defs BorrowStack
begin

abbreviation "collect_tags_stack == BorrowStack.collect_tags"
abbreviation "pop_tags_stack == BorrowStack.pop_tags"
abbreviation "writable_stack == BorrowStack.writable"

record globals_ram =
  memory :: "val list"
  tags :: "(ref_kind * tag set) stack list"
  issued_tags :: "tag list"

fun wf_tags :: "(ref_kind * tag set) stack list \<Rightarrow> bool" where
  "wf_tags [] = True" |
  "wf_tags (stack # ts) = (wf_reborrow stack \<and> stack_finite stack \<and> wf_tags ts)"

lemma wf_tags_spec:
  "wf_tags ts \<longleftrightarrow> (\<forall>stack \<in> set ts. wf_reborrow stack \<and> stack_finite stack)"
proof (induction ts)
qed auto

lemma wf_tags_snoc:
  "wf_tags (ts @ [stack]) \<longleftrightarrow> wf_tags ts \<and> wf_reborrow stack \<and> stack_finite stack"
  using wf_tags_spec by auto

lemma list_update_forall:
  "\<lbrakk>\<forall>x \<in> set xs. P x; P x'\<rbrakk> \<Longrightarrow> \<forall>x \<in> set (xs[p := x']). P x"
  using set_update_subset_insert by fastforce

lemma wf_tags_update:
  assumes
    "wf_tags ts"
    "wf_reborrow stack"
  shows "wf_tags (ts[p := stack])"
  using assms set_update_subset_insert wf_tags_spec by fastforce

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

lemma collect_tags_update_subset:
  "collect_tags (ts[p := stack]) \<subseteq> collect_tags_stack stack \<union> collect_tags ts"
  using collect_tags_update by blast

lemma collect_tags_last[simp, intro]:
  "collect_tags (ts @ [stack]) = collect_tags_stack stack \<union> (collect_tags ts)"
proof (induction ts)
qed auto

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

fun pop_tags :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> 'a globals_ram_scheme" where
  "pop_tags r s =
    (let p = the_ptr (pointer r);
         stack = tags s ! p;
         stack' = pop_tags_stack (tag r) stack in
    s\<lparr> tags := (tags s)[p := stack'] \<rparr>)"

fun_cases pop_tags_elims: "pop_tags r s = s'"

lemma pop_tags_wf_tags:
  assumes
    "pop_tags r s = s'"
    "the_ptr (pointer r) < length (tags s)"
    "(tags s') ! the_ptr (pointer r) \<noteq> []"
    "wf_tags (tags s)"
  shows "wf_tags (tags s')"
  using assms(1) apply (rule pop_tags_elims, simp add: Let_def)
  apply (rule wf_tags_update)
  using assms(4) apply simp
  using assms dropWhile_stack_reborrow wf_tags_spec by simp

lemma hd_pop_tags:
  assumes
    "pop_tags r s = s'"
    "the_ptr (pointer r) < length (tags s)"
    "tag r \<in> collect_tags_stack ((tags s) ! the_ptr (pointer r))"
  shows "tag r \<in> snd (hd ((tags s') ! the_ptr (pointer r)))"
  using assms(1) apply (rule pop_tags_elims)
  using assms hd_dropWhile_stack Let_def  by (auto simp add: Let_def)

lemma pop_tags_memory[intro]:
  "pop_tags r s = s' \<Longrightarrow> memory s' = memory s"
  apply (erule pop_tags.elims)
  by (simp add: Let_def)

lemma pop_tags_tags_length:
  assumes "pop_tags r s = s'"
  shows "length (tags s) = length (tags s')"
using assms proof (rule pop_tags_elims, auto simp add: Let_def)
qed

lemma pop_tags_result:
  assumes
    "pop_tags r s = s'"
    "the_ptr (pointer r) < length (tags s)"
    "p < length (tags s)"
  shows "\<exists>start. (tags s) ! p =
    (if p = the_ptr (pointer r) then
      start @ (tags s') ! p
    else
       (tags s') ! p)"
proof -
  have "p \<noteq> the_ptr (pointer r) \<Longrightarrow> (tags s) ! p = (tags s') ! p"
    using assms(1) apply (rule pop_tags_elims)
    by (auto simp add: Let_def)
  moreover have "p = the_ptr (pointer r) \<Longrightarrow> \<exists>start. (tags s) ! p = start @ (tags s') ! p"
    using assms(1) apply (rule pop_tags_elims)
    apply (auto simp add: Let_def)
    by (metis assms(2) takeWhile_dropWhile_id nth_list_update_eq)
  ultimately show ?thesis by simp
qed

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

fun writable :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> bool" where
  "writable r s =
    (let p = the_ptr (pointer r) in
    let t = tag r in
    p < length (memory s) \<and> writable_stack t (tags s ! p))"

lemma writable_update[simp]: "writable r (memwrite r' v s) = writable r s"
  by simp

lemma pop_tags_writable[intro]: "\<lbrakk>writable r s; wf_heap s\<rbrakk> \<Longrightarrow> writable r (pop_tags r s)"
  apply (auto simp del: BorrowStack.pop_tags.simps)
  by (metis nth_list_update_eq writable_pop_tags)

fun new_pointer :: "'a globals_ram_scheme \<Rightarrow> pointer" where
  "new_pointer s = ptr_val (length (memory s))"

fun heap_new :: "val \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> tagged_ref * 'a globals_ram_scheme" where
  "heap_new v s =
    (let p = new_pointer s;
         t = new_tag s in
    (\<lparr> pointer = p, tag = t \<rparr>,
     s\<lparr> memory := memory s @ [v],
        tags := tags s @ [[(Unique, {t})]],
        issued_tags := t # issued_tags s \<rparr>))"

fun_cases heap_new_elims: "heap_new v s = (r, s')"

lemma heap_new_writable: "\<lbrakk>wf_heap s; heap_new v s = (r', s')\<rbrakk> \<Longrightarrow> writable r' s'"
  apply (erule heap_new_elims)
  by (simp add: Let_def)

lemma heap_new_wf_heap_update: "\<lbrakk>wf_heap s; heap_new v s = (r', s')\<rbrakk> \<Longrightarrow> wf_heap s'"
  apply (erule heap_new_elims)
  by (auto simp add: Let_def wf_tags_snoc BorrowRoot)

fun reborrow :: "ref_kind \<Rightarrow> tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> tagged_ref * 'a globals_ram_scheme" where
  "reborrow k r s =
    (let p = the_ptr (pointer r) in
    let t = new_tag s in
    let tags = (tags s)[p := reborrow_ind k t (tag r) ((tags s) ! p)] in
    (\<lparr> pointer = pointer r, tag = t \<rparr>,  s\<lparr> tags := tags, issued_tags := t # issued_tags s \<rparr>))"

fun_cases reborrow_elims: "reborrow k r s = (r', s')"

(*
lemma collect_tags_stack_reborrow_subset:
  assumes
    "pop_tags_stack parent stack = popped"
    "reborrow_stack k child popped = stack'"
  shows "collect_tags_stack stack' \<subseteq> {child} \<union> collect_tags_stack stack"
proof -
  have "collect_tags_stack stack' \<subseteq> {child} \<union> collect_tags_stack popped"
    using collect_tags_reborrow_subset assms by simp
  moreover have "collect_tags_stack popped \<subseteq> collect_tags_stack stack"
    using notin_pop_tags assms by simp
  ultimately show ?thesis by auto
qed

lemma collect_tags_reborrow_subset:
  "\<lbrakk>the_ptr (pointer r) < length (tags s); reborrow k r s = (r', s')\<rbrakk> \<Longrightarrow> collect_tags (tags s') \<subseteq> {new_tag s} \<union> collect_tags (tags s)"
  apply (erule reborrow_elims)
  apply (simp add: Let_def del: reborrow_comp.simps)
  using collect_tags_update_subset reborrow_comp_subset collect_tags_spec' nth_mem by blas

lemma collect_tags_reborrow_subset':
  "\<lbrakk>the_ptr (pointer r) < length (tags s)\<rbrakk> 
  \<Longrightarrow> collect_tags (tags (snd (reborrow k r s))) \<subseteq> {new_tag s} \<union> collect_tags (tags s)"
  apply (simp add: Let_def del: reborrow_comp.simps)
  using collect_tags_update_subset reborrow_comp_subset collect_tags_spec' nth_mem by blas
*)

lemma reborrow_pointer: "reborrow k r s = (r', s') \<Longrightarrow> pointer r' = pointer r"
  apply (erule reborrow_elims)
  by (auto simp add: Let_def)

(*
lemma new_tag_collect:
  assumes
    "p < length ts"
    "x \<in> collect_tags (ts[p := reborrow_comp_stack k t' t (ts ! p)])"
      (is "x \<in> collect_tags (ts[p := ?stack])")
    "collect_tags ts \<subseteq> issued"
    "x \<notin> issued"
  shows "x = t'"
proof -
  have "x \<in> collect_tags_stack ?stack \<union> collect_tags ts"
    using assms collect_tags_update by blast
  then have "x \<in> {t'} \<union> collect_tags_stack (ts ! p) \<union> collect_tags ts"
    using reborrow_comp_subset by blast
  moreover have "collect_tags_stack (ts ! p) \<subseteq> collect_tags ts"
    using assms collect_tags_spec' nth_mem by blast
  ultimately have "x \<in> {t'} \<union> collect_tags ts" by auto
  then show ?thesis using assms by auto
qed
*)

lemma new_tag_collect:
  assumes
    "p < length ts"
    "x \<in> collect_tags (ts[p := THE stack'. reborrow' k deriv orig (ts ! p) stack'])"
      (is "x \<in> collect_tags (ts[p := ?stack'])")
    "collect_tags ts \<subseteq> issued"
    "x \<notin> issued"
    "\<exists>stack'. reborrow' k deriv orig (ts ! p) stack'"
  shows "x = deriv"
proof -
  have *: "x \<notin> collect_tags_stack (ts ! p)" using assms collect_tags_spec' nth_mem by blast
  have "x \<in> collect_tags_stack ?stack' \<union> collect_tags ts"
    using collect_tags_update_subset assms by blast
  then have "x \<in> collect_tags_stack ?stack'"
    using assms by auto
  then have "x \<in> {deriv} \<union> collect_tags_stack (ts ! p)" using reborrow'_subset assms
    by (metis insert_subset mk_disjoint_insert reborrow_unique the_equality)
  then show ?thesis using * by auto
qed

lemma ex_reborrow'_writable:
  assumes
    "wf_heap s"
    "writable r s"
    "the_ptr (pointer r) < length (tags s)"
  shows "\<exists>!stack'. reborrow' k deriv (tag r) ((tags s) ! (the_ptr (pointer r))) stack'"
  using BorrowStack.ex1_reborrow'_writable wf_tags_spec assms by auto

lemma reborrow_update_heap':
  assumes
    "wf_heap s"
    "writable r s"
    "the_ptr (pointer r) < length (tags s)"
  shows "wf_heap (snd (reborrow k r s))"
  using assms apply (auto simp add: Let_def)
   apply (rule wf_tags_update)
    apply assumption
   apply (rule wf_reborrow_reborrow')
     apply (rule theI')
     apply (auto simp add: ex_reborrow'_writable)
  using wf_tags_spec apply auto[1]
  using new_tag_notin_at apply fastforce
  apply (rule new_tag_collect, auto)
  using ex_reborrow'_writable assms by blast

lemma reborrow_update_heap:
  "\<lbrakk>wf_heap s; writable r s; the_ptr (pointer r) < length (tags s); reborrow k r s = (r', s')\<rbrakk> \<Longrightarrow> wf_heap s'"
  using reborrow_update_heap' by (metis snd_conv)

lemma reborrow_writable: "\<lbrakk>wf_heap s; writable r s; reborrow k r s = (r', s')\<rbrakk> \<Longrightarrow> writable r s'"
  apply (erule reborrow_elims)
  apply (simp add: Let_def)
  apply (rule writable_reborrow)
     apply (rule theI')
     apply (simp add: Rustv.ex_reborrow'_writable)
  using wf_tags_spec nth_mem apply blast
  using new_tag_notin_at by auto

lemma reborrow_writable_derived:
  assumes
    "wf_heap s"
    "writable r s"
    "reborrow k r s = (r', s')"
    "k = Unique \<or> k = SharedReadWrite"
    "the_ptr (pointer r) < length (tags s)"
  shows "writable r' s'"
  using assms(3) apply (rule reborrow_elims)
  using assms apply (simp add: Let_def)
  apply (rule writable_reborrow_derived)
     apply (rule theI')
     apply (simp add: Rustv.ex_reborrow'_writable)
  using wf_tags_spec by auto

lemma lemma_for_write_ex1:
  assumes
    "the_ptr (pointer p) < length ts"
    "\<exists>x \<in> set (ts ! the_ptr (pointer p)). t \<in> snd x"
  shows "t \<in> collect_tags ts"
  using assms collect_tags_spec nth_mem by auto

lemma lemma_for_write_ex:
  assumes
    "the_ptr (pointer p) < length ts"
    "collect_tags ts \<subseteq> set issued"
  shows "\<forall>x \<in> set (ts ! the_ptr (pointer p)). tag_val (Suc (max_list (map the_tag issued))) \<notin> snd x"
  using assms lemma_for_write_ex1
  by (metis Suc_n_not_le_n in_set_conv_nth length_map max_list_ge nth_map subsetD the_tag.simps)

end
