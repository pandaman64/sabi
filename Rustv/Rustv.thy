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

fun collect_tags_stack :: "(ref_kind * tag set) stack \<Rightarrow> tag set" where
  "collect_tags_stack stack = \<Union>(set (map snd stack))"
lemma collect_tags_stack_spec:
  "t \<in> collect_tags_stack stack \<longleftrightarrow> (\<exists>entry \<in> set stack. t \<in> snd entry)"
proof (induction stack)
qed auto

inductive wf_reborrow :: "(ref_kind * tag set) stack \<Rightarrow> bool" where
  (* An allocation root is a Unique reference (Box) *)
  BorrowRoot: "wf_reborrow [(Unique, {t})]" |

  (* Reborrowing from a Unique reference *)
  ReborrowUniqueUnique:
    "\<lbrakk>wf_reborrow ((Unique, {t}) # tail); t' \<notin> insert t (collect_tags_stack tail)\<rbrakk>
 \<Longrightarrow> wf_reborrow ((Unique, {t'}) # (Unique, {t}) # tail)" |
  ReborrowUniqueSRW:
    "\<lbrakk>wf_reborrow ((Unique, {t}) # tail); t' \<notin> insert t (collect_tags_stack tail)\<rbrakk>
 \<Longrightarrow> wf_reborrow ((SharedReadWrite, {t'}) # (Unique, {t}) # tail)" |
  ReborrowUniqueSRO:
    "\<lbrakk>wf_reborrow ((Unique, {t}) # tail); t' \<notin> insert t (collect_tags_stack tail)\<rbrakk>
 \<Longrightarrow> wf_reborrow ((SharedReadOnly, {t'}) # (Unique, {t}) # tail)" |

  (* Reborrowing from a SharedReadWrite *)
  ReborrowSRWUnique:
    "\<lbrakk>wf_reborrow ((SharedReadWrite, ts) # tail); t' \<notin> ts \<union> collect_tags_stack tail\<rbrakk>
 \<Longrightarrow> wf_reborrow ((Unique, {t'}) # (SharedReadWrite, ts) # tail)" |
  ReborrowSRWSRW:
    "\<lbrakk>wf_reborrow ((SharedReadWrite, ts) # tail); t \<notin> ts \<union> collect_tags_stack tail\<rbrakk>
 \<Longrightarrow> wf_reborrow ((SharedReadWrite, insert t ts) # tail)" |
  ReborrowSRWSRO:
    "\<lbrakk>wf_reborrow ((SharedReadWrite, ts) # tail); t' \<notin> ts \<union> collect_tags_stack tail\<rbrakk>
 \<Longrightarrow> wf_reborrow ((SharedReadOnly, {t'}) # (SharedReadWrite, ts) # tail)" |

  (* Reborrowing from a SharedReadOnly gives only a shared reference *)
  ReborrowSROSRO:
    "\<lbrakk>wf_reborrow ((SharedReadOnly, ts) # tail); t \<notin> ts \<union> collect_tags_stack tail\<rbrakk>
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

lemma shared_read_only_top:
  assumes
    "wf_reborrow stack"
    "\<exists>entry \<in> set stack. fst entry = SharedReadOnly"
  shows "fst (hd stack) = SharedReadOnly \<and> \<not>(\<exists>entry \<in> set (tl stack). fst entry = SharedReadOnly)"
using assms proof (induction stack rule: wf_reborrow.induct)
qed auto

lemma wf_reborrow_top_tag_notin:
  assumes
    "wf_reborrow stack"
    "target \<in> snd (hd stack)"
  shows "target \<notin> collect_tags_stack (tl stack)"
using assms proof (induction stack rule: wf_reborrow.induct)
qed auto

lemma wf_reborrow_tag_position_inj_zero:
  assumes
    "wf_reborrow stack"
    "i < length stack"
    "target \<in> snd (stack ! i)"
    "target \<in> snd (stack ! 0)"
  shows "i = 0"
proof (cases i)
  case 0
  then show ?thesis by simp
next
  case (Suc i')
  have "target \<in> snd (hd stack)" using assms wf_reborrow_nonempty
    by (simp add: hd_conv_nth)
  moreover have "target \<in> collect_tags_stack (tl stack)"
    using assms collect_tags_stack_spec nth_tl wf_reborrow_nonempty
    by (metis Nitpick.size_list_simp(2) Suc Suc_less_SucD nth_mem)
  ultimately show ?thesis using wf_reborrow_top_tag_notin assms(1) by blast
qed

(* repetitive, obvious proof *)
lemma wf_reborrow_tag_position_inj:
  assumes
    "wf_reborrow stack"
    "i < length stack"
    "j < length stack"
    "target \<in> snd (stack ! i)"
    "target \<in> snd (stack ! j)"
  shows "i = j"
using assms proof (induction stack arbitrary: i j rule: wf_reborrow.induct)
  case (BorrowRoot t)
  then show ?case by simp
next
  case (ReborrowUniqueUnique t tail t')
  show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using ReborrowUniqueUnique wf_reborrow.ReborrowUniqueUnique
        wf_reborrow_tag_position_inj_zero by blast
  next
    case (Suc i')
    note Suci = Suc
    then show ?thesis
    proof (cases j)
      case 0
      then show ?thesis
        using ReborrowUniqueUnique wf_reborrow.ReborrowUniqueUnique
          wf_reborrow_tag_position_inj_zero by blast
    next
      case (Suc j')
      then show ?thesis using Suc Suci ReborrowUniqueUnique by auto
    qed
  qed
next
  case (ReborrowUniqueSRW t tail t')
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using ReborrowUniqueSRW wf_reborrow.ReborrowUniqueSRW
        wf_reborrow_tag_position_inj_zero by blast
  next
    case (Suc i')
    note Suci = Suc
    then show ?thesis
    proof (cases j)
      case 0
      then show ?thesis
        using ReborrowUniqueSRW wf_reborrow.ReborrowUniqueSRW
          wf_reborrow_tag_position_inj_zero by blast
    next
      case (Suc j')
      then show ?thesis using Suc Suci ReborrowUniqueSRW by auto
    qed
  qed
next
  case (ReborrowUniqueSRO t tail t')
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using ReborrowUniqueSRO wf_reborrow.ReborrowUniqueSRO
        wf_reborrow_tag_position_inj_zero by blast
  next
    case (Suc i')
    note Suci = Suc
    then show ?thesis
    proof (cases j)
      case 0
      then show ?thesis
      using ReborrowUniqueSRO wf_reborrow.ReborrowUniqueSRO
        wf_reborrow_tag_position_inj_zero by blast
    next
      case (Suc j')
      then show ?thesis using Suc Suci ReborrowUniqueSRO by auto
    qed
  qed
next
  case (ReborrowSRWUnique ts tail t')
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using ReborrowSRWUnique wf_reborrow.ReborrowSRWUnique
        wf_reborrow_tag_position_inj_zero by blast
  next
    case (Suc i')
    note Suci = Suc
    then show ?thesis
    proof (cases j)
      case 0
      then show ?thesis
      using ReborrowSRWUnique wf_reborrow.ReborrowSRWUnique
        wf_reborrow_tag_position_inj_zero by blast
    next
      case (Suc j')
      then show ?thesis using Suc Suci ReborrowSRWUnique by auto
    qed
  qed
next
  case (ReborrowSRWSRW ts tail t)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using ReborrowSRWSRW wf_reborrow.ReborrowSRWSRW
        wf_reborrow_tag_position_inj_zero by blast
  next
    case (Suc i')
    note Suci = Suc
    then show ?thesis
    proof (cases j)
      case 0
      then show ?thesis
      using ReborrowSRWSRW wf_reborrow.ReborrowSRWSRW
        wf_reborrow_tag_position_inj_zero by blast
    next
      case (Suc j')
      then show ?thesis using Suc Suci ReborrowSRWSRW
        by (metis length_Cons nth_Cons_Suc)
    qed
  qed
next
  case (ReborrowSRWSRO ts tail t')
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using ReborrowSRWSRO wf_reborrow.ReborrowSRWSRO
        wf_reborrow_tag_position_inj_zero by blast
  next
    case (Suc i')
    note Suci = Suc
    then show ?thesis
    proof (cases j)
      case 0
      then show ?thesis
      using ReborrowSRWSRO wf_reborrow.ReborrowSRWSRO
        wf_reborrow_tag_position_inj_zero by blast
    next
      case (Suc j')
      then show ?thesis using Suc Suci ReborrowSRWSRO by auto
    qed
  qed
next
  case (ReborrowSROSRO ts tail t)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using ReborrowSROSRO wf_reborrow.ReborrowSROSRO
        wf_reborrow_tag_position_inj_zero by blast
  next
    case (Suc i')
    note Suci = Suc
    then show ?thesis
    proof (cases j)
      case 0
      then show ?thesis
      using ReborrowSROSRO wf_reborrow.ReborrowSROSRO
        wf_reborrow_tag_position_inj_zero by blast
    next
      case (Suc j')
      then show ?thesis using Suc Suci ReborrowSROSRO
        by (metis length_Cons nth_Cons_Suc)
    qed
  qed
qed

lemma wf_reborrow_tag_position_unique':
  assumes
    "wf_reborrow stack"
    "target \<in> collect_tags_stack stack"
  shows "\<exists>i. (i < length stack \<and> target \<in> snd (stack ! i)) \<and>
  (\<forall>j. j < length stack \<and> target \<in> snd (stack ! j) \<longrightarrow> j = i)"
proof -
  have "\<exists>i < length stack. target \<in> snd (stack ! i)"
    using assms collect_tags_stack_spec by (metis in_set_conv_nth)
  then obtain i where
    "i < length stack"
    "target \<in> snd (stack ! i)"
    by auto
  moreover
  note calc = calculation
  have "\<forall>j. j < length stack \<and> target \<in> snd (stack ! j) \<longrightarrow> j = i"
  proof
    fix j
    show "j < length stack \<and> target \<in> snd (stack ! j) \<longrightarrow> j = i"
    proof
      assume "j < length stack \<and> target \<in> snd (stack ! j)"
      then show "j = i" using calc assms wf_reborrow_tag_position_inj by auto
    qed
  qed
  ultimately show "\<exists>i. (i < length stack \<and> target \<in> snd (stack ! i)) \<and>
    (\<forall>j. j < length stack \<and> target \<in> snd (stack ! j) \<longrightarrow> j = i)"
    by blast
qed

lemma wf_reborrow_tag_position_unique:
  assumes
    "wf_reborrow stack"
    "target \<in> collect_tags_stack stack"
  shows "\<exists>!i. i < length stack \<and> target \<in> snd (stack ! i)"
  using wf_reborrow_tag_position_unique' assms by blast

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
    "stack_finite stack"
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

lemma collect_tags_stack_finite:
  assumes "stack_finite stack"
  shows "finite (collect_tags_stack stack)"
  using assms stack_finite_spec by auto

lemma stack_finite_finite_collect_tags_stack:
  assumes "finite (collect_tags_stack stack)"
  shows "stack_finite stack"
  using assms by (simp add: stack_finite_spec)

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

fun pop_tags_stack :: "tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> (ref_kind * tag set) stack" where
  "pop_tags_stack t stack = dropWhile (\<lambda>entry. t \<notin> snd entry) stack"

fun pop_tags :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> 'a globals_ram_scheme" where
  "pop_tags r s =
    (let p = the_ptr (pointer r);
         stack = tags s ! p;
         stack' = pop_tags_stack (tag r) stack in
    s\<lparr> tags := (tags s)[p := stack'] \<rparr>)"

fun_cases pop_tags_elims: "pop_tags r s = s'"

lemma hd_dropWhile_stack:
  assumes
    "pop_tags_stack t stack = stack'"
    "\<exists>entry \<in> set stack. t \<in> snd entry"
  shows "t \<in> snd (hd stack')"
  by (metis assms(1) assms(2) pop_tags_stack.simps dropWhile_eq_Nil_conv hd_dropWhile)

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
    then show ?thesis using Cons.prems by simp
  qed
qed

lemma dropWhile_stack_finite:
  "stack_finite stack \<Longrightarrow> stack_finite (dropWhile P stack)"
proof (induction stack)
  case Nil
  then show ?case by simp
next
  case (Cons st stack)
  then have *: "stack_finite (dropWhile P stack)" by simp
  then show ?case
  proof (cases "P st")
    case True
    then show ?thesis using * by simp
  next
    case False
    then show ?thesis using Cons.prems by simp
  qed
qed

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
  using assms dropWhile_stack_reborrow wf_tags_spec apply simp
  using assms dropWhile_stack_finite wf_tags_spec by simp

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

fun writable_stack :: "tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> bool" where
  "writable_stack t [] \<longleftrightarrow> False" |
  "writable_stack t ((k, ts) # stack) \<longleftrightarrow>
    (if t \<in> ts then k = Unique \<or> k = SharedReadWrite else writable_stack t stack)"

lemma writable_stack_in_collect_tags:
  assumes "writable_stack t stack"
  shows "t \<in> collect_tags_stack stack"
using assms proof (induction stack)
  case (Cons entry stack)
  then show ?case using writable_stack.elims(2) by fastforce
qed auto

lemma writable_stack_the_index:
  assumes
    "wf_reborrow stack"
    "writable_stack t stack"
  shows "\<exists>!i. i < length stack \<and> t \<in> snd (stack ! i)"
  using wf_reborrow_tag_position_unique writable_stack_in_collect_tags assms by simp

lemma writable_stack_pop_tags_stack:
  "writable_stack t stack \<Longrightarrow> writable_stack t (pop_tags_stack t stack)"
proof (induction stack)
  case Nil
  then show ?case by simp
next
  case (Cons entry stack)
  then show ?case using writable_stack.elims(2) by fastforce
qed

lemma writable_stack_pop_tags_stack':
  assumes
    "writable_stack t stack"
    "pop_tags_stack t stack = stack'"
  shows "(fst (hd stack') = Unique \<or> fst (hd stack') = SharedReadWrite)
      \<and> t \<in> snd (hd stack')"
    (is "?kind \<and> _")
proof
  show ?kind
    using assms
    by (metis hd_dropWhile list.collapse pop_tags_stack.elims prod.collapse writable_stack.simps(1)
        writable_stack.simps(2) writable_stack_pop_tags_stack)
next
  show "t \<in> snd (hd stack')"
    using hd_dropWhile_stack assms writable_stack_in_collect_tags by simp
qed

fun writable :: "tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> bool" where
  "writable r s =
    (let p = the_ptr (pointer r) in
    let t = tag r in
    p < length (memory s) \<and> writable_stack t (tags s ! p))"

lemma writable_update[simp]: "writable r (memwrite r' v s) = writable r s"
  by simp

lemma pop_tags_writable[intro]: "\<lbrakk>writable r s; wf_heap s\<rbrakk> \<Longrightarrow> writable r (pop_tags r s)"
  apply (auto simp del: pop_tags_stack.simps)
  by (metis nth_list_update_eq writable_stack_pop_tags_stack)

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

fun reborrow_stack :: "ref_kind \<Rightarrow> tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> (ref_kind * tag set) stack"
  where
  (* reborrwing Unique *)
  "reborrow_stack Unique t ((Unique, ts) # stack) = (Unique, {t}) # (Unique, ts) # stack" |
  "reborrow_stack Unique t ((SharedReadWrite, ts) # stack) =
    (Unique, {t}) # (SharedReadWrite, ts) # stack" |
  (* reborrowing SharedReadWrite *)
  "reborrow_stack SharedReadWrite t ((Unique, ts) # stack) =
    (SharedReadWrite, {t}) # (Unique, ts) # stack" |
  "reborrow_stack SharedReadWrite t ((SharedReadWrite, ts) # stack) =
    (SharedReadWrite, insert t ts) # stack" |
  (* reborrwing SharedReadOnly *)
  "reborrow_stack SharedReadOnly t ((Unique, ts) # stack) =
    (SharedReadOnly, {t}) # (Unique, ts) # stack" |
  "reborrow_stack SharedReadOnly t ((SharedReadWrite, ts) # stack) =
    (SharedReadOnly, {t}) # (SharedReadWrite, ts) # stack" |
  "reborrow_stack SharedReadOnly t ((SharedReadOnly, ts) # stack) =
    (SharedReadOnly, insert t ts) # stack" |
  (* other cases are uninteresting as reborrow is not well-formed *)
  "reborrow_stack _ _ [] = []" |
  "reborrow_stack Unique _ ((SharedReadOnly, _) # stack) = []" |
  "reborrow_stack SharedReadWrite _ ((SharedReadOnly, _) # stack) = []"

lemma reborrow_stack_hd:
  assumes
    "reborrow_stack r t stack = stack'"
    "stack' \<noteq> []"
  shows "r = fst (hd stack') \<and> t \<in> snd (hd stack')"
using assms proof (cases rule: reborrow_stack.elims)
qed auto

fun_cases reborrow_stack_elims_Unique[case_names _ UniqueUnique UniqueSRW]:
  "reborrow_stack Unique t stack = (Unique, ts) # stack'"
fun_cases reborrow_stack_elims_SRW[case_names _ SRWUnique SRWSRW]:
  "reborrow_stack SharedReadWrite t stack = (SharedReadWrite, ts) # stack'"
fun_cases reborrow_stack_elims_SRO[case_names _ SROUnique SROSRW SROSRO]:
  "reborrow_stack SharedReadOnly t stack = (SharedReadOnly, ts) # stack'"

lemma wf_reborrow_reborrow_stack_Unique:
  assumes
    "wf_reborrow stack"
    "t \<notin> collect_tags_stack stack"
    "reborrow_stack Unique t stack = stack'"
    "stack' \<noteq> []"
  shows "wf_reborrow stack'"
proof -
  have p: "Unique = fst (hd stack') \<and> t \<in> snd (hd stack')"
    using assms reborrow_stack_hd by simp
  then obtain ts rest where
    q: "stack' = (Unique, ts) # rest"
    using assms by (metis list.collapse prod.collapse)
  then have "wf_reborrow ((Unique, ts) # rest)"
  proof (cases t stack ts rest rule: reborrow_stack_elims_Unique)
    case _
    then show ?case using assms(3) q by blast
  next
    case (UniqueUnique ts' stack)
    moreover obtain t' where
      "ts' = {t'}"
      using assms(1) calculation(1) unique_ref_head by blast
    moreover have "wf_reborrow ((Unique, {t}) # (Unique, {t'}) # stack)"
    proof (rule ReborrowUniqueUnique)
      show "wf_reborrow ((Unique, {t'}) # stack)"
        using assms(1) calculation(1) calculation(4) by auto
    next
      have "t \<notin> {t'} \<union> collect_tags_stack stack"
        using assms(2) calculation(1) calculation(4) by auto
      then show "t \<notin> insert t' (collect_tags_stack stack)" by simp
    qed
    ultimately show ?thesis by simp
  next
    case (UniqueSRW ts' stack)
    moreover have "wf_reborrow ((Unique, {t}) # (SharedReadWrite, ts') # stack)"
    proof (rule ReborrowSRWUnique)
      show "wf_reborrow ((SharedReadWrite, ts') # stack)"
        using assms(1) calculation(1) by blast
    next
      show "t \<notin> ts' \<union> collect_tags_stack stack"
        using assms(2) calculation(1) by auto
    qed
    ultimately show ?thesis by simp
  qed
  then show ?thesis by (simp add: q)
qed

lemma wf_reborrow_reborrow_stack_SRW:
  assumes
    "wf_reborrow stack"
    "t \<notin> collect_tags_stack stack"
    "reborrow_stack SharedReadWrite t stack = stack'"
    "stack' \<noteq> []"
  shows "wf_reborrow stack'"
proof -
  have p: "SharedReadWrite = fst (hd stack') \<and> t \<in> snd (hd stack')"
    using assms reborrow_stack_hd by simp
  then obtain ts rest where
    q: "stack' = (SharedReadWrite, ts) # rest"
    using assms by (metis list.collapse prod.collapse)
  then have "wf_reborrow ((SharedReadWrite, ts) # rest)"
  proof (cases t stack ts rest rule: reborrow_stack_elims_SRW)
    case _
    then show ?case using assms(3) q by blast
  next
    case (SRWUnique ts' stack)
    moreover obtain t' where
      "ts' = {t'}"
      using assms(1) calculation(1) unique_ref_head by blast
    moreover have "wf_reborrow ((SharedReadWrite, {t}) # (Unique, {t'}) # stack)"
    proof (rule ReborrowUniqueSRW)
      show "wf_reborrow ((Unique, {t'}) # stack)"
        using assms SRWUnique calculation by simp
    next
      have "t \<notin> {t'} \<union> (collect_tags_stack stack)"
        using assms(2) calculation(1) calculation(4) by auto
      then show "t \<notin> insert t' (collect_tags_stack stack)" by auto
    qed
    moreover have "wf_reborrow ((SharedReadWrite, ts) # (Unique, ts') # stack)"
      using calculation by simp
    ultimately show ?thesis by simp
  next
    case (SRWSRW ts')
    moreover have "wf_reborrow ((SharedReadWrite, insert t ts') # rest)"
    proof (rule ReborrowSRWSRW)
      show "wf_reborrow ((SharedReadWrite, ts') # rest)" using assms SRWSRW by simp
    next
      show "t \<notin> ts' \<union> collect_tags_stack rest" using assms SRWSRW by simp
    qed
    ultimately show ?thesis by simp
  qed
  then show ?thesis by (simp add: q)
qed

lemma wf_reborrow_reborrow_stack_SRO:
  assumes
    "wf_reborrow stack"
    "t \<notin> collect_tags_stack stack"
    "reborrow_stack SharedReadOnly t stack = stack'"
    "stack' \<noteq> []"
  shows "wf_reborrow stack'"
proof -
  have p: "SharedReadOnly = fst (hd stack') \<and> t \<in> snd (hd stack')"
    using assms reborrow_stack_hd by simp
  then obtain ts rest where
    q: "stack' = (SharedReadOnly, ts) # rest"
    using assms by (metis list.collapse prod.collapse)
  then have "wf_reborrow ((SharedReadOnly, ts) # rest)"
  proof (cases t stack ts rest rule: reborrow_stack_elims_SRO)
    case _
    then show ?case using assms(3) q by blast
  next
    case (SROUnique ts' stack)
    moreover obtain t' where
      "ts' = {t'}"
      using assms(1) calculation(1) unique_ref_head by blast
    moreover have "wf_reborrow ((SharedReadOnly, {t}) # (Unique, {t'}) # stack)"
    proof (rule ReborrowUniqueSRO)
      show "wf_reborrow ((Unique, {t'}) # stack)"
        using assms calculation by simp
    next
      have "t \<notin> {t'} \<union> collect_tags_stack stack"
        using assms(2) calculation(1) calculation(4) by auto
      then show "t \<notin> insert t' (collect_tags_stack stack)" by simp
    qed
    ultimately show ?thesis by (simp add: q)
  next
    case (SROSRW ts' stack)
    moreover have "wf_reborrow ((SharedReadOnly, {t}) # (SharedReadWrite, ts') # stack)"
    proof (rule ReborrowSRWSRO)
      show "wf_reborrow ((SharedReadWrite, ts') # stack)"
        using assms(1) calculation(1) by auto
    next
      show "t \<notin> ts' \<union> collect_tags_stack stack"
        using assms(2) calculation(1) by fastforce
    qed
    ultimately show ?thesis by (simp add: q)
  next
    case (SROSRO ts')
    moreover have "wf_reborrow ((SharedReadOnly, insert t ts') # rest)"
    proof (rule ReborrowSROSRO)
      show "wf_reborrow ((SharedReadOnly, ts') # rest)"
        using assms(1) calculation(1) by blast
    next
      show "t \<notin> ts' \<union> collect_tags_stack rest" using assms SROSRO by simp
    qed
    ultimately show ?thesis by simp
  qed
  then show ?thesis by (simp add: q)
qed

lemma wf_reborrow_reborrow_stack:
  assumes
    "wf_reborrow stack"
    "t \<notin> collect_tags_stack stack"
    "reborrow_stack k t stack = stack'"
    "stack' \<noteq> []"
  shows "wf_reborrow stack'"
proof (cases k)
  case Unique
  then show ?thesis using assms wf_reborrow_reborrow_stack_Unique by simp
next
  case SharedReadWrite
  then show ?thesis using assms wf_reborrow_reborrow_stack_SRW by simp
next
  case SharedReadOnly
  then show ?thesis using assms wf_reborrow_reborrow_stack_SRO by simp
qed

lemma collect_tags_reborrow_stack_subset:
  assumes "reborrow_stack k t stack = stack'"
  shows "collect_tags_stack stack' \<subseteq> {t} \<union> collect_tags_stack stack"
using assms proof(cases rule: reborrow_stack.elims)
qed auto

lemma stack_finite_reborrow_stack:
  assumes
    "reborrow_stack k t stack = stack'"
    "stack_finite stack"
  shows "stack_finite stack'"
using assms collect_tags_reborrow_stack_subset stack_finite_finite_collect_tags_stack
  by (meson collect_tags_stack_finite finite.emptyI finite.insertI finite_Un finite_subset)

lemma notin_pop_tags_stack:
  assumes "pop_tags_stack t stack = stack'"
  shows "collect_tags_stack stack' \<subseteq> collect_tags_stack stack"
using assms proof (induction stack arbitrary: stack')
  case Nil
  then show ?case by simp
next
  case (Cons entry stack)
  show ?case
  proof (cases "t \<in> snd entry")
    case True
    then have "stack' = entry # stack" using Cons.prems by simp
    then show ?thesis by simp
  next
    case False
    then have "stack' = pop_tags_stack t stack" using Cons.prems by simp
    then show ?thesis using Cons.IH by auto
  qed
qed

lemma wf_reborrow_stack_reborrow:
  assumes
    "wf_reborrow stack"
    "writable_stack old stack"
    "pop_tags_stack old stack = popped"
    "reborrow_stack k new popped = stack'"
    "new \<notin> collect_tags_stack stack"
  shows "wf_reborrow stack'"
proof -
  have p: "wf_reborrow popped"
    using assms
    by (metis dropWhile_stack_reborrow pop_tags_stack.elims
        writable_stack.simps(1) writable_stack_pop_tags_stack)
  have q: "new \<notin> collect_tags_stack popped"
    using assms notin_pop_tags_stack by fastforce
  have "(fst (hd popped) = Unique \<and> old \<in> snd (hd popped))
      \<or> (fst (hd popped) = SharedReadWrite \<and> old \<in> snd (hd popped))"
    using assms writable_stack_pop_tags_stack' by blast
  then show ?thesis
  proof
    assume "fst (hd popped) = Unique \<and> old \<in> snd (hd popped)"
    then obtain ts rest where
      "popped = (Unique, ts) # rest"
      "old \<in> ts"
      by (metis assms(2) assms(3) list.collapse prod.collapse
          writable_stack.simps(1) writable_stack_pop_tags_stack)
    moreover have "ts = {old}" using calculation assms p unique_ref_head by fastforce
    moreover have "reborrow_stack k new ((Unique, {old}) # rest) = stack'"
      using assms calculation by simp
    then show ?thesis
    proof (rule reborrow_stack.elims, auto)
      show "wf_reborrow ((Unique, {new}) # (Unique, {old}) # rest)"
        using assms calculation p q ReborrowUniqueUnique by simp
    next
      show "wf_reborrow ((SharedReadWrite, {new}) # (Unique, {old}) # rest)"
        using assms calculation p q ReborrowUniqueSRW by simp
    next
      show "wf_reborrow ((SharedReadOnly, {new}) # (Unique, {old}) # rest)"
        using assms calculation p q ReborrowUniqueSRO by simp
    qed
  next
    assume "fst (hd popped) = SharedReadWrite \<and> old \<in> snd (hd popped)"
    then obtain ts rest where
      "popped = (SharedReadWrite, ts) # rest"
      "old \<in> ts"
      by (metis assms(2) assms(3) list.collapse prod.collapse
          writable_stack.simps(1) writable_stack_pop_tags_stack)
    moreover have "reborrow_stack k new ((SharedReadWrite, ts) # rest) = stack'"
      using assms calculation by simp
    then show ?thesis
    proof (rule reborrow_stack.elims, auto)
      show "wf_reborrow ((Unique, {new}) # (SharedReadWrite, ts) # rest)"
        using assms calculation p q ReborrowSRWUnique by simp
    next
      show "wf_reborrow ((SharedReadWrite, insert new ts) # rest)"
        using assms calculation p q ReborrowSRWSRW by simp
    next
      show "wf_reborrow ((SharedReadOnly, {new}) # (SharedReadWrite, ts) # rest)"
        using assms calculation p q ReborrowSRWSRO by simp
    qed
  qed
qed

fun reborrow_pop_stack :: "ref_kind \<Rightarrow> tag \<Rightarrow> tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> (ref_kind * tag set) stack" where
  "reborrow_pop_stack k child parent stack =
    reborrow_stack k child (pop_tags_stack parent stack)"

fun reborrow :: "ref_kind \<Rightarrow> tagged_ref \<Rightarrow> 'a globals_ram_scheme \<Rightarrow> tagged_ref * 'a globals_ram_scheme" where
  "reborrow k r s =
    (let p = the_ptr (pointer r) in
    let t = new_tag s in
    let tags = (tags s)[p := reborrow_pop_stack k t (tag r) ((tags s) ! p)] in
    (\<lparr> pointer = pointer r, tag = t \<rparr>,  s\<lparr> tags := tags, issued_tags := t # issued_tags s \<rparr>))"

fun_cases reborrow_elims: "reborrow k r s = (r', s')"

lemma collect_tags_stack_reborrow_subset:
  assumes
    "pop_tags_stack parent stack = popped"
    "reborrow_stack k child popped = stack'"
  shows "collect_tags_stack stack' \<subseteq> {child} \<union> collect_tags_stack stack"
proof -
  have "collect_tags_stack stack' \<subseteq> {child} \<union> collect_tags_stack popped"
    using collect_tags_reborrow_stack_subset assms by simp
  moreover have "collect_tags_stack popped \<subseteq> collect_tags_stack stack"
    using notin_pop_tags_stack assms by simp
  ultimately show ?thesis by auto
qed

lemma writable_reborrow_pop_stack:
  assumes
    "writable_stack t stack"
    "reborrow_pop_stack k t' t stack = stack'"
    "t \<noteq> t'"
  shows "writable_stack t stack'"
  sorry

lemma collect_tags_reborrow_subset:
  "reborrow k r s = (r', s') \<Longrightarrow> collect_tags (tags s') \<subseteq> {new_tag s} \<union> collect_tags (tags s)"
  sorry

lemma reborrow_pointer: "reborrow k r s = (r', s') \<Longrightarrow> pointer r' = pointer r"
  apply (erule reborrow_elims)
  by (auto simp: Let_def)

lemma reborrow_update_heap: "\<lbrakk>wf_heap s; writable r s; reborrow k r s = (r', s')\<rbrakk> \<Longrightarrow> wf_heap s'"
  apply (erule reborrow_elims)
  apply auto
    apply (simp add: Let_def) (* length condition is solved by simp *)
   (* finite condition *)
   apply (simp add: Let_def)
   apply (rule wf_tags_update)
     apply simp
    prefer 2
  using stack_finite_reborrow_stack wf_tags_spec apply (simp add: dropWhile_stack_finite)
   apply (rule wf_reborrow_stack_reborrow, auto)
  using nth_mem wf_tags_spec apply blast
  using new_tag_notin_at apply fastforce
  apply (subgoal_tac "collect_tags (tags s') \<subseteq> {new_tag s} \<union> collect_tags (tags s)")
   apply (simp add: Let_def)
   apply auto[1]
  using collect_tags_reborrow_subset
  by (metis new_tag.simps pop_tags_stack.elims reborrow.simps reborrow_pop_stack.simps)

lemma reborrow_writable: "\<lbrakk>wf_heap s; writable r s; reborrow k r s = (r', s')\<rbrakk> \<Longrightarrow> writable r s'"
  apply (erule reborrow_elims)
  apply (simp add: Let_def)
  apply (rule writable_reborrow_pop_stack)
  sorry

end
