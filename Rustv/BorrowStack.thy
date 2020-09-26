theory BorrowStack
  imports Defs
begin

fun collect_tags :: "(ref_kind * tag set) stack \<Rightarrow> tag set" where
  "collect_tags stack = \<Union>(set (map snd stack))"
lemma collect_tags_spec:
  "t \<in> collect_tags stack \<longleftrightarrow> (\<exists>entry \<in> set stack. t \<in> snd entry)"
proof (induction stack)
qed auto

inductive wf_reborrow :: "(ref_kind * tag set) stack \<Rightarrow> bool" where
  (* An allocation root is a Unique reference (Box) *)
  BorrowRoot: "wf_reborrow [(Unique, {t})]" |

  (* Reborrowing from a Unique reference *)
  ReborrowUniqueUnique:
    "\<lbrakk>wf_reborrow ((Unique, {t}) # tail); t' \<notin> insert t (collect_tags tail)\<rbrakk>
 \<Longrightarrow> wf_reborrow ((Unique, {t'}) # (Unique, {t}) # tail)" |
  ReborrowUniqueSRW:
    "\<lbrakk>wf_reborrow ((Unique, {t}) # tail); t' \<notin> insert t (collect_tags tail)\<rbrakk>
 \<Longrightarrow> wf_reborrow ((SharedReadWrite, {t'}) # (Unique, {t}) # tail)" |
  ReborrowUniqueSRO:
    "\<lbrakk>wf_reborrow ((Unique, {t}) # tail); t' \<notin> insert t (collect_tags tail)\<rbrakk>
 \<Longrightarrow> wf_reborrow ((SharedReadOnly, {t'}) # (Unique, {t}) # tail)" |

  (* Reborrowing from a SharedReadWrite *)
  ReborrowSRWUnique:
    "\<lbrakk>wf_reborrow ((SharedReadWrite, ts) # tail); t' \<notin> ts \<union> collect_tags tail\<rbrakk>
 \<Longrightarrow> wf_reborrow ((Unique, {t'}) # (SharedReadWrite, ts) # tail)" |
  ReborrowSRWSRW:
    "\<lbrakk>wf_reborrow ((SharedReadWrite, ts) # tail); t \<notin> ts \<union> collect_tags tail\<rbrakk>
 \<Longrightarrow> wf_reborrow ((SharedReadWrite, insert t ts) # tail)" |
  ReborrowSRWSRO:
    "\<lbrakk>wf_reborrow ((SharedReadWrite, ts) # tail); t' \<notin> ts \<union> collect_tags tail\<rbrakk>
 \<Longrightarrow> wf_reborrow ((SharedReadOnly, {t'}) # (SharedReadWrite, ts) # tail)" |

  (* Reborrowing from a SharedReadOnly gives only a shared reference *)
  ReborrowSROSRO:
    "\<lbrakk>wf_reborrow ((SharedReadOnly, ts) # tail); t \<notin> ts \<union> collect_tags tail\<rbrakk>
 \<Longrightarrow> wf_reborrow ((SharedReadOnly, insert t ts) # tail)"

inductive_cases wf_reborrow_elims: "wf_reborrow stack"

inductive_cases wf_reborrow_structure_elims:
  "wf_reborrow []"
  "wf_reborrow ((Unique, ts) # (Unique, ts') # tail)"
  "wf_reborrow ((SharedReadWrite, ts) # (Unique, ts') # tail)"

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

lemma wf_reborrow_comp:
  assumes
    "wf_reborrow stack"
    "stack = st1 # st2 # rest"
  shows "wf_reborrow (st2 # rest)"
using assms proof (induction arbitrary: st1 rule: wf_reborrow.induct)
qed auto

lemma wf_reborrow_comp':
  fixes top rest
  assumes
    "wf_reborrow (top # rest)"
    "rest \<noteq> []"
  shows "wf_reborrow rest"
using assms proof (induction "(top # rest)" arbitrary: top rule: wf_reborrow.induct)
qed auto

(* convenient intro rules *)
lemma BorrowRoot'[intro]:
  assumes
    "k = Unique"
    "is_singleton ts"
    "tail = []"
  shows "wf_reborrow ((k, ts) # tail)"
  using BorrowRoot assms is_singletonE by auto

lemma ReborrowUniqueUnique'[intro]:
  assumes
    "k = Unique"
    "is_singleton ts"
    "ts \<inter> collect_tags tail = {}"
    "wf_reborrow tail"
    "\<exists>t' tail'. tail = ((Unique, {t'}) # tail')"
  shows "wf_reborrow ((k, ts) # tail)"
proof -
  obtain t t' tail' where
    "ts = {t}"
    "tail = (Unique, {t'}) # tail'"
    using assms is_singletonE by metis
  moreover have "wf_reborrow ((Unique, {t}) # (Unique, {t'}) # tail')"
    using ReborrowUniqueUnique assms calculation by auto
  ultimately show ?thesis using assms by auto
qed

lemma ReborrowSRWUnique'[intro]:
  assumes
    "k = Unique"
    "is_singleton ts"
    "ts \<inter> collect_tags tail = {}"
    "wf_reborrow tail"
    "\<exists>ts' tail'. tail = ((SharedReadWrite, ts') # tail')"
  shows "wf_reborrow ((k, ts) # tail)"
proof -
  obtain t ts' tail' where
    "ts = {t}"
    "tail = (SharedReadWrite, ts') # tail'"
    using assms is_singletonE by metis
  moreover have "wf_reborrow ((Unique, {t}) # (SharedReadWrite, ts') # tail')"
    using ReborrowSRWUnique assms calculation by auto
  ultimately show ?thesis using assms by auto
qed

lemma ReborrowUniqueSRW'[intro]:
  assumes
    "k = SharedReadWrite"
    "ts \<inter> collect_tags tail = {}"
    "wf_reborrow tail"
    "\<exists>t' tail'. tail = ((Unique, {t'}) # tail')"
    "finite ts"
    "ts \<noteq> {}"
  shows "wf_reborrow ((k, ts) # tail)"
using assms(5) assms(6) assms proof (induction rule: finite_ne_induct)
  case (singleton t)
  then show ?case using ReborrowUniqueSRW by auto
next
  case (insert t ts)
  then show ?case using ReborrowSRWSRW by simp
qed

lemma ReborrowUniqueSRO'[intro]:
  assumes
    "k = SharedReadOnly"
    "ts \<inter> collect_tags tail = {}"
    "wf_reborrow tail"
    "\<exists>t' tail'. tail = ((Unique, {t'}) # tail')"
    "finite ts"
    "ts \<noteq> {}"
  shows "wf_reborrow ((k, ts) # tail)"
using assms(5) assms(6) assms proof (induction rule: finite_ne_induct)
  case (singleton t)
  then show ?case using ReborrowUniqueSRO by auto
next
  case (insert t ts)
  then show ?case using ReborrowSROSRO by simp
qed

lemma ReborrowSRWSRO'[intro]:
  assumes
    "k = SharedReadOnly"
    "ts \<inter> collect_tags tail = {}"
    "wf_reborrow tail"
    "\<exists>ts' tail'. tail = ((SharedReadWrite, ts') # tail')"
    "finite ts"
    "ts \<noteq> {}"
  shows "wf_reborrow ((k, ts) # tail)"
using assms(5) assms(6) assms proof (induction rule: finite_ne_induct)
  case (singleton t)
  then show ?case using ReborrowSRWSRO by auto
next
  case (insert t ts)
  then show ?case using ReborrowSROSRO by simp
qed

(* convenient elimination rules on structure of well formed borrow stack *)
lemma wf_reborrow_elims'[
  consumes 1,
  case_names Root UniqueUnique UniqueSRW UniqueSRO SRWUnique SRWSRO
  ]:
  fixes stack
  fixes P
  assumes
    "wf_reborrow stack"
    "\<And>t. stack = [(Unique, {t})] \<Longrightarrow> P"
    "\<And>t t' tail.
      \<lbrakk>stack = (Unique, {t'}) # (Unique, {t}) # tail;
      {t'} \<inter> ({t} \<union> collect_tags tail) = {};
      wf_reborrow ((Unique, {t}) # tail)\<rbrakk> \<Longrightarrow> P"
    "\<And>t ts' tail.
      \<lbrakk>stack = (SharedReadWrite, ts') # (Unique, {t}) # tail;
      ts' \<inter> ({t} \<union> collect_tags tail) = {};
      wf_reborrow ((Unique, {t}) # tail)\<rbrakk> \<Longrightarrow> P"
    "\<And>t ts' tail.
      \<lbrakk>stack = (SharedReadOnly, ts') # (Unique, {t}) # tail;
      ts' \<inter> ({t} \<union> collect_tags tail) = {};
      wf_reborrow ((Unique, {t}) # tail)\<rbrakk> \<Longrightarrow> P"
    "\<And>ts t' tail.
      \<lbrakk>stack = (Unique, {t'}) # (SharedReadWrite, ts) # tail;
      {t'} \<inter> (ts \<union> collect_tags tail) = {};
      wf_reborrow ((SharedReadWrite, ts) # tail)\<rbrakk> \<Longrightarrow> P"
    "\<And>ts ts' tail.
      \<lbrakk>stack = (SharedReadOnly, ts') # (SharedReadWrite, ts) # tail;
      ts' \<inter> (ts \<union> collect_tags tail) = {};
      wf_reborrow ((SharedReadWrite, ts) # tail)\<rbrakk> \<Longrightarrow> P"
  shows P
using assms proof (induction)
  case (BorrowRoot t)
  then show ?case by auto
next
  case (ReborrowUniqueUnique t tail t')
  then show ?case by blast
next
  case (ReborrowUniqueSRW t tail t')
  then show ?case by blast
next
  case (ReborrowUniqueSRO t tail t')
  then show ?case by blast
next
  case (ReborrowSRWUnique ts tail t')
  then show ?case by blast
next
  case (ReborrowSRWSRW ts tail t)
  then show ?case by fastforce
next
  case (ReborrowSRWSRO ts tail t')
  then show ?case by simp
next
  case (ReborrowSROSRO ts tail t)
  then show ?case by fastforce
qed

lemma wf_reborrow_induct'[
  consumes 1,
  case_names Root UniqueUnique UniqueSRW UniqueSRO SRWUnique SRWSRO
  ]:
  fixes stack
  fixes P
  assumes
    "wf_reborrow stack"
    "\<And>t. P [(Unique, {t})]"
    "\<And>t t' tail.
      \<lbrakk>P ((Unique, {t}) # tail);
      {t'} \<inter> ({t} \<union> collect_tags tail) = {};
      wf_reborrow ((Unique, {t}) # tail)\<rbrakk>
      \<Longrightarrow> P ((Unique, {t'}) # (Unique, {t}) # tail)"
    "\<And>t ts' tail.
      \<lbrakk>P ((Unique, {t}) # tail);
      ts' \<inter> ({t} \<union> collect_tags tail) = {};
      wf_reborrow ((Unique, {t}) # tail)\<rbrakk>
      \<Longrightarrow> P ((SharedReadWrite, ts') # (Unique, {t}) # tail)"
    "\<And>t ts' tail.
      \<lbrakk>P ((Unique, {t}) # tail);
      ts' \<inter> ({t} \<union> collect_tags tail) = {};
      wf_reborrow ((Unique, {t}) # tail)\<rbrakk>
      \<Longrightarrow> P ((SharedReadOnly, ts') # (Unique, {t}) # tail)"
    "\<And>ts t' tail.
      \<lbrakk>P ((SharedReadWrite, ts) # tail);
      {t'} \<inter> (ts \<union> collect_tags tail) = {};
      wf_reborrow ((SharedReadWrite, ts) # tail)\<rbrakk>
      \<Longrightarrow> P ((Unique, {t'}) # (SharedReadWrite, ts) # tail)"
    "\<And>ts ts' tail.
      \<lbrakk>P ((SharedReadWrite, ts) # tail);
      ts' \<inter> (ts \<union> collect_tags tail) = {};
      wf_reborrow ((SharedReadWrite, ts) # tail)\<rbrakk>
      \<Longrightarrow> P ((SharedReadOnly, ts') # (SharedReadWrite, ts) # tail)"
  shows "P stack"
proof -
  have "stack \<noteq> []"
    using assms(1) wf_reborrow_nonempty by simp
  then show ?thesis
  using assms proof (induction rule: list_nonempty_induct)
    case (single entry)
    then show ?case by (metis last_ConsL wf_reborrow_root)
  next
    case (cons entry stack)
    show ?case
    using cons.prems(1) proof (cases "(entry # stack)" rule: wf_reborrow_elims')
      case (Root t)
      then show ?thesis using assms by simp
    next
      case (UniqueUnique t t' tail)
      then show ?thesis using assms cons by simp
    next
      case (UniqueSRW t ts' tail)
      then show ?thesis using assms cons by simp
    next
      case (UniqueSRO t ts' tail)
      then show ?thesis using assms cons by simp
    next
      case (SRWUnique ts t' tail)
      then show ?thesis using assms cons by simp
    next
      case (SRWSRO ts ts' tail)
      then show ?thesis using assms cons by simp
    qed
  qed
qed

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
  shows "target \<notin> collect_tags (tl stack)"
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
  moreover have "target \<in> collect_tags (tl stack)"
    using assms collect_tags_spec nth_tl wf_reborrow_nonempty
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
    "target \<in> collect_tags stack"
  shows "\<exists>i. (i < length stack \<and> target \<in> snd (stack ! i)) \<and>
  (\<forall>j. j < length stack \<and> target \<in> snd (stack ! j) \<longrightarrow> j = i)"
proof -
  have "\<exists>i < length stack. target \<in> snd (stack ! i)"
    using assms collect_tags_spec by (metis in_set_conv_nth)
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
    "target \<in> collect_tags stack"
  shows "\<exists>!i. i < length stack \<and> target \<in> snd (stack ! i)"
  using wf_reborrow_tag_position_unique' assms by blast

fun stack_finite :: "(ref_kind * tag set) stack \<Rightarrow> bool" where
  "stack_finite [] = True" |
  "stack_finite (s # stack) = (finite (snd s) \<and> stack_finite stack)"

lemma stack_finite_spec: "stack_finite stack \<longleftrightarrow> (\<forall>s \<in> set stack. finite (snd s))"
proof (induction stack)
qed auto

lemma stack_finite_wf_reborrow[intro]:
  assumes "wf_reborrow stack"
  shows "stack_finite stack"
using assms proof (induction rule: wf_reborrow.induct)
qed auto

lemma collect_tags_stack_finite:
  assumes "stack_finite stack"
  shows "finite (collect_tags stack)"
  using assms stack_finite_spec by auto

lemma stack_finite_finite_collect_tags:
  assumes "finite (collect_tags stack)"
  shows "stack_finite stack"
  using assms by (simp add: stack_finite_spec)

fun pop_tags :: "tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> (ref_kind * tag set) stack" where
  "pop_tags t stack = dropWhile (\<lambda>entry. t \<notin> snd entry) stack"

lemma hd_dropWhile_stack:
  assumes
    "pop_tags t stack = stack'"
    "\<exists>entry \<in> set stack. t \<in> snd entry"
  shows "t \<in> snd (hd stack')"
  by (metis assms(1) assms(2) pop_tags.simps dropWhile_eq_Nil_conv hd_dropWhile)

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
    moreover have "wf_reborrow rest" using calculation Cons.prems wf_reborrow_comp' by auto
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

fun writable :: "tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> bool" where
  "writable t [] \<longleftrightarrow> False" |
  "writable t ((k, ts) # stack) \<longleftrightarrow>
    (if t \<in> ts then k = Unique \<or> k = SharedReadWrite else writable t stack)"

lemma writable_in_collect_tags:
  assumes "writable t stack"
  shows "t \<in> collect_tags stack"
using assms proof (induction stack)
  case (Cons entry stack)
  then show ?case using writable.elims(2) by fastforce
qed auto

lemma writable_the_index:
  assumes
    "wf_reborrow stack"
    "writable t stack"
  shows "\<exists>!i. i < length stack \<and> t \<in> snd (stack ! i)"
  using wf_reborrow_tag_position_unique writable_in_collect_tags assms by simp

lemma writable_pop_tags:
  "writable t stack \<Longrightarrow> writable t (pop_tags t stack)"
proof (induction stack)
  case Nil
  then show ?case by simp
next
  case (Cons entry stack)
  then show ?case using writable.elims(2) by fastforce
qed

lemma writable_pop_tags':
  assumes
    "writable t stack"
    "pop_tags t stack = stack'"
  shows "(fst (hd stack') = Unique \<or> fst (hd stack') = SharedReadWrite)
      \<and> t \<in> snd (hd stack')"
    (is "?kind \<and> _")
proof
  show ?kind
    using assms
    by (metis hd_dropWhile list.collapse pop_tags.elims prod.collapse writable.simps(1)
        writable.simps(2) writable_pop_tags)
next
  show "t \<in> snd (hd stack')"
    using hd_dropWhile_stack assms writable_in_collect_tags by simp
qed

inductive reborrow'
  :: "ref_kind \<Rightarrow> tag \<Rightarrow> tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> bool" where
  DerivUniqueUnique:
    "reborrow' Unique deriv orig
      ((Unique, {orig}) # tail)
      ((Unique, {deriv}) # (Unique, {orig}) # tail)" |
  DerivUniqueSRW:
    "reborrow' SharedReadWrite deriv orig
      ((Unique, {orig}) # tail)
      ((SharedReadWrite, {deriv}) # (Unique, {orig}) # tail)" |
  DerivUniqueSRO:
    "reborrow' SharedReadOnly deriv orig
      ((Unique, {orig}) # tail)
      ((SharedReadOnly, {deriv}) # (Unique, {orig}) # tail)" |
  DerivSRWUnique:
    "orig \<in> ts
     \<Longrightarrow> reborrow' Unique deriv orig
      ((SharedReadWrite, ts) # tail)
      ((Unique, {deriv}) # (SharedReadWrite, ts) # tail)" |
  DerivSRWSRW:
    "orig \<in> ts
     \<Longrightarrow> reborrow' SharedReadWrite deriv orig
      ((SharedReadWrite, ts) # tail)
      ((SharedReadWrite, insert deriv ts) # tail)" |
  DerivSRWSRO:
    "orig \<in> ts
     \<Longrightarrow> reborrow' SharedReadOnly deriv orig
      ((SharedReadWrite, ts) # tail)
      ((SharedReadOnly, {deriv}) # (SharedReadWrite, ts) # tail)" |
  DerivSROSRO:
    "orig \<in> ts
     \<Longrightarrow> reborrow' SharedReadOnly deriv orig
      ((SharedReadOnly, ts) # tail)
      ((SharedReadOnly, insert deriv ts) # tail)" |
  DerivPop:
    "\<lbrakk>reborrow' k deriv orig tail stack;
      orig \<notin> snd entry\<rbrakk>
    \<Longrightarrow> reborrow' k deriv orig (entry # tail) stack"

(* computational definition of reborrow *)
fun reborrow :: "ref_kind \<Rightarrow> tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> (ref_kind * tag set) stack"
  where
  (* reborrwing Unique *)
  "reborrow Unique t ((Unique, ts) # stack) = (Unique, {t}) # (Unique, ts) # stack" |
  "reborrow Unique t ((SharedReadWrite, ts) # stack) =
    (Unique, {t}) # (SharedReadWrite, ts) # stack" |
  (* reborrowing SharedReadWrite *)
  "reborrow SharedReadWrite t ((Unique, ts) # stack) =
    (SharedReadWrite, {t}) # (Unique, ts) # stack" |
  "reborrow SharedReadWrite t ((SharedReadWrite, ts) # stack) =
    (SharedReadWrite, insert t ts) # stack" |
  (* reborrwing SharedReadOnly *)
  "reborrow SharedReadOnly t ((Unique, ts) # stack) =
    (SharedReadOnly, {t}) # (Unique, ts) # stack" |
  "reborrow SharedReadOnly t ((SharedReadWrite, ts) # stack) =
    (SharedReadOnly, {t}) # (SharedReadWrite, ts) # stack" |
  "reborrow SharedReadOnly t ((SharedReadOnly, ts) # stack) =
    (SharedReadOnly, insert t ts) # stack" |
  (* other cases are uninteresting as reborrow is not well-formed *)
  "reborrow _ _ [] = []" |
  "reborrow Unique _ ((SharedReadOnly, _) # stack) = []" |
  "reborrow SharedReadWrite _ ((SharedReadOnly, _) # stack) = []"

fun reborrow_comp :: "ref_kind \<Rightarrow> tag \<Rightarrow> tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> (ref_kind * tag set) stack" where
  "reborrow_comp k child parent stack =
    reborrow k child (pop_tags parent stack)"

lemma reborrow_ind[intro]:
  "reborrow' k deriv orig stack stack' \<Longrightarrow> reborrow_comp k deriv orig stack = stack'"
proof (induction rule: reborrow'.induct)
qed simp_all

lemma reborrow_ind_unique:
  assumes
    "reborrow' k deriv orig stack stack'"
    "reborrow' k deriv orig stack stack''"
  shows "stack' = stack''"
  using assms(1) assms(2) reborrow_ind by blast

lemma reborrow_comp_pop:
  assumes "orig \<notin> snd entry"
  shows "reborrow_comp k deriv orig (entry # stack) = reborrow_comp k deriv orig stack"
using assms proof (induction stack, auto)
qed

lemma reborrow_hd:
  assumes
    "reborrow r t stack = stack'"
    "stack' \<noteq> []"
  shows "r = fst (hd stack') \<and> t \<in> snd (hd stack')"
using assms proof (cases rule: reborrow.elims)
qed auto

fun_cases reborrow_elims_Unique[case_names _ UniqueUnique UniqueSRW]:
  "reborrow Unique t stack = (Unique, ts) # stack'"
fun_cases reborrow_elims_SRW[case_names _ SRWUnique SRWSRW]:
  "reborrow SharedReadWrite t stack = (SharedReadWrite, ts) # stack'"
fun_cases reborrow_elims_SRO[case_names _ SROUnique SROSRW SROSRO]:
  "reborrow SharedReadOnly t stack = (SharedReadOnly, ts) # stack'"

lemma wf_reborrow_reborrow_Unique:
  assumes
    "wf_reborrow stack"
    "t \<notin> collect_tags stack"
    "reborrow Unique t stack = stack'"
    "stack' \<noteq> []"
  shows "wf_reborrow stack'"
proof -
  have p: "Unique = fst (hd stack') \<and> t \<in> snd (hd stack')"
    using assms reborrow_hd by simp
  then obtain ts rest where
    q: "stack' = (Unique, ts) # rest"
    using assms by (metis list.collapse prod.collapse)
  then have "wf_reborrow ((Unique, ts) # rest)"
  proof (cases t stack ts rest rule: reborrow_elims_Unique)
    case _
    then show ?case using assms(3) q by blast
  next
    case (UniqueUnique ts' stack)
    then show ?thesis using ReborrowUniqueUnique' assms(1) assms(2) unique_ref_head by simp
  next
    case (UniqueSRW ts' stack)
    then show ?thesis using ReborrowSRWUnique' assms(1) assms(2) by simp
  qed
  then show ?thesis by (simp add: q)
qed

lemma wf_reborrow_reborrow_SRW:
  assumes
    "wf_reborrow stack"
    "t \<notin> collect_tags stack"
    "reborrow SharedReadWrite t stack = stack'"
    "stack' \<noteq> []"
  shows "wf_reborrow stack'"
proof -
  have p: "SharedReadWrite = fst (hd stack') \<and> t \<in> snd (hd stack')"
    using assms reborrow_hd by simp
  then obtain ts rest where
    q: "stack' = (SharedReadWrite, ts) # rest"
    using assms by (metis list.collapse prod.collapse)
  then have "wf_reborrow ((SharedReadWrite, ts) # rest)"
  proof (cases t stack ts rest rule: reborrow_elims_SRW)
    case _
    then show ?case using assms(3) q by blast
  next
    case (SRWUnique ts' stack)
    then show ?thesis using assms(1) assms(2) ReborrowUniqueSRW' unique_ref_head by simp
  next
    case (SRWSRW ts')
    moreover have "wf_reborrow ((SharedReadWrite, insert t ts') # rest)"
    proof (rule ReborrowSRWSRW)
      show "wf_reborrow ((SharedReadWrite, ts') # rest)" using assms SRWSRW by simp
    next
      show "t \<notin> ts' \<union> collect_tags rest" using assms SRWSRW by simp
    qed
    ultimately show ?thesis by simp
  qed
  then show ?thesis by (simp add: q)
qed

lemma wf_reborrow_reborrow_SRO:
  assumes
    "wf_reborrow stack"
    "t \<notin> collect_tags stack"
    "reborrow SharedReadOnly t stack = stack'"
    "stack' \<noteq> []"
  shows "wf_reborrow stack'"
proof -
  have p: "SharedReadOnly = fst (hd stack') \<and> t \<in> snd (hd stack')"
    using assms reborrow_hd by simp
  then obtain ts rest where
    q: "stack' = (SharedReadOnly, ts) # rest"
    using assms by (metis list.collapse prod.collapse)
  then have "wf_reborrow ((SharedReadOnly, ts) # rest)"
  proof (cases t stack ts rest rule: reborrow_elims_SRO)
    case _
    then show ?case using assms(3) q by blast
  next
    case (SROUnique ts' stack)
    then show ?thesis using assms(1) assms(2) ReborrowUniqueSRO' unique_ref_head by simp
  next
    case (SROSRW ts' stack)
    then show ?thesis using assms(1) assms(2) ReborrowSRWSRO' by simp
  next
    case (SROSRO ts')
    moreover have "wf_reborrow ((SharedReadOnly, insert t ts') # rest)"
    proof (rule ReborrowSROSRO)
      show "wf_reborrow ((SharedReadOnly, ts') # rest)"
        using assms(1) calculation(1) by blast
    next
      show "t \<notin> ts' \<union> collect_tags rest" using assms SROSRO by simp
    qed
    ultimately show ?thesis by simp
  qed
  then show ?thesis by (simp add: q)
qed

lemma wf_reborrow_reborrow:
  assumes
    "wf_reborrow stack"
    "t \<notin> collect_tags stack"
    "reborrow k t stack = stack'"
    "stack' \<noteq> []"
  shows "wf_reborrow stack'"
proof (cases k)
  case Unique
  then show ?thesis using assms wf_reborrow_reborrow_Unique by simp
next
  case SharedReadWrite
  then show ?thesis using assms wf_reborrow_reborrow_SRW by simp
next
  case SharedReadOnly
  then show ?thesis using assms wf_reborrow_reborrow_SRO by simp
qed

lemma collect_tags_reborrow_subset:
  assumes "reborrow k t stack = stack'"
  shows "collect_tags stack' \<subseteq> {t} \<union> collect_tags stack"
using assms proof(cases rule: reborrow.elims)
qed auto

lemma stack_finite_reborrow:
  assumes
    "reborrow k t stack = stack'"
    "stack_finite stack"
  shows "stack_finite stack'"
using assms collect_tags_reborrow_subset stack_finite_finite_collect_tags
  by (meson collect_tags_stack_finite finite.emptyI finite.insertI finite_Un finite_subset)

lemma notin_pop_tags:
  assumes "pop_tags t stack = stack'"
  shows "collect_tags stack' \<subseteq> collect_tags stack"
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
    then have "stack' = pop_tags t stack" using Cons.prems by simp
    then show ?thesis using Cons.IH by auto
  qed
qed

lemma wf_reborrow_reborrow_comp:
  assumes
    "wf_reborrow stack"
    "writable old stack"
    "pop_tags old stack = popped"
    "reborrow k new popped = stack'"
    "new \<notin> collect_tags stack"
  shows "wf_reborrow stack'"
proof -
  have p: "wf_reborrow popped"
    using assms
    by (metis dropWhile_stack_reborrow BorrowStack.pop_tags.elims
        writable.simps(1) writable_pop_tags)
  have q: "new \<notin> collect_tags popped"
    using assms notin_pop_tags by fastforce
  have "(fst (hd popped) = Unique \<and> old \<in> snd (hd popped))
      \<or> (fst (hd popped) = SharedReadWrite \<and> old \<in> snd (hd popped))"
    using assms writable_pop_tags' by blast
  then show ?thesis
  proof
    assume "fst (hd popped) = Unique \<and> old \<in> snd (hd popped)"
    then obtain ts rest where
      "popped = (Unique, ts) # rest"
      "old \<in> ts"
      by (metis assms(2) assms(3) list.collapse prod.collapse
          writable.simps(1) writable_pop_tags)
    moreover have "ts = {old}" using calculation assms p unique_ref_head by fastforce
    moreover have "reborrow k new ((Unique, {old}) # rest) = stack'"
      using assms calculation by simp
    then show ?thesis
    proof (rule reborrow.elims, auto)
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
          writable.simps(1) writable_pop_tags)
    moreover have "reborrow k new ((SharedReadWrite, ts) # rest) = stack'"
      using assms calculation by simp
    then show ?thesis
    proof (rule reborrow.elims, auto)
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

lemma reborrow_comp_subset:
  "collect_tags (reborrow_comp k child parent stack) \<subseteq> {child} \<union> collect_tags stack"
proof (induction stack arbitrary: child parent)
  case Nil
  then show ?case by simp
next
  case (Cons entry stack)
  then show ?case
    by (metis collect_tags_reborrow_subset insert_is_Un insert_mono
        notin_pop_tags reborrow_comp.elims subset_trans)
qed

lemma decomp_pop_tags_writable:
  assumes
    "writable t stack"
    "pop_tags t stack = stack'"
    "wf_reborrow stack"
  shows "(\<exists>rest. stack' = (Unique, {t}) # rest)
  \<or> (\<exists>rest ts. stack' = (SharedReadWrite, ts) # rest \<and> t \<in> ts)"
using assms proof (induction stack)
  case Nil
  then show ?case by simp
next
  case (Cons entry stack)
  then show ?case
  proof (cases "t \<in> snd entry")
    case True
    moreover have "stack' = entry # stack" using Cons.prems calculation by simp
    moreover have "fst entry = Unique \<or> fst entry = SharedReadWrite"
      using Cons.prems(1) Cons.prems(2) calculation(2) writable_pop_tags' by fastforce
    moreover have "entry = (Unique, {t}) \<or> (\<exists>ts. entry = (SharedReadWrite, ts) \<and> t \<in> ts)"
      using Cons calculation
      by (metis empty_iff insert_iff prod.collapse unique_ref_head)
    ultimately show ?thesis by simp
  next
    case False
    moreover have "writable t stack" using Cons.prems calculation
      by (metis eq_snd_iff list.inject writable.elims(2))
    moreover have "pop_tags t stack = stack'" using Cons.prems calculation by simp
    moreover have "wf_reborrow stack"
      using Cons.prems wf_reborrow_comp' calculation(2) writable.simps(1) by blast
    ultimately show ?thesis using Cons.IH by simp
  qed
qed

lemma decomp_reborrow_comp_writable:
  assumes
    "writable t stack"
    "reborrow_comp k t' t stack = stack'"
    "wf_reborrow stack"
  shows "
  (\<exists>rest. k = Unique \<and> stack' = (Unique, {t'}) # (Unique, {t}) # rest)
  \<or> (\<exists>rest. k = SharedReadWrite \<and> stack' = (SharedReadWrite, {t'}) # (Unique, {t}) # rest)
  \<or> (\<exists>rest. k = SharedReadOnly \<and> stack' = (SharedReadOnly, {t'}) # (Unique, {t}) # rest)
  \<or> (\<exists>rest ts. k = Unique \<and>  stack' = (Unique, {t'}) # (SharedReadWrite, ts) # rest \<and> t \<in> ts)
  \<or> (\<exists>rest ts. k = SharedReadWrite \<and> stack' = (SharedReadWrite, insert t' ts) # rest \<and> t \<in> ts)
  \<or> (\<exists>rest ts. k = SharedReadOnly \<and> stack' = (SharedReadOnly, {t'}) # (SharedReadWrite, ts) # rest \<and> t \<in> ts)"
proof -
  have *: "reborrow k t' (pop_tags t stack) = stack'" (is "reborrow _ _ ?popped = _")
    using assms by simp
  then have "(\<exists>rest. ?popped = (Unique, {t}) # rest)
  \<or> (\<exists>rest ts. ?popped = (SharedReadWrite, ts) # rest \<and> t \<in> ts)"
    using assms decomp_pop_tags_writable by simp
  then show ?thesis
  proof
    assume "\<exists>rest. ?popped = (Unique, {t}) # rest"
    then show ?thesis
      using assms
      by (metis (full_types) "*" reborrow.simps(1) reborrow.simps(3)
          reborrow.simps(5) ref_kind.exhaust)
  next
    assume "\<exists>rest ts. ?popped = (SharedReadWrite, ts) # rest \<and> t \<in> ts"
    then show ?thesis
      using assms
      by (metis (full_types) * reborrow.simps(2) reborrow.simps(4)
          reborrow.simps(6) ref_kind.exhaust)
  qed
qed

lemma decomp_reborrow_comp_writable_elims'[
  consumes 3,
  case_names UniqueUnique SRWUnique SROUnique UniqueSRW SRWSRW SROSRW
  ]:
  assumes
    "writable t stack"
    "reborrow_comp k t' t stack = stack'"
    "wf_reborrow stack"
    "\<exists>rest. k = Unique \<and> stack' = (Unique, {t'}) # (Unique, {t}) # rest \<Longrightarrow> P"
    "\<exists>rest. k = SharedReadWrite \<and> stack' = (SharedReadWrite, {t'}) # (Unique, {t}) # rest \<Longrightarrow> P"
    "\<exists>rest. k = SharedReadOnly \<and> stack' = (SharedReadOnly, {t'}) # (Unique, {t}) # rest \<Longrightarrow> P"
    "\<exists>rest ts. k = Unique \<and> stack' = (Unique, {t'}) # (SharedReadWrite, ts) # rest \<and> t \<in> ts \<Longrightarrow> P"
    "\<exists>rest ts. k = SharedReadWrite \<and> stack' = (SharedReadWrite, insert t' ts) # rest \<and> t \<in> ts \<Longrightarrow> P"
    "\<exists>rest ts. k = SharedReadOnly \<and> stack' = (SharedReadOnly, {t'}) # (SharedReadWrite, ts) # rest \<and> t \<in> ts \<Longrightarrow> P"
  shows "P"
  using decomp_reborrow_comp_writable assms by blast

lemma decomp_reborrow_comp_writable_elims[
  consumes 3,
  case_names UniqueUnique SRWUnique SROUnique UniqueSRW SRWSRW SROSRW
  ]:
  assumes
    "writable t stack"
    "reborrow_comp k t' t stack = stack'"
    "wf_reborrow stack"
    "\<And>rest. k = Unique \<and> stack' = (Unique, {t'}) # (Unique, {t}) # rest \<Longrightarrow> P"
    "\<And>rest. k = SharedReadWrite \<and> stack' = (SharedReadWrite, {t'}) # (Unique, {t}) # rest \<Longrightarrow> P"
    "\<And>rest. k = SharedReadOnly \<and> stack' = (SharedReadOnly, {t'}) # (Unique, {t}) # rest \<Longrightarrow> P"
    "\<And>rest ts. k = Unique \<and> stack' = (Unique, {t'}) # (SharedReadWrite, ts) # rest \<and> t \<in> ts \<Longrightarrow> P"
    "\<And>rest ts. k = SharedReadWrite \<and> stack' = (SharedReadWrite, insert t' ts) # rest \<and> t \<in> ts \<Longrightarrow> P"
    "\<And>rest ts. k = SharedReadOnly \<and> stack' = (SharedReadOnly, {t'}) # (SharedReadWrite, ts) # rest \<and> t \<in> ts \<Longrightarrow> P"
  shows "P"
using assms proof (cases rule: decomp_reborrow_comp_writable_elims')
qed auto

lemma writable_reborrow_comp:
  assumes
    "writable t stack"
    "reborrow_comp k t' t stack = stack'"
    "wf_reborrow stack"
    "t' \<notin> collect_tags stack"
  shows "writable t stack'"
using assms proof (cases rule: decomp_reborrow_comp_writable_elims)
  case SROUnique
  then show ?thesis using assms writable_in_collect_tags by fastforce
next
  case SROSRW
  then show ?thesis using assms writable_in_collect_tags by fastforce
qed auto

lemma writable_reborrow_comp_derived:
  assumes
    "writable t stack"
    "reborrow_comp k t' t stack = stack'"
    "wf_reborrow stack"
    "k = Unique \<or> k = SharedReadWrite"
  shows "writable t' stack'"
using assms proof (cases rule: decomp_reborrow_comp_writable_elims)
qed auto

end