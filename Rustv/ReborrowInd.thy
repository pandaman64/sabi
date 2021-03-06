theory ReborrowInd
  imports BorrowStack
begin

inductive reborrow'
  :: "ref_kind \<Rightarrow> tag \<Rightarrow> tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> bool"
where
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
    "\<lbrakk>reborrow' k deriv orig tail stack; orig \<notin> snd entry\<rbrakk>
    \<Longrightarrow> reborrow' k deriv orig (entry # tail) stack"

lemma reborrow'_nonempty_src:
  "reborrow' k deriv orig stack stack' \<Longrightarrow> stack \<noteq> []"
  using reborrow'.simps by blast

lemma ex_reborrow'_writable:
  assumes
    "wf_reborrow stack"
    "writable orig stack"
  shows "\<exists>stack'. reborrow' k deriv orig stack stack'"
using assms proof (induction rule: wf_reborrow_induct')
  case (Root t)
  then show ?case
    by (metis (full_types) DerivUniqueSRO DerivUniqueSRW DerivUniqueUnique empty_iff insert_iff
        ref_kind.exhaust writable.simps(1) writable.simps(2))
next
  case (UniqueUnique t t' tail)
  then show ?case
    by (metis (full_types) DerivPop DerivUniqueSRO DerivUniqueSRW DerivUniqueUnique
        ref_kind.exhaust singletonD snd_conv writable.simps(2))
next
  case (UniqueSRW t ts' tail)
  then show ?case
    by (metis (full_types) DerivPop DerivSRWSRO DerivSRWSRW DerivSRWUnique
        ref_kind.exhaust snd_eqD writable.simps(2))
next
  case (UniqueSRO t ts' tail)
  then show ?case
    by (metis DerivPop ref_kind.distinct(3) ref_kind.distinct(5) snd_conv writable.simps(2))
next
  case (SRWUnique ts t' tail)
  then show ?case
    by (metis (full_types) DerivPop DerivUniqueSRO DerivUniqueSRW DerivUniqueUnique
        ref_kind.exhaust singletonD snd_eqD writable.simps(2))
next
  case (SRWSRO ts ts' tail)
  then show ?case
    by (metis DerivPop ref_kind.distinct(3) ref_kind.distinct(5) sndI writable.simps(2))
qed

lemma ex_reborrow'_readable:
  assumes
    "wf_reborrow stack"
    "readable orig stack"
    "k = SharedReadOnly"
  shows "\<exists>stack'. reborrow' k deriv orig stack stack'"
using assms proof (induction rule: wf_reborrow_induct')
  case (Root t)
  then show ?case using DerivUniqueSRO by auto
next
  case (UniqueUnique t t' tail)
  then show ?case
  proof (cases "t' = orig")
    case True
    then show ?thesis using UniqueUnique DerivUniqueSRO by auto
  next
    case False
    then show ?thesis
    proof -
      obtain stack' where
        "reborrow' k deriv orig ((Unique, {t}) # tail) stack'"
        using UniqueUnique False by auto
      then show ?thesis using False DerivPop by force
    qed
  qed
next
  case (UniqueSRW t ts' tail)
  then show ?case
  proof (cases "orig \<in> ts'")
    case True
    then show ?thesis using UniqueSRW DerivSRWSRO by blast
  next
    case False
    then show ?thesis
    proof -
      obtain stack' where
        "reborrow' k deriv orig ((Unique, {t}) # tail) stack'"
        using UniqueSRW False by auto
      then show ?thesis using False DerivPop by force
    qed
  qed
next
  case (UniqueSRO t ts' tail)
  then show ?case
  proof (cases "orig \<in> ts'")
    case True
    then show ?thesis using UniqueSRO DerivSROSRO by blast
  next
    case False
    then show ?thesis
    proof -
      obtain stack' where
        "reborrow' k deriv orig ((Unique, {t}) # tail) stack'"
        using UniqueSRO False by auto
      then show ?thesis using False DerivPop by force
    qed
  qed
next
  case (SRWUnique ts t' tail)
  then show ?case
  proof (cases "t' = orig")
    case True
    then show ?thesis using SRWUnique DerivUniqueSRO by auto
  next
    case False
    then show ?thesis
    proof -
      obtain stack' where
        "reborrow' k deriv orig ((SharedReadWrite, ts) # tail) stack'"
        using SRWUnique False by auto
      then show ?thesis using False DerivPop by force
    qed
  qed
next
  case (SRWSRO ts ts' tail)
  then show ?case
  proof (cases "orig \<in> ts'")
    case True
    then show ?thesis using SRWSRO DerivSROSRO by blast
  next
    case False
    then show ?thesis
    proof -
      obtain stack' where
        "reborrow' k deriv orig ((SharedReadWrite, ts) # tail) stack'"
        using SRWSRO False by auto
      then show ?thesis using False DerivPop by force
    qed
  qed
qed

fun reborrow_ind
  :: "ref_kind \<Rightarrow> tag \<Rightarrow> tag \<Rightarrow> (ref_kind * tag set) stack \<Rightarrow> (ref_kind * tag set) stack" where
  "reborrow_ind k deriv orig stack = (THE stack'. reborrow' k deriv orig stack stack')"

lemma reborrow_by_comp[simp, intro]:
  assumes "reborrow' k deriv orig stack stack'"
  shows "reborrow_comp k deriv orig stack = stack'"
using assms proof (induction rule: reborrow'.induct)
qed auto

lemma the_reborrow_by_comp[simp, intro]:
  assumes "reborrow' k deriv orig stack (reborrow_comp k deriv orig stack)"
  shows "(THE stack'. reborrow' k deriv orig stack stack') = reborrow_comp k deriv orig stack"
  using assms reborrow_by_comp by blast

lemma the_reborrow_by_comp'[simp, intro]:
  assumes "reborrow' k deriv orig stack (reborrow_comp k deriv orig stack)"
  shows "The (reborrow' k deriv orig stack) = reborrow_comp k deriv orig stack"
  using assms the_reborrow_by_comp by simp

lemma reborrow_unique:
  assumes
    "reborrow' k deriv orig stack stack'"
    "reborrow' k deriv orig stack stack''"
  shows "stack' = stack''"
  using assms(1) assms(2) reborrow_by_comp by blast

lemma ex1_reborrow'_writable:
  assumes
    "wf_reborrow stack"
    "writable orig stack"
  shows "\<exists>!stack'. reborrow' k deriv orig stack stack'"
proof -
  obtain stack' where
    *: "reborrow' k deriv orig stack stack'"
    using assms ex_reborrow'_writable by blast
  moreover have "\<forall>stack''. reborrow' k deriv orig stack stack'' \<longrightarrow> stack'' = stack'"
    using reborrow_unique * by auto
  ultimately show ?thesis by blast
qed

lemma ex1_reborrow'_readable:
  assumes
    "wf_reborrow stack"
    "readable orig stack"
    "k = SharedReadOnly"
  shows "\<exists>!stack'. reborrow' k deriv orig stack stack'"
proof -
  obtain stack' where
    *: "reborrow' k deriv orig stack stack'"
    using assms ex_reborrow'_readable by blast
  moreover have "\<forall>stack''. reborrow' k deriv orig stack stack'' \<longrightarrow> stack'' = stack'"
    using reborrow_unique * by auto
  ultimately show ?thesis by blast
qed

lemma the_reborrow'_writable:
  assumes
    "wf_reborrow stack"
    "writable orig stack"
  shows "\<exists>!stack'. reborrow' k deriv orig stack stack'"
  using assms ex_reborrow'_writable reborrow_unique by auto

lemma the_reborrow'_readable:
  assumes
    "wf_reborrow stack"
    "readable orig stack"
    "k = SharedReadOnly"
  shows "\<exists>!stack'. reborrow' k deriv orig stack stack'"
  using assms ex_reborrow'_readable reborrow_unique by fastforce

lemma reborrow'_hd:
  assumes "reborrow' k deriv orig stack stack'"
  shows "k = fst (hd stack') \<and> deriv \<in> snd (hd stack')"
using assms proof (induction rule: reborrow'.induct, auto)
qed

lemma wf_reborrow_reborrow':
  assumes
    "reborrow' k deriv orig stack stack'"
    "wf_reborrow stack"
    "deriv \<notin> collect_tags stack"
  shows "wf_reborrow stack'"
using assms proof (induction)
  case (DerivPop k deriv orig tail stack entry)
  then show ?case using reborrow'_nonempty_src wf_reborrow_pop' by auto
qed (auto simp add: ReborrowSRWSRW ReborrowSROSRO)

lemma wf_reborrow_reborrow'_the:
  assumes
    "writable orig stack"
    "wf_reborrow stack"
    "deriv \<notin> collect_tags stack"
  shows "wf_reborrow (THE stack'. reborrow' k deriv orig stack stack')"
  using assms wf_reborrow_reborrow'
  by (metis reborrow_by_comp the_reborrow'_writable the_reborrow_by_comp the_reborrow_by_comp')

lemma stack_finite_reborrow':
  assumes
    "reborrow' k deriv orig stack stack'"
    "stack_finite stack"
  shows "stack_finite stack'"
using assms proof (induction, auto)
qed

lemma reborrow'_subset:
  assumes "reborrow' k deriv orig stack stack'"
  shows "collect_tags stack' \<subseteq> {deriv} \<union> collect_tags stack"
using assms proof (induction, auto)
qed

lemma writable_reborrow:
  assumes
    "reborrow' k deriv orig stack stack'"
    "wf_reborrow stack"
    "writable orig stack"
    "deriv \<notin> collect_tags stack"
  shows "writable orig stack'"
using assms proof (induction)
  case (DerivPop k deriv orig tail stack entry)
  show ?case
  proof (rule DerivPop.IH)
    show "wf_reborrow tail" using DerivPop wf_reborrow_pop' reborrow'_nonempty_src by simp
  next
    show "writable orig tail" using DerivPop writable_tl by fastforce
  next
    show "deriv \<notin> collect_tags tail" using DerivPop.prems by simp
  qed
qed auto

lemma writable_reborrow_the:
  assumes
    "wf_reborrow stack"
    "writable orig stack"
    "deriv \<notin> collect_tags stack"
  shows "writable orig (THE stack'. reborrow' k deriv orig stack stack')"
  using writable_reborrow
  by (metis assms ex_reborrow'_writable reborrow_by_comp the_reborrow_by_comp')

lemma writable_reborrow_derived:
  assumes
    "reborrow' k deriv orig stack stack'"
    "writable orig stack"
    "wf_reborrow stack"
    "k = Unique \<or> k = SharedReadWrite"
  shows "writable deriv stack'"
using assms proof (induction)
  case (DerivPop k deriv orig tail stack entry)
  show ?case
  proof (rule DerivPop.IH)
    show "wf_reborrow tail" using DerivPop wf_reborrow_pop' reborrow'_nonempty_src by simp
  next
    show "writable orig tail" using DerivPop writable_tl by fastforce
  next
    show "k = Unique \<or> k = SharedReadWrite" using DerivPop.prems by simp
  qed
qed auto

lemma writable_reborrow_derived_the:
  assumes
    "writable orig stack"
    "wf_reborrow stack"
    "k = Unique \<or> k = SharedReadWrite"
  shows "writable deriv (THE stack'. reborrow' k deriv orig stack stack')"
  using writable_reborrow_derived
  by (metis assms ex_reborrow'_writable reborrow_by_comp the_reborrow_by_comp')

lemma reborrow_comp_by_ind:
  assumes
    "wf_reborrow stack"
    "reborrow_comp k deriv orig stack = stack'"
    "stack' \<noteq> []"
  shows
    "reborrow' k deriv orig stack stack'"
using assms proof (induction rule: wf_reborrow_induct')
  case (Root t)
  consider "orig \<noteq> t" | "orig = t" by auto
  then show ?case
  proof (cases)
    case 1
    then show ?thesis using Root by simp
  next
    case 2
    then show ?thesis using Root reborrow_by_comp the_reborrow'_writable by fastforce
  qed
next
  case (UniqueUnique t t' tail)
  consider "t' \<noteq> orig" | "t' = orig" by auto
  then show ?case
  proof (cases)
    case 1
    then have "reborrow_comp k deriv orig ((Unique, {t}) # tail) = stack'"
      using UniqueUnique.prems(1) by auto
    then show ?thesis using UniqueUnique \<open>t' \<noteq> orig\<close> reborrow'.intros(8) by auto
  next
    case 2
    then show ?thesis
    proof (cases k)
      case Unique
      then show ?thesis using 2 UniqueUnique DerivUniqueUnique by auto
    next
      case SharedReadWrite
      then show ?thesis using 2 UniqueUnique DerivUniqueSRW by auto
    next
      case SharedReadOnly
      then show ?thesis using 2 UniqueUnique DerivUniqueSRO by auto
    qed
  qed
next
  case (UniqueSRW t ts' tail)
  consider "orig \<notin> ts'" | "orig \<in> ts'" by auto
  then show ?case
  proof (cases)
    case 1
    then have "reborrow_comp k deriv orig ((Unique, {t}) # tail) = stack'"
      using UniqueSRW.prems(1) by auto
    then show ?thesis using UniqueSRW \<open>orig \<notin> ts'\<close> reborrow'.intros(8) by auto
  next
    case 2
    then show ?thesis
    proof (cases k)
      case Unique
      then show ?thesis using 2 UniqueSRW DerivSRWUnique by auto
    next
      case SharedReadWrite
      then show ?thesis using 2 UniqueSRW DerivSRWSRW by auto
    next
      case SharedReadOnly
      then show ?thesis using 2 UniqueSRW DerivSRWSRO by auto
    qed
  qed
next
  case (UniqueSRO t ts' tail)
  consider "orig \<notin> ts'" | "orig \<in> ts'" by auto
  then show ?case
  proof (cases)
    case 1
    then have "reborrow_comp k deriv orig ((Unique, {t}) # tail) = stack'"
      using UniqueSRO.prems(1) by auto
    then show ?thesis using UniqueSRO \<open>orig \<notin> ts'\<close> reborrow'.intros(8) by auto
  next
    case 2
    then show ?thesis
    proof (cases k)
      case Unique
      then show ?thesis using 2 UniqueSRO by auto
    next
      case SharedReadWrite
      then show ?thesis using 2 UniqueSRO by auto
    next
      case SharedReadOnly
      then show ?thesis using 2 UniqueSRO DerivSROSRO by auto
    qed
  qed
next
  case (SRWUnique ts t' tail)
  consider "t' \<noteq> orig" | "t' = orig" by auto
  then show ?case
  proof (cases)
    case 1
    then have "reborrow_comp k deriv orig ((SharedReadWrite, ts) # tail) = stack'"
      using SRWUnique.prems(1) by auto
    then show ?thesis using SRWUnique \<open>t' \<noteq> orig\<close> reborrow'.intros(8) by auto
  next
    case 2
    then show ?thesis
    proof (cases k)
      case Unique
      then show ?thesis using 2 SRWUnique DerivUniqueUnique by auto
    next
      case SharedReadWrite
      then show ?thesis using 2 SRWUnique DerivUniqueSRW by auto
    next
      case SharedReadOnly
      then show ?thesis using 2 SRWUnique DerivUniqueSRO by auto
    qed
  qed
next
  case (SRWSRO ts ts' tail)
  consider "orig \<notin> ts'" | "orig \<in> ts'" by auto
  then show ?case
  proof (cases)
    case 1
    then have "reborrow_comp k deriv orig ((SharedReadWrite, ts) # tail) = stack'"
      using SRWSRO.prems(1) by auto
    then show ?thesis using SRWSRO \<open>orig \<notin> ts'\<close> reborrow'.intros(8) by auto
  next
    case 2
    then show ?thesis
    proof (cases k)
      case Unique
      then show ?thesis using 2 SRWSRO by auto
    next
      case SharedReadWrite
      then show ?thesis using 2 SRWSRO by auto
    next
      case SharedReadOnly
      then show ?thesis using 2 SRWSRO DerivSROSRO by auto
    qed
  qed
qed

lemma reborrow_equivalence:
  assumes
    "wf_reborrow stack"
    "writable orig stack \<or> (readable orig stack \<and> k = SharedReadOnly)"
  shows "reborrow_comp k deriv orig stack = stack' \<longleftrightarrow> reborrow' k deriv orig stack stack'"
  using assms reborrow_by_comp reborrow_comp_by_ind nonempty_reborrow_comp_if_valid_reborrow
  by fast

lemma wf_reborrow_pop''[
  consumes 1,
  case_names Root Reborrow
]:
  assumes
    "wf_reborrow stack"
  obtains
    t where
    "stack = [(Unique, {t})]"
  | entry and tail where
    "stack = entry # tail" and
    "wf_reborrow tail"
  by (metis assms last.simps neq_Nil_conv wf_reborrow_pop'
      wf_reborrow_root wf_reborrow_structure_elims(1))

lemma writable_reborrow_comp_derived':
  assumes
    "writable t stack"
    "reborrow_comp k t' t stack = stack'"
    "wf_reborrow stack"
    "k = Unique \<or> k = SharedReadWrite"
  shows "writable t' stack'"
proof -
  have "reborrow' k t' t stack stack'"
    using assms reborrow_equivalence by simp
  then show ?thesis
  using assms proof (induction)
    case (DerivPop k deriv orig tail stack entry)
    moreover have "writable orig tail"
      using writable_tl DerivPop by fastforce
    moreover have "wf_reborrow tail"
      using reborrow'_nonempty_src wf_reborrow_pop' calculation by blast
    moreover have "reborrow_comp k deriv orig tail = stack"
      using reborrow_equivalence calculation by simp
    ultimately show ?case by simp
  qed auto
qed

end