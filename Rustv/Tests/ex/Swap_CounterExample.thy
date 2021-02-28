theory Swap_CounterExample
  imports Simpl.Semantic Simpl.Vcg "Rust-Verification.Rust_Semantics"
begin

record rustv_swap_env = globals_ram +
  x :: tagged_ref
  y :: tagged_ref
  tmp :: tagged_ref

definition rustv_swap_body :: "(rustv_swap_env, 'p, rust_error) com" where
  "rustv_swap_body ==
    Basic (\<lambda>s. let (r, s') = heap_new uninit s in s'\<lparr> tmp := r \<rparr>);;
    copy_betw_places x tmp;;
    copy_betw_places y x;;
    copy_betw_places tmp y"

definition root where
  "root = tag_val 0"
definition s1 where
  "s1 = tag_val 1"
definition u where
  "u = tag_val 2"
definition s2 where
  "s2 = tag_val 3"
definition borrow_stack where
  "borrow_stack = [(SharedReadWrite, {s2}), (Unique, {u}),
    (SharedReadWrite, {s1}), (Unique, {root})]"

lemma l1: "wf_reborrow borrow_stack"
  unfolding borrow_stack_def
  apply (rule ReborrowUniqueSRW)
   apply (rule ReborrowSRWUnique)
    apply (rule ReborrowUniqueSRW)
     apply (rule BorrowRoot)
  by (simp_all add: root_def s1_def u_def s2_def)

definition the_memory :: rustv_swap_env where
  "the_memory = \<lparr>
    memory = [int_val 100],
    tags = [borrow_stack],
    issued_tags = [root, s1, u, s2],
    x = \<lparr> pointer = ptr_val 0, tag = s1 \<rparr>,
    y = \<lparr> pointer = ptr_val 0, tag = s2 \<rparr>,
    tmp = undefined
  \<rparr>"

lemma l2: "wf_heap the_memory"
  apply (auto simp add: the_memory_def borrow_stack_def)
  using l1 by (simp add: borrow_stack_def)

lemma l3: "(let (r, s') = heap_new uninit the_memory
     in s'\<lparr>tmp := r\<rparr>)
    \<in> {s. Rustv.writable (tmp s) s \<and>
           Rustv.readable (x s) s}"
  unfolding the_memory_def
  by (auto simp add: Let_def borrow_stack_def)

lemma l4: "\<Gamma> \<turnstile>\<langle>rustv_swap_body, Normal the_memory\<rangle> \<Rightarrow> Fault invalid_ref"
  unfolding rustv_swap_body_def
  apply (rule Semantic.exec.Seq)
   apply (rule Semantic.exec.Seq)
    apply (rule Semantic.exec.Seq)
     apply (rule Semantic.exec.Basic)
    apply (rule Semantic.exec.Guard)
     apply (rule l3)
    apply (rule Semantic.exec.Seq)
     apply (rule Semantic.exec.Seq)
      apply (rule Semantic.exec.Basic)
     apply (rule Semantic.exec.Basic)
    apply (rule Semantic.exec.Basic)
   apply (rule Semantic.exec.GuardFault)
   prefer 2
   apply simp
  by (auto simp add: Let_def the_memory_def borrow_stack_def s1_def s2_def u_def root_def)

lemma l6: "writable (x the_memory) the_memory"
  unfolding the_memory_def borrow_stack_def
  by simp

lemma l7: "writable (y the_memory) the_memory"
  unfolding the_memory_def borrow_stack_def
  by simp

theorem "\<exists>s.
  writable (x s) s \<and>
  writable (y s) s \<and>
  \<Gamma> \<turnstile> \<langle>rustv_swap_body, Normal s\<rangle> \<Rightarrow> Fault invalid_ref"
  using l4 l6 l7 by auto

inductive det where
  DetBasic: "det (Basic f)" |
  DetSeq: "\<lbrakk>det c1; det c2\<rbrakk> \<Longrightarrow> det (c1;; c2)" |
  DetGuard: "det c \<Longrightarrow> det (Guard f g c)"

lemma det_det:
  assumes
    "det c"
    "\<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> t"
    "\<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> t'"
  shows "t = t'"
using assms proof (induction arbitrary: s t t')
  case (DetBasic f)
  then show ?case
    by (metis exec_Normal_elim_cases(6) exec_elim_cases(7))
next
  case (DetSeq c1 c2)
  show ?case
  proof (cases s)
    case (Normal x1)
    then show ?thesis
      by (metis DetSeq.IH DetSeq.prems exec_Normal_elim_cases(8))
  next
    case (Abrupt x2)
    then show ?thesis
      by (metis Abrupt_end DetSeq.prems(1) DetSeq.prems(2))
  next
    case (Fault x3)
    then show ?thesis
      by (metis Fault_end DetSeq.prems(1) DetSeq.prems(2))
  next
    case Stuck
    then show ?thesis
      by (metis Stuck_end DetSeq.prems(1) DetSeq.prems(2))
  qed
next
  case (DetGuard c f g)
  thm exec_Normal_elim_cases(5)
  thm exec_elim_cases
  show ?case
  proof (cases s)
    case (Normal x1)
    then show ?thesis
      by (metis DetGuard.IH DetGuard.prems exec_Normal_elim_cases(5))
  next
    case (Abrupt x2)
    then show ?thesis
      by (metis Abrupt_end DetGuard.prems(1) DetGuard.prems(2))
  next
    case (Fault x3)
    then show ?thesis
      by (metis Fault_end DetGuard.prems(1) DetGuard.prems(2))
  next
    case Stuck
    then show ?thesis
      by (metis Stuck_end DetGuard.prems(1) DetGuard.prems(2))
  qed
qed

lemma det_swap: "det rustv_swap_body"
  unfolding rustv_swap_body_def
  by (simp add: DetBasic DetGuard DetSeq)

lemma l5: "\<Gamma> \<turnstile>\<langle>rustv_swap_body, Normal the_memory\<rangle> \<Rightarrow> t \<Longrightarrow> t = Fault invalid_ref"
proof -
  assume "\<Gamma> \<turnstile>\<langle>rustv_swap_body, Normal the_memory\<rangle> \<Rightarrow> t"
  then show "t = Fault invalid_ref"
    using det_det det_swap l4 by blast
qed

theorem "\<exists>s.
  writable (x s) s \<and>
  writable (y s) s \<and>
  (\<forall>t. \<Gamma> \<turnstile> \<langle>rustv_swap_body, Normal s\<rangle> \<Rightarrow> t \<longrightarrow> t = Fault invalid_ref)"
  using l5 l6 l7 by auto

lemma "\<Gamma> \<turnstile>\<^bsub>/{invalid_ref}\<^esub>
  {s. s = the_memory}
  rustv_swap_body
  {s. False}, {s. False}"
  unfolding rustv_swap_body_def
  apply vcg
  apply (auto simp add: Let_def)
  by (auto simp add: the_memory_def borrow_stack_def
      s1_def s2_def u_def root_def)

end