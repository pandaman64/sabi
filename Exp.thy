theory Exp
  imports Definitions
begin

section \<open>Semantics of Expressions\<close>

text \<open>This section presents the big-step semantics of expressions.\<close>

inductive exp_sem :: 
  "gamma * heap * exp \<Rightarrow> heap * val \<Rightarrow> bool" (infix "\<Down>" 65)
where
  Const: "(\<Gamma>, H, Const v) \<Down> (H, v)" |
  Var: "the (\<Gamma> x) = v \<Longrightarrow> (\<Gamma>, H, Var x) \<Down> (H, v)" |
  Box: "\<lbrakk>(\<Gamma>, H, e) \<Down> (H', v); p = length H'; t = fresh_tag H'\<rbrakk> 
        \<Longrightarrow> (\<Gamma>, H, Box e) \<Down> (H' @ [(v, [t])], Reference p t)" |
  Reborrow: "\<lbrakk>(\<Gamma>, H, e) \<Down> (H', Reference p t); writable p t H'; (v, ts) = H' ! p; t' = fresh_tag H'\<rbrakk>
             \<Longrightarrow> (\<Gamma>, H, Reborrow e) \<Down> (H'[p := (v, (kill t ts) @ [t'])], Reference p t')" |
  Deref: "\<lbrakk>(\<Gamma>, H, e) \<Down> (H', Reference p t); readable p t H'; (v, ts) = H' ! p\<rbrakk>
          \<Longrightarrow> (\<Gamma>, H, Deref e) \<Down> (H'[p := (v, kill t ts)], v)" |
  Plus: "\<lbrakk>(\<Gamma>, H, e1) \<Down> (H', VInt i1); (\<Gamma>, H', e2) \<Down> (H'', VInt i2)\<rbrakk>
         \<Longrightarrow> (\<Gamma>, H, Plus e1 e2) \<Down> (H'', VInt (i1 + i2))" |
  Less: "\<lbrakk>(\<Gamma>, H, e1) \<Down> (H', VInt i1); (\<Gamma>, H', e2) \<Down> (H'', VInt i2)\<rbrakk>
         \<Longrightarrow> (\<Gamma>, H, Less e1 e2) \<Down> (H'', VBool (i1 < i2))" |
  Not: "(\<Gamma>, H, e) \<Down> (H', VBool b) \<Longrightarrow> (\<Gamma>, H, Not e) \<Down> (H', VBool (\<not>b))" |
  And: "\<lbrakk>(\<Gamma>, H, e1) \<Down> (H', VBool b1); (\<Gamma>, H', e2) \<Down> (H'', VBool b2)\<rbrakk>
         \<Longrightarrow> (\<Gamma>, H, And e1 e2) \<Down> (H'', VBool (b1 \<and> b2))"

text \<open>
We present the intuition behind the selected rules.
First, {\sc{Box}} rule allocates a new slot at the end of heap,
returning a reference pointing to the slot with a fresh tag.

\begin{framed}
\centering
@{thm[mode=Rule] Box} \sc{Box}
\end{framed}

Next, {\sc{Deref}} rule allows us to access the content the given reference is pointing to.
The validity of the reference is checked by @{const_typ readable}.
Moreover, {\sc{Deref}} invalidates all descendant references to establish the uniqueness
($kill\ t\ ts$).

\begin{framed}
\centering
@{thm[mode=Rule] Deref} \sc{Deref}
\end{framed}

Last but not least, {\sc{Reborrow}} rule creates a new reference with a fresh tag reborrowing the given reference.
The newly created reference is writable. Thus the original reference must be valid for writes.
Reborrow is considered as the use of the original reference and hence it invalidates former children
of the reference. As a result, the reborrow tree will have the original reference and the reborrowing
reference as the last two element.

\begin{framed}
\sc{Reborrow} rule:
\centering
@{thm[mode=Rule] Reborrow}
\end{framed}
\<close>

(* proof automation *)
(*<*)
lemmas exp_sem_cases = exp_sem.cases[split_format(complete)] \<^marker>\<open>tag invisible\<close>
lemmas exp_sem_induct = exp_sem.induct[split_format(complete)] \<^marker>\<open>tag invisible\<close>
declare exp_sem.intros[simp, intro] \<^marker>\<open>tag invisible\<close>

inductive_cases ConstE[elim!]: "(\<Gamma>, H, Const v) \<Down> v'" \<^marker>\<open>tag invisible\<close>
inductive_cases VarE[elim!]: "(\<Gamma>, H, Var x) \<Down> v" \<^marker>\<open>tag invisible\<close>
inductive_cases BoxE[elim!]: "(\<Gamma>, H, Box e) \<Down> v" \<^marker>\<open>tag invisible\<close>
inductive_cases ReborrowE[elim!]: "(\<Gamma>, H, Reborrow e) \<Down> v" \<^marker>\<open>tag invisible\<close>
inductive_cases DerefE[elim!]: "(\<Gamma>, H, Deref e) \<Down> v" \<^marker>\<open>tag invisible\<close>
inductive_cases AlithE[elim!]: \<^marker>\<open>tag invisible\<close>
  "(\<Gamma>, H, Plus e1 e2) \<Down> v"
  "(\<Gamma>, H, Less e1 e2) \<Down> v"
  "(\<Gamma>, H, Not e) \<Down> v"
  "(\<Gamma>, H, And e1 e2) \<Down> v"

(*>*)

lemma reborrow_det_lemma: \<^marker>\<open>tag invisible\<close>
  assumes
    reborrow: "(\<Gamma>, H, Reborrow e) \<Down> E''" and
    memory: "(v, ts) = H' ! p" and
    readable: "readable p t H'" and
    fresh_tag: "t' = fresh_tag H'" and
    IH: "\<And>E'. (\<Gamma>, H, e) \<Down> E' \<Longrightarrow> E' = (H', Reference p t)"
  shows "E'' = (H'[p := (v, kill t ts @ [t'])], Reference p t')"
proof (rule ReborrowE[where \<Gamma> = \<Gamma> and H = H and v = E'' and e = e]) \<^marker>\<open>tag invisible\<close>
  show "(\<Gamma>, H, Reborrow e) \<Down> E''" using reborrow by auto
next
  fix H'a pa ta va tsa
  let ?fix_type = "fresh_tag H'a" (* without this line, the following let fails *)
  let ?t'a = "Suc (fold max (fold (\<lambda>e ts. ts @ snd e) H'a []) 0)"
  assume
    e'': "E'' = (H'a[pa := (va, kill ta tsa @ [?t'a])], Reference pa ?t'a)" and
    loc: "(\<Gamma>, H, e) \<Down>  (H'a, Reference pa ta)" and
    memorya: "(va, tsa) = H'a ! pa" and
    allocateda: "pa < length H'a" and
    valida: "ta \<in> set (snd (H'a ! pa))"
  moreover have "H'a = H'" "pa = p" "ta = t" using loc IH by auto
  moreover have "(va, tsa) = (v, ts)" using calculation memory memorya by auto
  moreover have "va = v" using calculation(9) by auto
  moreover have "tsa = ts" using calculation(9) by auto
  moreover have "?t'a = t'" using calculation(6) fresh_tag by auto
  ultimately show "E'' = (H'[p := (v, kill t ts @ [t'])], Reference p t')" by auto
qed

text \<open>We can prove that the semantics of expressions is deterministic.\<close>

lemma exp_sem_deterministic: "E \<Down> E' \<Longrightarrow> E \<Down> E'' \<Longrightarrow> E'' = E'"
proof (induction E E' arbitrary: E'' rule: exp_sem.induct)
  case (Reborrow \<Gamma> H e H' p t v ts t')
  show ?case
    using Reborrow.IH Reborrow.hyps(2) Reborrow.hyps(3) Reborrow.hyps(4)
          Reborrow.prems readable_def reborrow_det_lemma by auto
next
  case (Deref \<Gamma> H e H' p t v ts)
  then show ?case
    by (smt DerefE Pair_inject val.inject(3))
qed auto

text \<open>The following lemmas are a sanity check of the semantics.
We must be able to write through the references retrieved by {\sc{Box}} and {\sc{Reborrow}}\<close>

lemma box__writable: "(\<Gamma>, H, Box e) \<Down> (H', Reference p t) \<Longrightarrow> writable p t H'"
  by auto

lemma reborrow__writable: "(\<Gamma>, H, Reborrow e) \<Down> (H', Reference p t) \<Longrightarrow> writable p t H'"
  by auto

code_pred [show_modes] exp_sem .

end