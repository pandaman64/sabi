theory Exp
  imports Definitions
begin

inductive exp_sem :: 
  "gamma * heap * reborrow * exp \<Rightarrow> heap * reborrow * val \<Rightarrow> bool" (infix "\<Down>" 65)
where
  Const: "(\<Gamma>, H, R, Const v) \<Down> (H, R, v)" |
  Var: "the (\<Gamma> x) = v \<Longrightarrow> (\<Gamma>, H, R, Var x) \<Down> (H, R, v)" |
  Box: "\<lbrakk>(\<Gamma>, H, R, e) \<Down> (H', R', v); fresh p H'; fresh_tag t R'\<rbrakk> 
        \<Longrightarrow> (\<Gamma>, H, R, Box e) \<Down> (H'(p \<mapsto> v), R'(p \<mapsto> [t]), Reference p t)" |
  Reborrow: "\<lbrakk>(\<Gamma>, H, R, e) \<Down> (H', R', Reference p t); writable p t R'; fresh_tag t' R'\<rbrakk>
             \<Longrightarrow> (\<Gamma>, H, R, Reborrow e) \<Down> (H', R'(p \<mapsto> kill t (the (R' p)) @ [t']), Reference p t')" |
  Deref: "\<lbrakk>(\<Gamma>, H, R, e) \<Down> (H', R', Reference p t); readable p t R'; v = the (H' p)\<rbrakk>
          \<Longrightarrow> (\<Gamma>, H, R, Deref e) \<Down> (H', R'(p \<mapsto> kill t (the (R' p))), v)" |
  Plus: "\<lbrakk>(\<Gamma>, H, R, e1) \<Down> (H', R', VInt i1); (\<Gamma>, H', R', e2) \<Down> (H'', R'', VInt i2)\<rbrakk>
         \<Longrightarrow> (\<Gamma>, H, R, Plus e1 e2) \<Down> (H'', R'', VInt (i1 + i2))" |
  Less: "\<lbrakk>(\<Gamma>, H, R, e1) \<Down> (H', R', VInt i1); (\<Gamma>, H', R', e2) \<Down> (H'', R'', VInt i2)\<rbrakk>
         \<Longrightarrow> (\<Gamma>, H, R, Less e1 e2) \<Down> (H'', R'', VBool (i1 < i2))" |
  Not: "(\<Gamma>, H, R, e) \<Down> (H', R', VBool b) \<Longrightarrow> (\<Gamma>, H, R, Not e) \<Down> (H', R', VBool (\<not>b))" |
  And: "\<lbrakk>(\<Gamma>, H, R, e1) \<Down> (H', R', VBool b1); (\<Gamma>, H', R', e2) \<Down> (H'', R'', VBool b2)\<rbrakk>
         \<Longrightarrow> (\<Gamma>, H, R, And e1 e2) \<Down> (H'', R'', VBool (b1 \<and> b2))"

lemmas exp_sem_cases = exp_sem.cases[split_format(complete)]
lemmas exp_sem_induct = exp_sem.induct[split_format(complete)]
declare exp_sem.intros[simp]

inductive_cases ConstE[elim!]: "(\<Gamma>, H, R, Const v) \<Down> v'"
thm ConstE
inductive_cases VarE[elim!]: "(\<Gamma>, H, R, Var x) \<Down> v"
thm VarE
inductive_cases BoxE[elim!]: "(\<Gamma>, H, R, Box e) \<Down> v"
thm BoxE
inductive_cases ReborrowE[elim!]: "(\<Gamma>, H, R, Reborrow e) \<Down> v"
thm ReborrowE
inductive_cases DerefE[elim!]: "(\<Gamma>, H, R, Deref e) \<Down> v"
thm DerefE

text \<open>
  We have nice derivation trees as shown in Figure \ref{fig:exp}.
  Note that the validity of reference is not checked in the current
  REBORROW and DEREF rules.
\begin{figure}[h]
  \centering
\begin{framed}
  @{thm[mode=Rule] Var} \sc{Var}\\
  @{thm[mode=Rule] Box} \sc{Box} \\
  @{thm[mode=Rule] Reborrow} \sc{Reborrow} \\
  @{thm[mode=Rule] Deref} \sc{Deref}
\end{framed}
  \caption{Selected derivation rules for expressions}
  \label{fig:exp}
\end{figure}
\<close>

lemma box__writable: "(\<Gamma>, H, R, Box e) \<Down> (H', R', Reference p t) \<Longrightarrow> writable p t R'"
  by auto

lemma reborrow__writable: "(\<Gamma>, H, R, Reborrow e) \<Down> (H', R', Reference p t) \<Longrightarrow> writable p t R'"
  by auto

code_pred exp_sem .

end