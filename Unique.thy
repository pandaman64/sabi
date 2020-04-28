theory Unique
  imports Main Definitions Exp Star
begin

section \<open>Semantics\<close>

type_synonym config = "gamma * heap * reborrow * com"
inductive com_sem :: "config \<Rightarrow> config \<Rightarrow> bool" (infix "\<rightarrow>" 65)
where
  VAssign: "(\<Gamma>, H, R, e) \<Down> (H', R', v)
            \<Longrightarrow> (\<Gamma>, H, R, x ::= e) \<rightarrow> (\<Gamma>(x := Some v), H', R', Skip)" |
  (* TODO: check validity of pointer? *)
  HAssign: "\<lbrakk>(\<Gamma>, H, R, e\<^sub>l) \<Down> (H', R', Reference p t);
             (\<Gamma>, H', R', e\<^sub>v) \<Down> (H'', R'', v);
             writable p t R''\<rbrakk>
            \<Longrightarrow> (\<Gamma>, H, R, *e\<^sub>l ::= e\<^sub>v) \<rightarrow> (\<Gamma>, H''(p := Some v), R''(p \<mapsto> kill t (the (R'' p))), Skip)" |
  SeqL: "(\<Gamma>, H, R, Skip;; c) \<rightarrow> (\<Gamma>, H, R, c)" |
  SeqR: "(\<Gamma>, H, R, C1) \<rightarrow> (\<Gamma>', H', R', c') \<Longrightarrow> (\<Gamma>, H, R, c1;; c2) \<rightarrow> (\<Gamma>', H', R', c';; c2)" |
  IfTrue: "(\<Gamma>, H, R, b) \<Down> (H', R', VBool True)
           \<Longrightarrow> (\<Gamma>, H, R, IF b THEN c1 ELSE c2) \<rightarrow> (\<Gamma>, H', R', c1)" |
  IfFlase: "(\<Gamma>, H, R, b) \<Down> (H', R', VBool False)
           \<Longrightarrow> (\<Gamma>, H, R, IF b THEN c1 ELSE c2) \<rightarrow> (\<Gamma>, H', R', c2)" |
  While: "(\<Gamma>, H, R, WHILE b DO c) \<rightarrow> (\<Gamma>, H, R, IF b THEN (c;; WHILE b DO c) ELSE Skip)"

(* We declare safe elimination rules (automatically applied I guess?) *)
inductive_cases [elim!]:
  "(\<Gamma>, H, R, x ::= e) \<rightarrow> cfg"
  "(\<Gamma>, H, R, *e\<^sub>l ::= e\<^sub>v) \<rightarrow> cfg"
  "(\<Gamma>, H, R, Skip;; c) \<rightarrow> cfg"
  "(\<Gamma>, H, R, c1;; c2) \<rightarrow> cfg"
  "(\<Gamma>, H, R, IF b THEN c1 ELSE c2) \<rightarrow> cfg"

(* WHILE might not terminate, so we declare it as an unsafe elimination rule *)
inductive_cases WhileE[elim]: "(\<Gamma>, H, R, WHILE b DO c) \<rightarrow> cfg"
thm WhileE

abbreviation com_sem_steps :: "config \<Rightarrow> config \<Rightarrow> bool" (infix "\<rightarrow>\<^sup>*" 65) where
  "cfg \<rightarrow>\<^sup>* cfg' == star com_sem cfg cfg'"

text \<open>
  Figure \ref{fig:com} shows the assignment rules. Other commands are standard.
\begin{figure}[h]
\centering
\begin{framed}
@{thm[mode=Rule] VAssign} \sc{VAssign} \\
@{thm[mode=Rule] HAssign} \sc{HAssign}
\end{framed}
\caption{Assignment rules}
\label{fig:com}
\end{figure}
\<close>

code_pred com_sem .

section \<open>Choosing fresh addresses/tags deterministically\<close>

definition empty :: "'a \<Rightarrow> 'b option" where
  "empty = (\<lambda>_. None)"

inductive packed_heap :: "nat \<Rightarrow> heap \<Rightarrow> bool" where
  EmptyH: "packed_heap 0 empty" |
  NextH: "packed_heap n H \<Longrightarrow> packed_heap (n + 1) (H(Address n \<mapsto> v))"

lemma packed_heap__domain: "packed_heap n H \<Longrightarrow> (\<forall>n'. n' \<ge> n \<longleftrightarrow> H (Address n') = None)"
proof (induction rule: packed_heap.induct)
  case EmptyH
  then show ?case
    by (simp add: Unique.empty_def)
next
  case (NextH n H v)
  then show ?case
    by (metis One_nat_def add.right_neutral add_Suc_right address.inject
        fun_upd_apply le_less le_simps(3) not_le option.discI)
qed

lemma packed_heap__fresh: "packed_heap n H \<Longrightarrow> fresh (Address n) H"
proof (induction rule: packed_heap.induct)
  case EmptyH
  then show ?case
    by (simp add: Unique.empty_def fresh_def)
next
  case (NextH n H v)
  then show ?case
    by (meson fresh_def le_less packed_heap.NextH packed_heap__domain)
qed

definition packed_tags :: "nat \<Rightarrow> reborrow \<Rightarrow> bool" where
  "packed_tags n R \<longleftrightarrow> tags R = {Tag k | k. k < n}"

lemma packed_tags__fresh: "packed_tags n R \<Longrightarrow> fresh_tag (Tag n) R"
  by (simp add: fresh_tag_def packed_tags_def)

section \<open>Code examples\<close>

text \<open>The following code accesss \<close>

definition XYX :: com where
  "XYX = 
    ''root'' ::= Box (Const (VInt 42));;
    ''px'' ::= Reborrow (Var ''root'');;
    *(Var ''px'') ::= Const (VInt 100);;
    ''py'' ::= Reborrow (Var ''root'');;
    *(Var ''px'') ::= Const (VInt 200)"

end