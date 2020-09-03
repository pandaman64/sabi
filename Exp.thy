theory Exp
  imports Definitions
begin

section \<open>Semantics of Expressions\<close>

text \<open>This section presents the big-step semantics of expressions.\<close>

text \<open>Introducing a locale here looks a good idea as it helps us formulate
axioms among the heap access modifier. Expected axioms:
\<^item> Modifier must be idempotent: \<^term>\<open>m p (m p H) = m p H\<close>.
\<^item> Modifier must not allocate/deallocate a memory cell: \<^term>\<open>length (m p H) = length H\<close>.
\<^item> The content is left intact: \<^term>\<open>fst ((m p H) ! a) = fst (H ! a)\<close>
\<close>

type_synonym modifier = "(address * tag) \<Rightarrow> heap \<Rightarrow> heap option"
fun write_access :: modifier where
  "write_access (a, t) H =
    (if writable H (a, t) then
      let (v, ts) = H ! a in
      Some (H[a := (v, kill t ts)])
     else None)"
fun read_access :: modifier where
  "read_access (a, t) H =
    (if readable H (a, t) then
      let (v, ts) = H ! a in
      Some (H[a := (v, kill t ts)])
     else None)"

inductive place_sem ::
  "gamma \<Rightarrow> modifier \<Rightarrow> heap * place \<Rightarrow> heap * val \<Rightarrow> bool"
  ("(_; _ \<turnstile> _ \<Down>\<^sub>p _)") for \<Gamma> m
where
  Var: "\<Gamma> x = (a, t) \<Longrightarrow> \<Gamma>; m \<turnstile> (H, Var x) \<Down>\<^sub>p (H, Reference a t)" |
  Deref: "\<lbrakk>\<Gamma>; m \<turnstile> (H, p) \<Down>\<^sub>p (H', Reference a t); m (a, t) H' = Some H''\<rbrakk> \<Longrightarrow>
          \<Gamma>; m \<turnstile> (H, Deref p) \<Down>\<^sub>p (H'', fst (H'' ! a))"

text \<open>The relation @{const place_sem} describes the semantics of places
with respect to a heap access modifier \<^term>\<open>m\<close>.
\<^term>\<open>\<Gamma>; m \<turnstile> (H, p) \<Down>\<^sub>p (H', v)\<close> means that a place expression \<^term>\<open>p\<close> evaluates to
a value \<^term>\<open>v\<close> under the environment \<^term>\<open>\<Gamma>\<close> and \<^term>\<open>H\<close>, while the access
has changed the state of the heap to \<^term>\<open>H'\<close>.\<close>

text \<open>We give a shorthand for read and write access to the place.\<close>

abbreviation read_place_sem :: "gamma \<Rightarrow> heap * place \<Rightarrow> heap * val \<Rightarrow> bool"
  ("(_ \<turnstile>\<^sub>r _ \<Down>\<^sub>p _)")
  where
  "\<Gamma> \<turnstile>\<^sub>r p \<Down>\<^sub>p v == \<Gamma>; read_access \<turnstile> p \<Down>\<^sub>p v"
abbreviation write_place_sem :: "gamma \<Rightarrow> heap * place \<Rightarrow> heap * val \<Rightarrow> bool"
  ("(_ \<turnstile>\<^sub>w _ \<Down>\<^sub>p _)")
  where
  "\<Gamma> \<turnstile>\<^sub>w p \<Down>\<^sub>p v == \<Gamma>; write_access \<turnstile> p \<Down>\<^sub>p v"

(*<*)
lemmas place_sem_cases = place_sem.cases[split_format(complete)]
lemmas place_sem_induct = place_sem.induct[split_format(complete)]
declare place_sem.intros[simp, intro]
inductive_cases place_sem_inv[elim!]:
  "\<Gamma>; m \<turnstile> (H, Var x) \<Down>\<^sub>p (H', v)"
  "\<Gamma>; m \<turnstile> (H, Deref p) \<Down>\<^sub>p (H', v)"
(*>*)

text \<open>Note that every operand is considered as a read access to the place.\<close>

inductive operand_sem ::
  "gamma \<Rightarrow> heap * operand \<Rightarrow> heap * val \<Rightarrow> bool"
  ("(_ \<turnstile> _ \<Down>\<^sub>o\<^sub>p _)") for \<Gamma>
where
  Place: "\<Gamma> \<turnstile>\<^sub>r (H, p) \<Down>\<^sub>p v \<Longrightarrow> \<Gamma> \<turnstile> (H, Place p) \<Down>\<^sub>o\<^sub>p v" |
  Constant: "\<Gamma> \<turnstile> (H, Constant v) \<Down>\<^sub>o\<^sub>p (H, v)"

(*<*)
lemmas operand_sem_cases = operand_sem.cases[split_format(complete)]
lemmas operand_sem_induct = operand_sem.induct[split_format(complete)]
declare operand_sem.simps[simp, intro]
inductive_cases operand_sem_inv[elim!]:
  "\<Gamma> \<turnstile> (H, Place p) \<Down>\<^sub>o\<^sub>p v"
  "\<Gamma> \<turnstile> (H, Constant v) \<Down>\<^sub>o\<^sub>p v'"
(*>*)

inductive rvalue_sem ::
  "gamma \<Rightarrow> tags * heap * rvalue \<Rightarrow> tags * heap * val \<Rightarrow> bool"
  ("(_ \<turnstile> _ \<Down> _)") for \<Gamma>
where
  Use: "\<Gamma> \<turnstile> (H, op) \<Down>\<^sub>o\<^sub>p (H', v) \<Longrightarrow> \<Gamma> \<turnstile> (T, H, Use op) \<Down> (T, H', v)" |
  Box: "\<lbrakk>\<Gamma> \<turnstile> (H, op) \<Down>\<^sub>o\<^sub>p (H', v); p = length H'; t = length T\<rbrakk>
        \<Longrightarrow> \<Gamma> \<turnstile> (T, H, Box op) \<Down> (T @ [Unique], H' @ [(v, [t])], Reference p t)" |
  Ref: "\<Gamma> \<turnstile>\<^sub>w (H, p) \<Down>\<^sub>p (H', Reference a t) \<Longrightarrow> \<Gamma> \<turnstile> (T, H, Ref p) \<Down> (T, H', Reference a t)" |
  Reborrow: "\<lbrakk>\<Gamma> \<turnstile>\<^sub>w (H, p) \<Down>\<^sub>p (H', Reference a t); writable H (a, t);
              t' = length T; H' ! a = (v, ts)\<rbrakk>
             \<Longrightarrow> \<Gamma> \<turnstile> (T, H, Reborrow p) \<Down> (T @ [Unique], H'[a := (v, ts @ [t'])], Reference a t')" |
  Plus: "\<lbrakk>\<Gamma> \<turnstile> (H, lhs) \<Down>\<^sub>o\<^sub>p (H', VInt lhs'); \<Gamma> \<turnstile> (H', rhs) \<Down>\<^sub>o\<^sub>p (H'', VInt rhs')\<rbrakk>
         \<Longrightarrow> \<Gamma> \<turnstile> (T, H, Plus lhs rhs) \<Down> (T, H'', VInt (lhs' + rhs'))" |
  Less: "\<lbrakk>\<Gamma> \<turnstile> (H, lhs) \<Down>\<^sub>o\<^sub>p (H', VInt lhs'); \<Gamma> \<turnstile> (H', rhs) \<Down>\<^sub>o\<^sub>p (H'', VInt rhs')\<rbrakk>
         \<Longrightarrow> \<Gamma> \<turnstile> (T, H, Less lhs rhs) \<Down> (T, H'', VBool (lhs' < rhs'))" |
  Not: "\<Gamma> \<turnstile> (H, op) \<Down>\<^sub>o\<^sub>p (H', VBool v) \<Longrightarrow> \<Gamma> \<turnstile> (T, H, Not op) \<Down> (T, H', VBool (\<not>v))" |
  And: "\<lbrakk>\<Gamma> \<turnstile> (H, lhs) \<Down>\<^sub>o\<^sub>p (H', VBool lhs'); \<Gamma> \<turnstile> (H', rhs) \<Down>\<^sub>o\<^sub>p (H'', VBool rhs')\<rbrakk>
         \<Longrightarrow> \<Gamma> \<turnstile> (T, H, And lhs rhs) \<Down> (T, H'', VBool (lhs' \<and> rhs'))"

(*<*)
lemmas rvalue_sem_cases = rvalue_sem.cases[split_format(complete)]
lemmas rvalue_sem_induct = rvalue_sem.induct[split_format(complete)]
declare rvalue_sem.intros[simp, intro]
inductive_cases rvalue_sem_inv[elim!]:
  "\<Gamma> \<turnstile> (T, H, Use op) \<Down> (T', H', v)"
  "\<Gamma> \<turnstile> (T, H, Box op) \<Down> (T', H', v)"
  "\<Gamma> \<turnstile> (T, H, Ref p) \<Down> (T', H', v)"
  "\<Gamma> \<turnstile> (T, H, Reborrow p) \<Down> (T', H', v)"
  "\<Gamma> \<turnstile> (T, H, Plus lhs rhs) \<Down> (T', H', v)"
  "\<Gamma> \<turnstile> (T, H, Less lhs rhs) \<Down> (T', H', v)"
  "\<Gamma> \<turnstile> (T, H, Not op) \<Down> (T', H', v)"
  "\<Gamma> \<turnstile> (T, H, And lhs rhs) \<Down> (T', H', v)"
(*>*)

text \<open>
Some TODO notes on the semantics of expressions:
\<^item> I don't get the semantics of @{const Ref} in MIR and how it should behave under the auto-boxing of variables.
\<^item> I'm not sure readable/writable checking is correct.
\<close>

text \<open>
We present the intuition behind the selected rules.
First, {\sc{Box}} rule allocates a new slot at the end of heap,
returning a reference pointing to the slot with a fresh tag.

\begin{framed}
\centering
@{thm[mode=Rule] Box} \sc{Box}
\end{framed}

Next, {\sc{Use}} and {\sc{Ref}} rules allow us to read the content through a place (or give a constant).

\begin{framed}
\centering
@{thm[mode=Rule] Use} \sc{Use}\\
@{thm[mode=Rule] Ref} \sc{Ref}
\end{framed}

Last but not least, {\sc{Reborrow}} rule creates a new reference pointing to the same object but with a fresh tag.
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

text \<open>We can prove that the semantics of expressions is deterministic.\<close>

lemma place_sem_det: "\<Gamma>; m \<turnstile> p \<Down>\<^sub>p v \<Longrightarrow> \<Gamma>; m \<turnstile> p \<Down>\<^sub>p v' \<Longrightarrow> v' = v"
proof (induction arbitrary: v' rule: place_sem.induct)
  case (Var x a t H)
  then show ?case
    by (metis Pair_inject place_sem_inv(1) surj_pair)
next
  case (Deref m H p H' a t H'')
  then show ?case
  sorry
  (*
    by (smt Pair_inject option.inject place_sem_inv(2) surj_pair val.inject(3))
  *)
qed
lemma place_sem_det': "\<Gamma>; m \<turnstile> (H, p) \<Down>\<^sub>p (H', v') \<Longrightarrow> \<Gamma>; m \<turnstile> (H, p) \<Down>\<^sub>p (H'', v'')
  \<Longrightarrow> (H'', v'') = (H', v')"
  using place_sem_det by auto

lemma operand_sem_det: "\<Gamma> \<turnstile> op \<Down>\<^sub>o\<^sub>p v \<Longrightarrow> \<Gamma> \<turnstile> op \<Down>\<^sub>o\<^sub>p v' \<Longrightarrow> v' = v"
proof (induction arbitrary: v' rule: operand_sem.induct)
  case (Place \<Gamma> H p v)
  then show ?case
    by (metis operand_sem_inv(1) place_sem_det' surj_pair)
next
  case (Constant \<Gamma> H v)
  then show ?case by blast
qed
lemma operand_sem_det': "\<Gamma> \<turnstile> (H, op) \<Down>\<^sub>o\<^sub>p (H', v') \<Longrightarrow> \<Gamma> \<turnstile> (H, op) \<Down>\<^sub>o\<^sub>p (H'', v'')
  \<Longrightarrow> (H'', v'') = (H', v')"
  using operand_sem_det by blast

lemma rvalue_sem_det: "\<Gamma> \<turnstile> (T, H, rv) \<Down> (T', H', v') \<Longrightarrow> \<Gamma> \<turnstile> (T, H, rv) \<Down> (T'', H'', v'')
  \<Longrightarrow> (T'', H'', v'') = (T', H', v')"
proof (induction arbitrary: T'' H'' v'' rule: rvalue_sem_induct)
  case (Use H op H' v T)
  then show ?case using operand_sem_det' by fastforce
next
  case (Box H op H' v p t T)
  then show ?case using place_sem_det' by blast
next
  case (Ref H p H' a t T)
  then show ?case using place_sem_det' by blast
next
  case (Reborrow H p H' a t t' T v ts)
  show ?case
  proof (rule rvalue_sem_inv(4))
    show "\<Gamma> \<turnstile> (T, H, Reborrow p) \<Down> (T'', H'', v'')" using Reborrow.prems by simp
  next
    fix H'a aa ta va tsa
    assume "\<Gamma> \<turnstile>\<^sub>w (H, p) \<Down>\<^sub>p (H'a, Reference aa ta)"
    then have "H'a = H' \<and> aa = a \<and> ta = t" using Reborrow.hyps place_sem_det by fastforce
    moreover assume "H'a ! aa = (va, tsa)"
    then have "va = v \<and> tsa = ts" using Reborrow.hyps calculation by auto
    moreover assume "H'' = H'a[aa := (va, tsa @ [length T])]"
    then have "H'' = H'a[a := (v, ts @ [t'])]" using Reborrow.hyps calculation by simp
    moreover assume "v'' = Reference aa (length T)"
    then have "v'' = Reference a t'" using Reborrow.hyps calculation by simp
    moreover assume "T'' = T @ [Unique]"
    thus ?thesis using calculation by simp
  qed
next
  case (Plus H lhs H' lhs' rhs He rhs' T)
  show ?case
  proof (rule rvalue_sem_inv(5))
    show "\<Gamma> \<turnstile> (T, H, Plus lhs rhs) \<Down> (T'', H'', v'')" using Plus.prems by simp
  next
    fix H'a lhs'a rhs'a
    assume "(\<exists>p. lhs = Place p \<and> (\<Gamma> \<turnstile>\<^sub>r (H, p) \<Down>\<^sub>p (H'a, VInt lhs'a)))
            \<or> lhs = Constant (VInt lhs'a) \<and> H'a = H"
    then have "lhs'a = lhs' \<and> H'a = H'" using Plus.hyps operand_sem_det' by fastforce
    moreover
    assume "(\<exists>p. rhs = Place p \<and> (\<Gamma> \<turnstile>\<^sub>r (H'a, p) \<Down>\<^sub>p (H'', VInt rhs'a)))
            \<or> rhs = Constant (VInt rhs'a) \<and> H'' = H'a"
    then have "rhs'a = rhs' \<and> He = H''"
      using Plus.hyps calculation operand_sem_det' by fastforce
    moreover assume "v'' = VInt (lhs'a + rhs'a)"
    thus ?thesis using calculation Plus.prems by auto
  qed
next
  case (Less H lhs H' lhs' rhs He rhs' T)
  show ?case
  proof (rule rvalue_sem_inv(6))
    show "\<Gamma> \<turnstile> (T, H, Less lhs rhs) \<Down> (T'', H'', v'')" using Less.prems by simp
  next
    fix H'a lhs'a rhs'a
    assume "(\<exists>p. lhs = Place p \<and> (\<Gamma> \<turnstile>\<^sub>r (H, p) \<Down>\<^sub>p (H'a, VInt lhs'a)))
            \<or> lhs = Constant (VInt lhs'a) \<and> H'a = H"
    then have "lhs'a = lhs' \<and> H'a = H'" using Less.hyps operand_sem_det' by fastforce
    moreover
    assume "(\<exists>p. rhs = Place p \<and> (\<Gamma> \<turnstile>\<^sub>r (H'a, p) \<Down>\<^sub>p (H'', VInt rhs'a)))
            \<or> rhs = Constant (VInt rhs'a) \<and> H'' = H'a"
    then have "rhs'a = rhs' \<and> He = H''"
      using Less.hyps calculation operand_sem_det' by fastforce
    moreover assume "v'' = VBool (lhs'a < rhs'a)"
    thus ?thesis using calculation Less.prems by auto
  qed
next
  case (Not H op H' v T)
  show ?case
  proof (rule rvalue_sem_inv(7))
    show "\<Gamma> \<turnstile> (T, H, Not op) \<Down> (T'', H'', v'')" using Not.prems by simp
  next
    fix va
    assume "(\<exists>p. op = Place p \<and> (\<Gamma> \<turnstile>\<^sub>r (H, p) \<Down>\<^sub>p (H'', VBool va)))
            \<or> op = Constant (VBool va) \<and> H'' = H"
    then have "H'' = H' \<and> va = v" using Not.hyps operand_sem_det' by fastforce
    moreover assume "T'' = T" and "v'' = VBool (\<not>va)"
    thus ?thesis by (simp add: calculation)
  qed
next
  case (And H lhs H' lhs' rhs He rhs' T)
  show ?case
  proof (rule rvalue_sem_inv(8))
    show "\<Gamma> \<turnstile> (T, H, And lhs rhs) \<Down> (T'', H'', v'')" using And.prems by simp
  next
    fix H'a lhs'a rhs'a
    assume "(\<exists>p. lhs = Place p \<and> (\<Gamma> \<turnstile>\<^sub>r (H, p) \<Down>\<^sub>p (H'a, VBool lhs'a)))
            \<or> lhs = Constant (VBool lhs'a) \<and> H'a = H"
    then have "lhs'a = lhs' \<and> H'a = H'" using And.hyps operand_sem_det' by fastforce
    moreover
    assume "(\<exists>p. rhs = Place p \<and> (\<Gamma> \<turnstile>\<^sub>r (H'a, p) \<Down>\<^sub>p (H'', VBool rhs'a)))
            \<or> rhs = Constant (VBool rhs'a) \<and> H'' = H'a"
    then have "rhs'a = rhs' \<and> He = H''"
      using And.hyps calculation operand_sem_det' by fastforce
    moreover assume "v'' = VBool (lhs'a \<and> rhs'a)"
    thus ?thesis using calculation And.prems by auto
  qed
qed

text \<open>The following lemmas are sanity checks of the semantics.
We must be able to write through the references retrieved by {\sc{Box}} and {\sc{Reborrow}} rules.\<close>

lemma box_writable: "\<Gamma> \<turnstile> (T, H, Box e) \<Down> (T', H', Reference a t) \<Longrightarrow> writable H' (a, t)"
  by auto

lemma wa_preserve_length: "write_access at H = Some H' \<Longrightarrow> length H' = length H"
  sorry
  (*
  by (smt kill_heap.simps kill_preserve_length option.distinct(1)
          option.sel prod.case_eq_if write_access.elims)
*)

lemma write_preserve_length: "\<Gamma> \<turnstile>\<^sub>w p \<Down>\<^sub>p v \<Longrightarrow> length (fst p) = length (fst v)"
proof (induction rule: place_sem.induct)
  case (Var x a t H)
  then show ?case by simp
next
  case (Deref H p H' a t H'')
  assume "write_access (a, t) H' = Some H''"
  then have "length H'' = length H'" using wa_preserve_length by blast
  moreover
  assume "length (fst (H, p)) = length (fst (H', Reference a t))"
  then have "length H = length H'" by simp
  ultimately have "length H'' = length H" by simp
  thus ?case by simp
qed

lemma reborrow_writable: "\<Gamma> \<turnstile> (T, H, Reborrow p) \<Down> (T', H', Reference a t) \<Longrightarrow> writable H' (a, t)"
proof (rule rvalue_sem_inv(4))
  assume "\<Gamma> \<turnstile> (T, H, Reborrow p) \<Down> (T', H', Reference a t)"
  then show "\<Gamma> \<turnstile> (T, H, Reborrow p) \<Down> (T', H', Reference a t)" by auto
next
  fix H'a aa ta va tsa
  assume "Reference a t = Reference aa (length T)"
  then have "aa = a" and "length T = t" by auto

  assume "\<Gamma> \<turnstile>\<^sub>w (H, p) \<Down>\<^sub>p (H'a, Reference aa ta)"
  then have "length H'a = length H" using write_preserve_length by auto
  moreover assume "aa < length H" then have "aa < length H'a" using calculation by simp
  moreover assume "H' = H'a[aa := (va, tsa @ [length T])]"
  then have "H' ! a = (va, tsa @ [t])" and "length H' = length H'a"
    using \<open>aa < length H\<close> \<open>aa = a\<close> \<open>length T = t\<close> calculation by auto
  thus ?thesis using \<open>aa = a\<close> \<open>aa < length H'a\<close> by auto
qed

end
