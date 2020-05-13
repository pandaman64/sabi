theory Exp
  imports Definitions
begin

section \<open>Semantics of Expressions\<close>

text \<open>This section presents the big-step semantics of expressions.\<close>

inductive place_sem ::
  "gamma \<Rightarrow> heap \<Rightarrow> place \<Rightarrow> (address * tag) list * val \<Rightarrow> bool"
  ("(_; _ \<turnstile> _ \<Down>\<^sub>p _)")
where
  Var: "\<Gamma> x = (a, t) \<Longrightarrow> \<Gamma>; H \<turnstile> Var x \<Down>\<^sub>p ([], Reference a t)" |
  Deref: "\<lbrakk>\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refs, Reference a t); allocated H a\<rbrakk> \<Longrightarrow>
          \<Gamma>; H \<turnstile> Deref p \<Down>\<^sub>p ((a, t) # refs, fst (H ! a))"

text \<open>The relation @{const place_sem} describes the semantics of places.
\<^term>\<open>\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refs, v)\<close> means that a place expression \<^term>\<open>p\<close> evaluates to
a value \<^term>\<open>v\<close> under the environment \<^term>\<open>\<Gamma>\<close> and \<^term>\<open>H\<close>, where \<^term>\<open>refs\<close> are
the references used to retrieve the value (thus they need to be validated).\<close>

(*<*)
lemmas place_sem_cases = place_sem.cases[split_format(complete)]
lemmas place_sem_induct = place_sem.induct[split_format(complete)]
declare place_sem.intros[simp, intro]
inductive_cases place_sem_inv[elim!]:
  "\<Gamma>; H \<turnstile> Var x \<Down>\<^sub>p (refs, v)"
  "\<Gamma>; H \<turnstile> Deref p \<Down>\<^sub>p (refs, v)"
(*>*)

inductive operand_sem ::
  "gamma \<Rightarrow> heap \<Rightarrow> operand \<Rightarrow> (address * tag) list * val \<Rightarrow> bool"
  ("(_; _ \<turnstile> _ \<Down>\<^sub>o\<^sub>p _)")
where
  Place: "\<Gamma>; H \<turnstile> p \<Down>\<^sub>p v \<Longrightarrow> \<Gamma>; H \<turnstile> Place p \<Down>\<^sub>o\<^sub>p v" |
  Constant: "\<Gamma>; H \<turnstile> Constant v \<Down>\<^sub>o\<^sub>p ([], v)"

(*<*)
lemmas operand_sem_cases = operand_sem.cases[split_format(complete)]
lemmas operand_sem_induct = operand_sem.induct[split_format(complete)]
declare operand_sem.simps[simp, intro]
inductive_cases operand_sem_inv[elim!]:
  "\<Gamma>; H \<turnstile> Place p \<Down>\<^sub>o\<^sub>p v"
  "\<Gamma>; H \<turnstile> Constant v \<Down>\<^sub>o\<^sub>p v'"
(*>*)

inductive rvalue_sem ::
  "gamma * tags * heap * rvalue \<Rightarrow> tags * heap * val \<Rightarrow> bool" (infix "\<Down>" 65)
where
  Use: "\<lbrakk>\<Gamma>; H \<turnstile> op \<Down>\<^sub>o\<^sub>p (refs, v); list_all (readable H) refs\<rbrakk>
        \<Longrightarrow> (\<Gamma>, T, H, Use op) \<Down> (T, kill_all refs H, v)" |
  Box: "\<lbrakk>\<Gamma>; H \<turnstile> op \<Down>\<^sub>o\<^sub>p (refs, v); p = length H; t = length T\<rbrakk>
        \<Longrightarrow> (\<Gamma>, T, H, Box op) \<Down> (T @ [Unique], H @ [(v, [t])], Reference p t)" |
  Ref: "\<lbrakk>\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refs, Reference a t); list_all (readable H) refs\<rbrakk>
        \<Longrightarrow> (\<Gamma>, T, H, Ref p) \<Down> (T, kill_all refs H, Reference a t)" |
  Reborrow: "\<lbrakk>\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refs, Reference a t); list_all (writable H) refs;
              writable H (a, t); t' = length T;
              H' = kill_all ((a, t) # refs) H; H' ! a = (v, ts)\<rbrakk>
             \<Longrightarrow> (\<Gamma>, T, H, Reborrow p) \<Down> (T @ [Unique], H'[a := (v, ts @ [t'])] , Reference a t')" |
  Plus: "\<lbrakk>\<Gamma>; H \<turnstile> lhs \<Down>\<^sub>o\<^sub>p (rl, VInt lhs'); \<Gamma>; H \<turnstile> rhs \<Down>\<^sub>o\<^sub>p (rr, VInt rhs');
          list_all (readable H) rl; list_all (readable H) rr\<rbrakk>
         \<Longrightarrow> (\<Gamma>, T, H, Plus lhs rhs) \<Down> (T, kill_all (rr @ rl) H, VInt (lhs' + rhs'))" |
  Less: "\<lbrakk>\<Gamma>; H \<turnstile> lhs \<Down>\<^sub>o\<^sub>p (rl, VInt lhs'); \<Gamma>; H \<turnstile> rhs \<Down>\<^sub>o\<^sub>p (rr, VInt rhs');
          list_all (readable H) rl; list_all (readable H) rr\<rbrakk>
         \<Longrightarrow> (\<Gamma>, T, H, Less lhs rhs) \<Down> (T, kill_all (rr @ rl) H, VBool (lhs' < rhs'))" |
  Not: "\<lbrakk>\<Gamma>; H \<turnstile> op \<Down>\<^sub>o\<^sub>p (refs, VBool v); list_all (readable H) refs\<rbrakk>
         \<Longrightarrow> (\<Gamma>, T, H, Not op) \<Down> (T, kill_all refs H, VBool (\<not>v))" |
  And: "\<lbrakk>\<Gamma>; H \<turnstile> lhs \<Down>\<^sub>o\<^sub>p (rl, VBool lhs'); \<Gamma>; H \<turnstile> rhs \<Down>\<^sub>o\<^sub>p (rr, VBool rhs');
          list_all (readable H) rl; list_all (readable H) rr\<rbrakk>
         \<Longrightarrow> (\<Gamma>, T, H, And lhs rhs) \<Down> (T, kill_all (rr @ rl) H, VBool (lhs' \<and> rhs'))"

(*<*)
lemmas rvalue_sem_cases = rvalue_sem.cases[split_format(complete)]
lemmas rvalue_sem_induct = rvalue_sem.induct[split_format(complete)]
declare rvalue_sem.intros[simp, intro]
inductive_cases rvalue_sem_inv[elim!]:
  "(\<Gamma>, T, H, Use op) \<Down> (T', H', v)"
  "(\<Gamma>, T, H, Box op) \<Down> (T', H', v)"
  "(\<Gamma>, T, H, Ref p) \<Down> (T', H', v)"
  "(\<Gamma>, T, H, Reborrow p) \<Down> (T', H', v)"
  "(\<Gamma>, T, H, Plus lhs rhs) \<Down> (T', H', v)"
  "(\<Gamma>, T, H, Less lhs rhs) \<Down> (T', H', v)"
  "(\<Gamma>, T, H, Not op) \<Down> (T', H', v)"
  "(\<Gamma>, T, H, And lhs rhs) \<Down> (T', H', v)"
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
The validity of the access is checked by @{const_typ readable}.
Moreover, they invalidate all descendant references to establish the uniqueness.

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

lemma place_sem_det: "\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refs, v) \<Longrightarrow> \<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refs', v') \<Longrightarrow> (refs', v') = (refs, v)"
proof (induction arbitrary: refs' v' rule: place_sem.induct)
  case (Var \<Gamma> x a t H)
  then show ?case by auto
next
  case (Deref \<Gamma> H p refs a t)
  then show ?case by blast
qed
lemmas place_sem_det' = place_sem_det[split_format(complete)]

lemma operand_sem_det: "\<Gamma>; H \<turnstile> op \<Down>\<^sub>o\<^sub>p (refs, v) \<Longrightarrow> \<Gamma>; H \<turnstile> op \<Down>\<^sub>o\<^sub>p (refs', v') \<Longrightarrow> (refs', v') = (refs, v)"
proof (induction arbitrary: refs' v' rule: operand_sem.induct)
  case (Place \<Gamma> H p v)
  then show ?case
    by (metis operand_sem_inv(1) place_sem_det' surj_pair)
next
  case (Constant \<Gamma> H v)
  then show ?case by blast
qed
lemmas operand_sem_det' = operand_sem_det[split_format(complete)]

lemma rvalue_sem_det: "(\<Gamma>, T, H, rv) \<Down> (T', H', v') \<Longrightarrow> (\<Gamma>, T, H, rv) \<Down> (T'', H'', v'')
  \<Longrightarrow> (T'', H'', v'') = (T', H', v')"
proof (induction rule: rvalue_sem_induct)
  case (Use \<Gamma> H op refs v T)
  show "(T'', H'', v'') = (T, kill_all refs H, v)"
  proof (rule rvalue_sem_inv(1))
    fix refs'
    assume op: "(\<exists>p. op = Place p \<and> (\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refs', v''))) \<or> op = Constant v'' \<and> refs' = []"
    then have "\<Gamma>; H \<turnstile> op \<Down>\<^sub>o\<^sub>p (refs', v'')" by simp
    then have "refs' = refs" and "v'' = v" using Use.hyps(1) operand_sem_det' by auto
    then show "(T'', H'', v'') = (T, kill_all refs H, v)"
      using Use.prems op place_sem_det' by blast
  next
    show "(\<Gamma>, T, H, Use op) \<Down> (T'', H'', v'')" using Use.prems by auto
  qed
next
  case (Box \<Gamma> H op refs v p t T)
  then show ?case using place_sem_det' by auto
next
  case (Ref \<Gamma> H p refs a t T)
  then show ?case using place_sem_det' by fastforce
next
  case (Reborrow \<Gamma> H p refs a t t' T H' v ts)
  show "(T'', H'', v'') = (T @ [Unique], H'[a := (v, ts @ [t'])], Reference a t')"
  proof (rule rvalue_sem_inv(4))
    show "(\<Gamma>, T, H, Reborrow p) \<Down> (T'', H'', v'')" using Reborrow.prems by simp
  next
    fix refsa aa ta va tsa
    let ?kill = "(case kill_all refsa H ! aa of (va, tsa) \<Rightarrow> (kill_all refsa H)[aa := (va, kill ta tsa)])"
    assume "\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refsa, Reference aa ta)"
    then have "refsa = refs \<and> aa = a \<and> ta = t" using Reborrow.hyps place_sem_det' by blast
    then have "refsa = refs" and "aa = a" and "ta = t" by auto
    moreover assume "?kill ! aa = (va, tsa)"
    then have "va = v" and "tsa = ts" using Reborrow.hyps calculation by auto
    moreover assume "H'' = ?kill[aa := (va, tsa @ [length T])]"
    then have "H'' = H'[a := (v, ts @ [t'])]" by (simp add: Reborrow.hyps calculation)
    moreover assume "v'' = Reference aa (length T)"
    then have "v'' = Reference a t'" using Reborrow.hyps calculation by simp
    ultimately show ?thesis using Reborrow.prems by auto
  qed
next
  case (Plus \<Gamma> H lhs rl lhs' rhs rr rhs' T)
  show "(T'', H'', v'') = (T, kill_all (rr @ rl) H, VInt (lhs' + rhs'))"
  proof (rule rvalue_sem_inv(5))
    show "(\<Gamma>, T, H, Plus lhs rhs) \<Down> (T'', H'', v'')" using Plus.prems by simp
  next
    fix rla lhs'a rra rhs'a
    assume opl: "(\<exists>p. lhs = Place p \<and> (\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (rla, VInt lhs'a))) \<or>
            lhs = Constant (VInt lhs'a) \<and> rla = []" and
           opr: "(\<exists>p. rhs = Place p \<and> (\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (rra, VInt rhs'a))) \<or>
            rhs = Constant (VInt rhs'a) \<and> rra = []"
    then have "\<Gamma>; H \<turnstile> lhs \<Down>\<^sub>o\<^sub>p (rla, VInt lhs'a)" and "\<Gamma>; H \<turnstile> rhs \<Down>\<^sub>o\<^sub>p (rra, VInt rhs'a)" by auto
    then have "rla = rl \<and> lhs'a = lhs' \<and> rra = rr \<and> rhs'a = rhs'"
      using Plus.hyps operand_sem_det' by blast
    then have "rla = rl" and "lhs'a = lhs'" and "rra = rr" and "rhs'a = rhs'" by auto
    moreover assume "H'' = kill_all rra (kill_all rla H)" and "v'' = VInt (lhs'a + rhs'a)"
    then have "H'' = kill_all (rr @ rl) H" and "v'' = VInt (lhs' + rhs')"
      using calculation foldr_append by auto
    ultimately show ?thesis using Plus.prems by auto
  qed
next
  case (Less \<Gamma> H lhs rl lhs' rhs rr rhs' T)
  show "(T'', H'', v'') = (T, kill_all (rr @ rl) H, VBool (lhs' < rhs'))"
  proof (rule rvalue_sem_inv(6))
    show "(\<Gamma>, T, H, Less lhs rhs) \<Down> (T'', H'', v'')" using Less.prems by simp
  next
    fix rla lhs'a rra rhs'a
    assume opl: "(\<exists>p. lhs = Place p \<and> (\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (rla, VInt lhs'a))) \<or>
            lhs = Constant (VInt lhs'a) \<and> rla = []" and
           opr: "(\<exists>p. rhs = Place p \<and> (\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (rra, VInt rhs'a))) \<or>
            rhs = Constant (VInt rhs'a) \<and> rra = []"
    then have "\<Gamma>; H \<turnstile> lhs \<Down>\<^sub>o\<^sub>p (rla, VInt lhs'a)" and "\<Gamma>; H \<turnstile> rhs \<Down>\<^sub>o\<^sub>p (rra, VInt rhs'a)" by auto
    then have "rla = rl \<and> lhs'a = lhs' \<and> rra = rr \<and> rhs'a = rhs'"
      using Less.hyps operand_sem_det' by blast
    then have "rla = rl" and "lhs'a = lhs'" and "rra = rr" and "rhs'a = rhs'" by auto
    moreover assume "H'' = kill_all rra (kill_all rla H)" and "v'' = VBool (lhs'a < rhs'a)"
    then have "H'' = kill_all (rr @ rl) H" and "v'' = VBool (lhs' < rhs')"
      using calculation foldr_append by auto
    ultimately show ?thesis using Less.prems by auto
  qed
next
  case (Not \<Gamma> H op refs v T)
  show "(T'', H'', v'') = (T, kill_all refs H, VBool (\<not>v))"
  proof (rule rvalue_sem_inv(7))
    fix refsa va
    assume "(\<exists>p. op = Place p \<and> (\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refsa, VBool va))) \<or> op = Constant (VBool va) \<and> refsa = []"
    then show "(T'', H'', v'') = (T, kill_all refs H, VBool (\<not>v))"
      using Not.prems Not.hyps operand_sem_det' place_sem_det' by blast
  next
    show "(\<Gamma>, T, H, Not op) \<Down> (T'', H'', v'')" using Not.prems by simp
  qed
next
  case (And \<Gamma> H lhs rl lhs' rhs rr rhs' T)
  show "(T'', H'', v'') = (T, kill_all (rr @ rl) H, VBool (lhs' \<and> rhs'))"
  proof (rule rvalue_sem_inv(8))
    show "(\<Gamma>, T, H, And lhs rhs) \<Down> (T'', H'', v'')" using And.prems by simp
  next
    fix rla lhs'a rra rhs'a
    assume opl: "(\<exists>p. lhs = Place p \<and> (\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (rla, VBool lhs'a))) \<or>
            lhs = Constant (VBool lhs'a) \<and> rla = []" and
           opr: "(\<exists>p. rhs = Place p \<and> (\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (rra, VBool rhs'a))) \<or>
            rhs = Constant (VBool rhs'a) \<and> rra = []"
    then have "\<Gamma>; H \<turnstile> lhs \<Down>\<^sub>o\<^sub>p (rla, VBool lhs'a)" and "\<Gamma>; H \<turnstile> rhs \<Down>\<^sub>o\<^sub>p (rra, VBool rhs'a)" by auto
    then have "rla = rl \<and> lhs'a = lhs' \<and> rra = rr \<and> rhs'a = rhs'"
      using And.hyps operand_sem_det' by blast
    then have "rla = rl" and "lhs'a = lhs'" and "rra = rr" and "rhs'a = rhs'" by auto
    moreover assume "H'' = kill_all rra (kill_all rla H)" and "v'' = VBool (lhs'a \<and> rhs'a)"
    then have "H'' = kill_all (rr @ rl) H" and "v'' = VBool (lhs' \<and> rhs')"
      using calculation foldr_append by auto
    ultimately show ?thesis using And.prems by auto
  qed
qed

text \<open>The following lemmas are sanity checks of the semantics.
We must be able to write through the references retrieved by {\sc{Box}} and {\sc{Reborrow}}\<close>

lemma box__writable: "(\<Gamma>, T, H, Box e) \<Down> (T', H', Reference a t) \<Longrightarrow> writable H' (a, t)"
  by auto

lemma reborrow__writable: "(\<Gamma>, T, H, Reborrow p) \<Down> (T', H', Reference a t) \<Longrightarrow> writable H' (a, t)"
proof (rule rvalue_sem_inv(4))
  assume "(\<Gamma>, T, H, Reborrow p) \<Down> (T', H', Reference a t)"
  then show "(\<Gamma>, T, H, Reborrow p) \<Down> (T', H', Reference a t)" by auto
next
  fix refsa aa ta va tsa
  let ?kill = "(case kill_all refsa H ! aa of (va, tsa) \<Rightarrow> (kill_all refsa H)[aa := (va, kill ta tsa)])"
  assume "H' = ?kill[aa := (va, tsa @ [length T])]"
    and "aa < length H"
    and "?kill ! aa = (va, tsa)"
  then have "H' ! aa = (va, tsa @ [length T])"
    by (metis (no_types, lifting) kill_all_preserve_length length_list_update
      nth_list_update_eq prod.case_eq_if)
  moreover assume "Reference a t = Reference aa (length T)"
  then have "aa = a" and "t = length T" by auto
  ultimately have alen: "a < length H" and elem: "H' ! a = (va, tsa @ [t])"
    using \<open>aa < length H\<close> by auto

  assume "H' = ?kill[aa := (va, tsa @ [length T])]"
  then have alen': "a < length H'"
    using alen kill_all_preserve_length kill_preserve_length by force

  have "t \<in> set (snd (H' ! a))" by (simp add: elem)
  with alen' show ?thesis by auto
qed

end