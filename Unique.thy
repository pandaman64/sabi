theory Unique
  imports Main Definitions Exp Star
begin

section \<open>Semantics of Commands\<close>

text \<open>This section describes the small-step semantics of commands.
The configuration of an execution consists of
\begin{itemize}
  \item the variable environment $\Gamma$ (of type @{type gamma});
  \item the heap $H$ (of type @{type heap}) which holds the actual data and the reborrow trees
  for each address; and
  \item the command to be executed $c$ (of type @{type com}).
\end{itemize}\<close>

type_synonym config = "gamma * heap * com"
inductive com_sem :: "config \<Rightarrow> config \<Rightarrow> bool" (infix "\<rightarrow>" 65)
where
  VAssign: "(\<Gamma>, H, e) \<Down> (H', v)
            \<Longrightarrow> (\<Gamma>, H, x ::= e) \<rightarrow> (\<Gamma>(x \<mapsto> v), H', Skip)" |
  HAssign: "\<lbrakk>(\<Gamma>, H, e\<^sub>l) \<Down> (H', Reference p t);
             (\<Gamma>, H', e\<^sub>v) \<Down> (H'', v);
             writable p t H''\<rbrakk>
            \<Longrightarrow> (\<Gamma>, H, *e\<^sub>l ::= e\<^sub>v) \<rightarrow> (\<Gamma>, H''[p := (v, kill t (snd (H'' ! p)))], Skip)" |
  SeqL: "(\<Gamma>, H, Skip;; c) \<rightarrow> (\<Gamma>, H, c)" |
  SeqR: "(\<Gamma>, H, c1) \<rightarrow> (\<Gamma>', H', c') \<Longrightarrow> (\<Gamma>, H, c1;; c2) \<rightarrow> (\<Gamma>', H', c';; c2)" |
  IfTrue: "(\<Gamma>, H, b) \<Down> (H', VBool True)
           \<Longrightarrow> (\<Gamma>, H, IF b THEN c1 ELSE c2) \<rightarrow> (\<Gamma>, H', c1)" |
  IfFlase: "(\<Gamma>, H, b) \<Down> (H', VBool False)
           \<Longrightarrow> (\<Gamma>, H, IF b THEN c1 ELSE c2) \<rightarrow> (\<Gamma>, H', c2)" |
  While: "(\<Gamma>, H, WHILE b DO c) \<rightarrow> (\<Gamma>, H, IF b THEN (c;; WHILE b DO c) ELSE Skip)"

code_pred [show_modes] com_sem .

lemmas com_sem_cases = com_sem.cases[split_format(complete)] \<^marker>\<open>tag invisible\<close>
lemmas com_sem_induct = com_sem.induct[split_format(complete)] \<^marker>\<open>tag invisible\<close>

declare com_sem.intros[simp, intro] \<^marker>\<open>tag invisible\<close>

(* We declare safe elimination rules (automatically applied I guess?) *)
inductive_cases ComE[elim!]: \<^marker>\<open>tag invisible\<close>
  "(\<Gamma>, H, x ::= e) \<rightarrow> cfg"
  "(\<Gamma>, H, *e\<^sub>l ::= e\<^sub>v) \<rightarrow> cfg"
  "(\<Gamma>, H, Skip;; c) \<rightarrow> cfg"
  "(\<Gamma>, H, c1;; c2) \<rightarrow> cfg"
  "(\<Gamma>, H, IF b THEN c1 ELSE c2) \<rightarrow> cfg"

(* WHILE might not terminate, so we declare it as an unsafe elimination rule *)
inductive_cases WhileE[elim]: "(\<Gamma>, H, WHILE b DO c) \<rightarrow> cfg" \<^marker>\<open>tag invisible\<close>

abbreviation com_sem_steps :: "config \<Rightarrow> config \<Rightarrow> bool" (infix "\<rightarrow>\<^sup>*" 65) where
  "cfg \<rightarrow>\<^sup>* cfg' == star com_sem cfg cfg'"

text \<open>
Figure \ref{fig:com} shows the assignment rules. Other commands are standard.

The {\sc{VAssign}} rule assigns a value to the variable while
the {\sc{HAssign}} rule to the location the reference on the left hand side is referring to.
To assign through a reference, the reference must be valid for writes.
Moreover, the write is considered as a use of the reference; it will invalidate the child references.

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

text \<open>The following lemmas show that the execution of the commands is deterministic.\<close>

definition final :: "config \<Rightarrow> bool" where
  "final cfg \<longleftrightarrow> (case cfg of (_, _, Skip) \<Rightarrow> True | _ \<Rightarrow> False)"

definition stuck :: "config \<Rightarrow> bool" where
  "stuck cfg \<longleftrightarrow> (case cfg of
     (_, _, Skip) \<Rightarrow> False |
     _ \<Rightarrow> \<not>(\<exists>cfg'. cfg \<rightarrow> cfg'))"

lemma skip_final_noteq[simp]: "(\<Gamma>, H, c) \<rightarrow> (\<Gamma>', H', c') \<Longrightarrow> c \<noteq> Skip"
proof (cases rule: com_sem_cases)
qed auto

lemma skip_final[simp]: "\<not>(\<Gamma>, H, Skip) \<rightarrow> (\<Gamma>', H', c)"
proof
  assume "(\<Gamma>, H, Skip) \<rightarrow> (\<Gamma>', H', c)"
  thus False using skip_final_noteq by blast
qed

lemma com_sem_deterministic: "cfg \<rightarrow> cfg' \<Longrightarrow> cfg \<rightarrow> cfg'' \<Longrightarrow> cfg'' = cfg'"
proof (induction arbitrary: cfg'' rule: com_sem.induct)
  case (VAssign \<Gamma> H e H' v x)
  then show ?case
    using exp_sem_deterministic by auto
next
  case (HAssign \<Gamma> H e\<^sub>l H' p t e\<^sub>v H'' v)
  then show ?case
    by (smt ComE(2) Pair_inject exp_sem_deterministic val.inject(3))
next
  case (SeqL \<Gamma> H c)
  then show ?case using skip_final by auto
next
  case (SeqR \<Gamma> H c1 \<Gamma>' H' c' c2)
  then show ?case by (metis ComE(4) prod.inject skip_final)
next
  case (IfTrue \<Gamma> H b H' c1 c2)
then show ?case using exp_sem_deterministic by fastforce
next
  case (IfFlase \<Gamma> H b H' c1 c2)
then show ?case using exp_sem_deterministic by fastforce
next
  case (While \<Gamma> H b c)
  then show ?case by auto
qed

lemmas star_induct' = star.induct[of "(\<rightarrow>)", split_format(complete)] \<^marker>\<open>tag invisible\<close>

text \<open>We show the transitivity of @{const com_sem_steps}.\<close>

lemma com_seql_trans:
  "(\<Gamma>, H, c1) \<rightarrow>\<^sup>* (\<Gamma>', H', c1') \<Longrightarrow> (\<Gamma>, H, c1;; c2) \<rightarrow>\<^sup>* (\<Gamma>', H', c1';; c2)"
proof (induction rule: star_induct')
  case (refl a a b)
  then show ?case by simp
next
  case (step a a b a a b a a b)
  then show ?case by (meson SeqR star.simps)
qed

section \<open>Code examples\<close>

subsection \<open>Invalidating a reference\<close>

text \<open>Consider the following Rust program.
\begin{minted}[linenos]{rust}
let mut root = Box::new(42);
let mut px = &mut *root; // reborrowing from root
*px = 100;
let mut py = &mut *root; // another reborrow. invalidates px
*py = 200;
// *px = 300 // this write is invalid.
\end{minted}

In line 1, we create a box that contains 42 in the heap.
In the following two lines, we reborrow from it and use the reference to write.
The interesting part is line 4. In this line, we create a new reference from \rust{root}.
As this reborrow asserts that \rust{py} is the unique reference to the box,
\rust{px} must be invalidated at this point.
Therefore, if we remove the comment in line 6, the program will perform an invalid write
(thus rustc will reject the program).

Let's execute the program with Unique.
The following command is the translation of the program above without the last commented line.\<close>

definition XY :: com where
  "XY =
    ''root'' ::= Box (Const (VInt 42));;
    ''px'' ::= Reborrow (Var ''root'');;
    *(Var ''px'') ::= Const (VInt 100);;
    ''py'' ::= Reborrow (Var ''root'');;
    *(Var ''py'') ::= Const (VInt 200)"

text \<open>We can let Isabelle compute the program.\<close>

values "{(map \<Gamma> [''root'', ''px'', ''py''], H, c) |
         \<Gamma> H c. (Map.empty, [], XY) \<rightarrow>\<^sup>* (\<Gamma>, H, c)}"

text \<open>The following shows the variable environment and the heap at the end of execution.\<close>

abbreviation \<Gamma>\<^sub>X\<^sub>Y :: gamma where
  "\<Gamma>\<^sub>X\<^sub>Y == [''root'' \<mapsto> Reference 0 1, ''px'' \<mapsto> Reference 0 2, ''py'' \<mapsto> Reference 0 3]"
abbreviation H\<^sub>X\<^sub>Y :: heap where
  "H\<^sub>X\<^sub>Y == [(VInt 200, [1, 3])]"

text \<open>We can also prove that the program result in the state shown above in theory,
but it's really tedious (why can't Isabelle prove it by computing the execution?).
The actual proof is left to the reader.\<close>

lemma final_xy: "(Map.empty, [], XY) \<rightarrow>\<^sup>* (\<Gamma>\<^sub>X\<^sub>Y, H\<^sub>X\<^sub>Y, Skip)"
  sorry \<^marker>\<open>tag important\<close>

text \<open>We show that accessing through \rust{px} after the program will stuck.\<close>

lemma intermediate_xyx: "(Map.empty, [], XY;; *(Var ''px'') ::= Const (VInt 300)) \<rightarrow>\<^sup>*
  (\<Gamma>\<^sub>X\<^sub>Y, H\<^sub>X\<^sub>Y, *(Var ''px'') ::= Const (VInt 300))"
  apply (rule star_trans)
   prefer 2
   apply (rule star_step1)
   apply (rule SeqL)
  apply (rule com_seql_trans)
  apply (rule final_xy)
  done

lemma stuck_xyx: "stuck
   (\<Gamma>\<^sub>X\<^sub>Y, H\<^sub>X\<^sub>Y, *(Var ''px'') ::= Const (VInt 300))"
  apply (simp add: stuck_def)
  apply (rule allI)+
  apply (rule notI)
  apply (rule ComE(1))
   apply (auto)
  done

lemma "\<exists>cfg. (Map.empty, [], XY;; *(Var ''px'') ::= Const (VInt 300)) \<rightarrow>\<^sup>* cfg
           \<and> stuck cfg"
  apply (rule exI)
  apply (rule conjI)
   apply (rule intermediate_xyx)
  apply (rule stuck_xyx)
  done

subsection \<open>Swap\<close>

text \<open>The following program swaps the content the given two references pointing to.\<close>

fun swap :: "exp \<Rightarrow> exp \<Rightarrow> com" where
  "swap x y =
    ''reborrow_x'' ::= Reborrow x;;
    ''reborrow_y'' ::= Reborrow y;;
    ''tmp'' ::= Deref (Var ''reborrow_x'');;
    *(Var ''reborrow_x'') ::= Deref (Var ''reborrow_y'');;
    *(Var ''reborrow_y'') ::= Var ''tmp''"

text \<open>We can see the content swapped during the execution by running it on Isabelle.\<close>

values "{H | \<Gamma> H c. (Map.empty, [], swap (Box (Const (VInt 42))) (Box (Const (VInt 100)))) \<rightarrow>\<^sup>* (\<Gamma>, H, c)}"

text \<open>Proving the correctness of @{const swap} would need a Hoare Logic. The road continues...\<close>

end
