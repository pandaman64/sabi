theory Unique
  imports Main Definitions Exp Star
begin

section \<open>Semantics of Commands\<close>

text \<open>This section describes the small-step semantics of commands.
The configuration of an execution consists of:
\<^item> the variable environment $\Gamma$ (of type @{type gamma});
\<^item> the heap $H$ (of type @{type heap}) which holds the actual data and the reborrow trees
  for each address; and
\<^item> the command to be executed $c$ (of type @{type com}).
\<close>

type_synonym config = "tags * heap * com"
inductive com_sem :: "gamma \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_ \<turnstile> _ \<rightarrow> _)")
where
  Assign: "\<lbrakk>\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refs, Reference a t); list_all (writable H) refs; writable H (a, t);
            H' = kill_all refs H; (\<Gamma>, T, H', rv) \<Down> (T', H'', v); H'' ! a = (_, ts)\<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> (T, H, p ::= rv) \<rightarrow> (T', H''[a := (v, kill t ts)], Skip)" |
  SeqL: "\<Gamma> \<turnstile> (T, H, Skip;; c) \<rightarrow> (T, H, c)" |
  SeqR: "\<Gamma> \<turnstile> (T, H, c1) \<rightarrow> (T', H', c') \<Longrightarrow> \<Gamma> \<turnstile> (T, H, c1;; c2) \<rightarrow> (T', H', c';; c2)" |
  IfTrue: "(\<Gamma>, T, H, b) \<Down> (T', H', VBool True)
           \<Longrightarrow> \<Gamma> \<turnstile> (T, H, IF b THEN c1 ELSE c2) \<rightarrow> (T', H', c1)" |
  IfFalse: "(\<Gamma>, T, H, b) \<Down> (T', H', VBool False)
           \<Longrightarrow> \<Gamma> \<turnstile> (T, H, IF b THEN c1 ELSE c2) \<rightarrow> (T', H', c2)" |
  While: "\<Gamma> \<turnstile> (T, H, WHILE b DO c) \<rightarrow> (T, H, IF b THEN (c;; WHILE b DO c) ELSE Skip)"

(*<*)
lemmas com_sem_cases = com_sem.cases[split_format(complete)]
lemmas com_sem_induct = com_sem.induct[split_format(complete)]
declare com_sem.intros[simp, intro]

(* We declare safe elimination rules (automatically applied I guess?) *)
inductive_cases ComE[elim!]:
  "\<Gamma> \<turnstile> (T, H, x ::= e) \<rightarrow> cfg"
  "\<Gamma> \<turnstile> (T, H, Skip;; c) \<rightarrow> cfg"
  "\<Gamma> \<turnstile> (T, H, c1;; c2) \<rightarrow> cfg"
  "\<Gamma> \<turnstile> (T, H, IF b THEN c1 ELSE c2) \<rightarrow> cfg"

(* WHILE might not terminate, so we declare it as an unsafe elimination rule *)
inductive_cases WhileE[elim]: "\<Gamma> \<turnstile> (T, H, WHILE b DO c) \<rightarrow> cfg"
(*>*)

abbreviation com_sem_steps :: "gamma \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_ \<turnstile> _ \<rightarrow>\<^sup>* _)") where
  "\<Gamma> \<turnstile> cfg \<rightarrow>\<^sup>* cfg' == star (com_sem \<Gamma>) cfg cfg'"

text \<open>
Figure \ref{fig:com} shows the assignment rules. Other commands are standard.

The {\sc{Assign}} rule assigns a value to the the location.
To assign through a reference, the reference must be valid for writes.
Moreover, the write is considered as a use of the reference; it will invalidate the child references.

\begin{figure}[h]
\centering
\begin{framed}
@{thm[mode=Rule] Assign} \sc{Assign}
\end{framed}
\caption{The assignment rule}
\label{fig:com}
\end{figure}
\<close>

text \<open>The following lemmas show that the execution of the commands is deterministic.\<close>

definition final :: "config \<Rightarrow> bool" where
  "final cfg \<longleftrightarrow> (case cfg of (_, _, Skip) \<Rightarrow> True | _ \<Rightarrow> False)"

definition stuck :: "gamma \<Rightarrow> config \<Rightarrow> bool" where
  "stuck \<Gamma> cfg \<longleftrightarrow> (case cfg of
     (_, _, Skip) \<Rightarrow> False |
     _ \<Rightarrow> \<not>(\<exists>cfg'. (\<Gamma> \<turnstile> cfg \<rightarrow> cfg')))"

lemma skip_final_noteq[simp]: "\<Gamma> \<turnstile> (T, H, c) \<rightarrow> (T, H', c') \<Longrightarrow> c \<noteq> Skip"
proof (cases rule: com_sem_cases)
qed auto

lemma skip_final[simp]: "\<Gamma> \<turnstile> (T, H, Skip) \<rightarrow> (T', H', c) \<Longrightarrow> False"
proof (cases \<Gamma> "(T, H, Skip)" "(T', H', c)" rule: com_sem_cases)
qed auto

lemma com_sem_det: "\<Gamma> \<turnstile> cfg \<rightarrow> cfg' \<Longrightarrow> \<Gamma> \<turnstile> cfg \<rightarrow> cfg'' \<Longrightarrow> cfg'' = cfg'"
proof (induction arbitrary: cfg'' rule: com_sem.induct)
  case (Assign \<Gamma> H p refs a t H' T rv T' H'' v uu ts)
  show ?case
  proof (rule ComE(1))
    show "\<Gamma> \<turnstile> (T, H, p ::= rv) \<rightarrow> cfg''" using Assign.prems by simp
  next
    fix refsa aa ta T'a H''a va uuu tsa

    assume "\<Gamma>; H \<turnstile> p \<Down>\<^sub>p (refsa, Reference aa ta)"
    then have "refsa = refs \<and> aa = a \<and> ta = t" using Assign.hyps place_sem_det' by blast
    then have refs: "refsa = refs" and "aa = a" and "ta = t" by auto

    moreover
    assume "(\<Gamma>, T, kill_all refsa H, rv) \<Down> (T'a, H''a, va)"
    then have "(\<Gamma>, T, H', rv) \<Down> (T'a, H''a, va)" using Assign.hyps refs by simp
    then have "T'a = T' \<and> H''a = H'' \<and> va = v" using Assign.hyps rvalue_sem_det by blast
    then have "T'a = T'" and "H''a = H''" and "va = v" by auto

    moreover
    assume "H''a ! aa = (uuu, tsa)"
    then have "tsa = ts" using \<open>H''a = H''\<close> \<open>aa = a\<close> Assign.hyps by auto

    moreover
    assume "cfg'' = (T'a, H''a[aa := (va, kill ta tsa)], Skip)"
    then show ?thesis using calculation by auto
  qed
next
  case (SeqL \<Gamma> T H c)
  then show ?case
    by (meson ComE(3) skip_final)
next
  case (SeqR \<Gamma> T H c1 T' H' c' c2)
  then show ?case
    by (metis ComE(3) old.prod.inject skip_final)
next
  case (IfTrue \<Gamma> T H b T' H' c1 c2)
  show ?case
  proof (rule ComE(4))
    show "\<Gamma> \<turnstile> (T, H, IF b THEN c1 ELSE c2) \<rightarrow> cfg''" using IfTrue.prems by simp
  next
    fix T'a H'a
    assume "(\<Gamma>, T, H, b) \<Down> (T'a, H'a, VBool True)"
    then have "T'a = T'" and "H'a = H'" using rvalue_sem_det IfTrue.hyps by auto

    assume "cfg'' = (T'a, H'a, c1)"
    thus ?thesis using \<open>T'a = T'\<close> \<open>H'a = H'\<close> by simp
  next
    fix T'a H'a
    assume "(\<Gamma>, T, H, b) \<Down> (T'a, H'a, VBool False)"
    then have False using rvalue_sem_det IfTrue.hyps by blast
    thus ?thesis by simp
  qed
next
  case (IfFalse \<Gamma> T H b T' H' c1 c2)
  show ?case
  proof (rule ComE(4))
    show "\<Gamma> \<turnstile> (T, H, IF b THEN c1 ELSE c2) \<rightarrow> cfg''" using IfFalse.prems by simp
  next
    fix T'a H'a
    assume "(\<Gamma>, T, H, b) \<Down> (T'a, H'a, VBool False)"
    then have "T'a = T'" and "H'a = H'" using rvalue_sem_det IfFalse.hyps by auto

    assume "cfg'' = (T'a, H'a, c2)"
    thus ?thesis using \<open>T'a = T'\<close> \<open>H'a = H'\<close> by simp
  next
    fix T'a H'a
    assume "(\<Gamma>, T, H, b) \<Down> (T'a, H'a, VBool True)"
    then have False using rvalue_sem_det IfFalse.hyps by blast
    thus ?thesis by simp
  qed
next
  case (While \<Gamma> T H b c)
  then show ?case by auto
qed

lemmas star_induct' = star.induct[of "com_sem \<Gamma>", split_format(complete)] \<^marker>\<open>tag invisible\<close>

text \<open>We show the transitivity of @{const com_sem_steps}.\<close>

lemma com_seql_trans:
  "\<Gamma> \<turnstile> (T, H, c1) \<rightarrow>\<^sup>* (T', H', c1') \<Longrightarrow> \<Gamma> \<turnstile> (T, H, c1;; c2) \<rightarrow>\<^sup>* (T', H', c1';; c2)"
proof (induction rule: star_induct')
  case (refl a a b)
  then show ?case by simp
next
  case (step a a b a a b a a b)
  then show ?case by (meson SeqR star.simps)
qed

section \<open>Code examples\<close>

text \<open>We need to assign a pre-allocated location to each variable to run a program.
Currently we initialize those locations with zeros, but they will be uninitialized when we implement
uninitialized slots.\<close>

abbreviation "\<Gamma>\<^sub>0 == \<lambda>_. undefined"
fun preallocate' :: "vname list \<Rightarrow> gamma * tags * heap \<Rightarrow> gamma * tags * heap" where
  "preallocate' [] ret = ret" |
  "preallocate' (x # xs) (\<Gamma>, T, H) =
    (let t = length T in
     let \<Gamma>' = \<Gamma>(x := (t, t)) in
     let T' = T @ [Unique] in
     let H' = H @ [(VInt 0, [t])] in
     preallocate' xs (\<Gamma>', T', H'))"
fun preallocate :: "vname list \<Rightarrow> gamma * tags * heap" where
  "preallocate xs = preallocate' xs (\<Gamma>\<^sub>0, [], [])"

value "preallocate [''x'', ''y'']"
value "map (fst (preallocate [''x'', ''y''])) [''x'', ''y'']"

fun prealloc_com_sem :: "vname list \<Rightarrow> com \<Rightarrow> config \<Rightarrow> bool"
  ("(_; _ \<rightarrow>\<^sup>* _)") where
  "(xs; c \<rightarrow>\<^sup>* cfg) =
   (let (\<Gamma>, T, H) = preallocate xs in (\<Gamma> \<turnstile> (T, H, c) \<rightarrow>\<^sup>* cfg))"

text \<open>Let Isabelle run Unique programs by generating code for the semantics.\<close>

code_pred [show_modes] place_sem .
code_pred [show_modes] operand_sem .
code_pred [show_modes] rvalue_sem .
code_pred [show_modes] com_sem .

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
    (Var ''root'') ::= (Use \<circ> Constant \<circ> VInt) 42;;
    (Var ''px'') ::= (Reborrow \<circ> Var) ''root'';;
    ((Deref \<circ> Var) ''px'') ::= (Use \<circ> Constant \<circ> VInt) 100;;
    (Var ''py'') ::= (Reborrow \<circ> Var) ''root'';;
    ((Deref \<circ> Var) ''py'') ::= (Use \<circ> Constant \<circ> VInt) 200"

text \<open>We can let Isabelle compute the program.\<close>

value "preallocate [''root'', ''px'', ''py'']"
abbreviation "\<Gamma> == \<Gamma>\<^sub>0(''root'' := (0, 0), ''px'' := (1, 1), ''py'' := (2, 2))"
abbreviation "T == [Unique, Unique, Unique]"
abbreviation "H == [(VInt 0, [0]), (VInt 0, [1]), (VInt 0, [2])]"
lemma "preallocate [''root'', ''px'', ''py''] = (\<Gamma>, T, H)" by auto

values "{(T', H') |
         T' H' c'. \<Gamma> \<turnstile> (T, H, XY) \<rightarrow>\<^sup>* (T', H', c')}"

text \<open>The following shows the tags and the heap at the end of execution.\<close>

abbreviation T\<^sub>X\<^sub>Y :: tags where
  "T\<^sub>X\<^sub>Y == [Unique, Unique, Unique, Unique, Unique]" (* 5 variables + 2 reborrows *)
abbreviation H\<^sub>X\<^sub>Y :: heap where
  "H\<^sub>X\<^sub>Y == [(VInt 200, [0, 4]), (Reference 0 3, [1]), (Reference 0 4, [2])]"

text \<open>We can also prove that the program result in the state shown above in theory,
but it's really tedious (why can't Isabelle prove it by computing the execution?).
The actual proof is left to the reader.\<close>

lemma final_xy: "\<Gamma> \<turnstile> (T, H, XY) \<rightarrow>\<^sup>* (T\<^sub>X\<^sub>Y, H\<^sub>X\<^sub>Y, Skip)"
  sorry \<^marker>\<open>tag important\<close>

text \<open>We show that accessing through \rust{px} after the program will stuck.\<close>

lemma intermediate_xyx: "\<Gamma> \<turnstile> (T, H, XY;; ((Deref \<circ> Var) ''px'') ::= (Use \<circ> Constant \<circ> VInt) 300)
  \<rightarrow>\<^sup>* (T\<^sub>X\<^sub>Y, H\<^sub>X\<^sub>Y, ((Deref \<circ> Var) ''px'') ::= (Use \<circ> Constant \<circ> VInt) 300)"
  apply (rule star_trans)
   prefer 2
   apply (rule star_step1)
   apply (rule SeqL)
  apply (rule com_seql_trans)
  apply (rule final_xy)
  done

lemma stuck_xyx: "stuck \<Gamma>
   (T\<^sub>X\<^sub>Y, H\<^sub>X\<^sub>Y, ((Deref \<circ> Var) ''px'') ::= (Use \<circ> Constant \<circ> VInt) 300)"
  apply (simp add: stuck_def)
  apply (rule allI)+
  apply (rule notI)
  apply (rule ComE(1))
   apply (auto)
  done

lemma "\<exists>cfg. (\<Gamma> \<turnstile> (T, H, XY;; ((Deref \<circ> Var) ''px'') ::= (Use \<circ> Constant \<circ> VInt) 300) \<rightarrow>\<^sup>* cfg)
           \<and> stuck \<Gamma> cfg"
  apply (rule exI)
  apply (rule conjI)
   apply (rule intermediate_xyx)
  apply (rule stuck_xyx)
  done

subsection \<open>Swap\<close>

text \<open>The following program swaps the content the given two references pointing to.\<close>

fun swap :: "place \<Rightarrow> place \<Rightarrow> com" where
  "swap x y =
    (Var ''reborrow_x'') ::= Reborrow x;;
    (Var ''reborrow_y'') ::= Reborrow y;;
    (Var ''tmp'') ::= (Use \<circ> Place \<circ> Deref \<circ> Deref \<circ> Var) ''reborrow_x'';;
    ((Deref \<circ> Var) ''reborrow_x'') ::= (Use \<circ> Place \<circ> Deref \<circ> Deref \<circ> Var) ''reborrow_y'';;
    ((Deref \<circ> Var) ''reborrow_y'') ::= (Use \<circ> Place \<circ> Deref \<circ> Deref \<circ> Var) ''tmp''"

text \<open>We can see the content swapped during the execution by running it on Isabelle.\<close>

values "{H | T H c.
  \<Gamma>\<^sub>0(''reborrow_x'' := (0, 0), ''reborrow_y'' := (1, 1), ''tmp'' := (2, 2), ''a'' := (3, 3), ''b'' := (4, 4)) \<turnstile>
  ([Unique, Unique, Unique],
   [(VInt 0, [0]), (VInt 0, [1]), (VInt 0, [2]), (VInt 10000, [3]), (VInt 20000, [4])],
   swap (Var ''a'') (Var ''b'')) \<rightarrow>\<^sup>* (T, H, c)}"

text \<open>Proving the correctness of @{const swap} would need a Hoare Logic. The road continues...\<close>

end
