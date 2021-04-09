theory Assume
  imports Simpl.Vcg "Rust-Verification.Rust_Semantics"
begin

(* In this theory, we explore the applicability of the technique proposed in [Flanagan and Saxe 2001]
 * to Simpl's Hoare logic.
 *)

(* First, we look at the definition of the validity of the Hoare triple with respect to partial correctness:
 * ?\<Gamma>\<Turnstile>\<^bsub>/?F\<^esub> ?P ?c ?Q,?A \<equiv>
 * \<forall>s t. ?\<Gamma>\<turnstile> \<langle>?c,s\<rangle> \<Rightarrow> t \<longrightarrow> s \<in> Normal ` ?P \<longrightarrow> t \<notin> Fault ` ?F \<longrightarrow> t \<in> Normal ` ?Q \<union> Abrupt ` ?A
 *
 * Assuming the Hoare triple is valid, if the program starts from a state in set P, then the
 * execution results in one of the following cases:
 * 1. It fail with a fault which is in the set F;
 * 2. It terminates normally, and the resulting state is in the set Q; or
 * 3. It terminates abruptly (due to an exception, etc), and the resulting state is in the set A.
 * Note that the program can fail with some f in F. Intuitively, F represents the failures that is
 * known to not happen. For more detail, see Def 3.1 in Schirmer's PhD thesis.
 *
 * Since Schirmer already proved the soundness and the completeness of the Hoare logic, we can
 * identify the Hoare rules and the validity.
 *)
thm HoarePartialDef.valid_def

(* For total correctness, we have the following validity predicate:
 * ?\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/?F\<^esub> ?P ?c ?Q,?A \<equiv> ?\<Gamma>\<Turnstile>\<^bsub>/?F\<^esub> ?P ?c ?Q,?A \<and> (\<forall>s\<in>Normal ` ?P. ?\<Gamma>\<turnstile>?c \<down> s)
 *
 * It says that the Hoare triple is valid with respect to partial correctness and the program
 * terminates (including run-time faults) for all inputs. The down arrow symbol indicates "guaranteed"
 * termination which states that the program terminates even in the presence of non-determinism.
 *)
thm HoareTotalDef.validt_def

(* It looks like the key ingredient of the Flanagan and Saxe's method is the assume command.
 * Informally, `assume e` states that the program state must satisfy e, otherwise the execution is
 * "blocked" (this term is used in [Leino 2005]), which means the program does not run at all.
 * The assume command is different from assert command (or guard command in Simpl) in the sense that
 * we can assume the validity of the predicate without interfering the program state or the execution.
 *
 * We represent the assume command using the following ASSUME command with the help of the special
 * failure set named faults.
 *)
datatype faults = assumed | fault
abbreviation ASSUME where
  "ASSUME X == Guard assumed X Skip"

(* Example *)
record env =
  a :: int
(* Since the failure set contains `assumed`, the Hoare triple assumes that `assumes` must not occur.
 * Therefore, the ASSUME command states that we can assume that A = 10 holds.
 *)
lemma "\<Gamma> \<turnstile>\<^sub>t\<^bsub>/{assumed}\<^esub>
  {s. a s \<noteq> 10}
  ASSUME {s. a s = 10}
  Q"
  apply vcg
  by auto

(* The proof above use the following Guarantee rule during the verification condition generation:
 *
 * \<lbrakk>?P \<subseteq> {s. s \<in> ?g \<longrightarrow> s \<in> ?R}; ?\<Gamma>,?\<Theta>\<turnstile>\<^bsub>/?F \<^esub>?R ?c ?Q,?A; ?f \<in> ?F\<rbrakk> \<Longrightarrow>
 * ?f \<in> ?F \<Longrightarrow> ?\<Gamma>,?\<Theta>\<turnstile>\<^bsub>/?F \<^esub>?P Guard ?f ?g ?c ?Q,?A
 *)
thm HoarePartial.Guarantee

(* We can derive the following Hoare rule which seems to correspond to the one shown in [Flanagan and Saxe 2001],
 * where they have:
 * wp.(assume e).Q = e \<longrightarrow> Q.
 *)
lemma Assume:
  "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{assumed}\<^esub> {s. s \<in> X \<longrightarrow> s \<in> Q} (ASSUME X) Q, A"
proof -
  have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{assumed}\<^esub> Q SKIP Q,A"
    by (meson hoarep.Skip)
  then show ?thesis
  using HoarePartial.Guarantee by fastforce
qed

end