theory No_Alias
  imports Simpl.Vcg "Rust-Verification.Rust_Semantics"
begin

record no_alias_env = globals_ram +
  x :: tagged_ref (* locals are represented by owning reference *)
  ref1 :: tagged_ref
  ref2 :: tagged_ref

definition no_alias_body :: "(no_alias_env, 'p, rust_error) com" where
  "no_alias_body ==
    Basic (\<lambda>s. (let (r, s') = heap_new (int_val 100) s in s'\<lparr> x := r \<rparr>));;

    reborrow_stmt Unique x (\<lambda>s r. s\<lparr> ref1 := r \<rparr>);;
    write_imm ref1 (int_val 200);;

    reborrow_stmt Unique x (\<lambda>s r. s\<lparr> ref2 := r \<rparr>);;
    write_imm ref2 (int_val 300)"

(* Termination *)
lemma "\<Gamma> \<turnstile>\<^sub>t {s. wf_heap s} no_alias_body {s. True}"
  unfolding no_alias_body_def
  apply vcg_step
       prefer 2
       apply vcg_step
       apply vcg_step
      apply vcg_step
     apply vcg_step
      prefer 2
      apply vcg_step
      apply vcg_step
     apply vcg_step
    apply vcg_step
     prefer 2
     apply vcg_step
     apply vcg_step
    apply vcg_step
   apply vcg_step
    prefer 2
    apply vcg_step
    apply vcg_step
   apply vcg_step
  apply vcg_step
  apply vcg_step
  by (simp add: Let_def)

(* Termination, by full VCG *)
lemma "\<Gamma> \<turnstile>\<^sub>t {s. wf_heap s} no_alias_body {s. True}"
  unfolding no_alias_body_def
  apply vcg
  by (auto simp: Let_def)

(* Spec of the program *)
lemma "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s}
  no_alias_body
  {s. (let p = the_ptr (pointer (x s)) in
      memory s ! p = int_val 300) \<and>
      writable (x s) s \<and> \<not>writable (ref1 s) s \<and> writable (ref2 s) s}"
  unfolding no_alias_body_def
  apply vcg
  (* This auto takes too long because of the term size *)
  by (auto simp: Let_def)

end