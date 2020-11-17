theory No_Alias_Precise
  imports Simpl.Vcg "Rust-Verification.Rust_Semantics"
begin

record no_alias_env = globals_ram +
  x :: "rust_integer typed_ref" (* locals are represented by owning reference *)
  ref1 :: "(rust_integer typed_ref) typed_ref"
  ref2 :: "(rust_integer typed_ref) typed_ref"

definition no_alias_body :: "(no_alias_env, 'p, rust_error) com" where
  "no_alias_body ==
    Basic (\<lambda>s. (let (r, s') = heap_new (int_val 100) s in s'\<lparr> x := typed r \<rparr>));;
    Basic (\<lambda>s. (let (r, s') = heap_new uninit s in s'\<lparr> ref1 := typed r \<rparr>));;
    Basic (\<lambda>s. (let (r, s') = heap_new uninit s in s'\<lparr> ref2 := typed r \<rparr>));;

    reborrow_typed Unique x ref1;;
    write_imm_typed ref1 (int_val 200);;

    reborrow_typed Unique x ref2;;
    write_imm_typed ref2 (int_val 300)"

lemma suc_len_access[simp]: "length ys \<ge> 2 \<Longrightarrow> (xs @ ys) ! Suc (length xs) = ys ! 1"
  by (metis Suc_eq_plus1 nth_append_length_plus)
lemma suc2_len_access[simp]: "length ys \<ge> 3 \<Longrightarrow> (xs @ ys) ! Suc (Suc (length xs)) = ys ! 2"
  by (metis add_2_eq_Suc' nth_append_length_plus)

(* Termination, by full VCG *)
lemma "\<Gamma> \<turnstile>\<^sub>t {s. wf_heap s} no_alias_body {s. True}"
  unfolding no_alias_body_def
  apply vcg
  apply (auto simp: Let_def)
  done

(* Spec of the program *)

(*
lemma "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s}
  no_alias_body
  {s. (let p = the_ptr (pointer (untyped (x s))) in
      memory s ! p = int_val 300) \<and>
      writable (untyped (x s)) s \<and> \<not>writable (untyped (ref1 s)) s \<and> writable (untyped (ref2 s)) s}"
  unfolding no_alias_body_def
  apply vcg
  (* This auto takes too long because of the term size *)
  apply (simp add: Let_def)
  oops
*)

end