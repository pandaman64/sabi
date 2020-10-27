theory Write
  imports Simpl.Vcg "Rust-Verification.Rust_Semantics"
begin

record deriv_env = globals_ram +
  p :: tagged_ref
  x :: tagged_ref

definition deriv_body :: "(deriv_env, 'p, rust_error) com" where
  "deriv_body = write_imm p (int_val 101)"

lemma partial: "\<Gamma> \<turnstile> {s. writable (p s) s} deriv_body {s. memory s ! (the_ptr (pointer (p s))) = int_val 101}"
  unfolding deriv_body_def
  apply (hoare_rule HoarePartial.Guard)
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (simp add: Let_def)
  by auto

lemma "\<Gamma> \<turnstile>\<^sub>t {s. writable (p s) s} deriv_body {s. memory s ! (the_ptr (pointer (p s))) = int_val 101}"
  unfolding deriv_body_def
  apply (hoare_rule HoareTotal.Guard)
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (simp add: Let_def)
  by auto

lemma "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^sub>t
  {s. s = \<sigma> \<and> writable (p s) s}
  deriv_body
  {s. memory s = (memory \<sigma>)[the_ptr (pointer (p \<sigma>)) := int_val 101]}"
  unfolding deriv_body_def
  apply (hoare_rule HoareTotal.Guard)
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (simp add: Let_def)
  by auto

lemma "\<Gamma> \<turnstile>\<^sub>t {s. writable (p s) s \<and> wf_heap s} deriv_body {s. writable (p s) s}"
  unfolding deriv_body_def
  apply vcg_step
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (auto simp add: Let_def)
  using writable_pop_tags by auto

definition reb_body :: "(deriv_env, 'p, rust_error) com" where
  "reb_body = reborrow_stmt Unique p (\<lambda>s r. s\<lparr> x := r \<rparr>)"

lemma "\<Gamma> \<turnstile>\<^sub>t
  {s. writable (p s) s \<and> wf_heap s}
  reb_body
  {s. writable (x s) s}"
  unfolding reb_body_def
  apply vcg
  apply (auto simp add: Let_def)
  apply (rule writable_reborrow_comp_derived, simp_all)
  using wf_tags_spec by auto

end
