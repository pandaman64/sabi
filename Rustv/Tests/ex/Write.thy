theory Write
  imports "Rust-Verification.Rustv"
begin

record deriv_env = globals_ram +
  p :: tagged_ref
  x :: tagged_ref

definition deriv_body :: "(deriv_env, 'p, rust_error) com" where
  "deriv_body = Guard invalid_ref {s. writable (p s) s}
    (Seq (Basic (\<lambda>s. invalidate_children (p s) s))
         (Basic (\<lambda>s. (memwrite (p s) (int_val 101) s))))"

lemma partial: "\<Gamma> \<turnstile> {s. writable (p s) s} deriv_body {s. memory s ! (Rep_ref (pointer (p s))) = int_val 101}"
  unfolding deriv_body_def
  apply (hoare_rule HoarePartial.Guard)
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (simp add: Let_def)
  by auto

lemma "\<Gamma> \<turnstile>\<^sub>t {s. writable (p s) s} deriv_body {s. memory s ! (Rep_ref (pointer (p s))) = int_val 101}"
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
  {s. memory s = (memory \<sigma>)[Rep_ref (pointer (p \<sigma>)) := int_val 101]}"
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
  by (auto simp add: Let_def)

definition reb_body :: "(deriv_env, 'p, rust_error) com" where
  "reb_body = Guard invalid_ref {s. writable (p s) s}
    (Seq (Basic (\<lambda>s. invalidate_children (p s) s))
         (Basic (\<lambda>s.
           (let (p', s') = reborrow (p s) s in
           s'\<lparr> x := p' \<rparr>))))"

lemma "\<Gamma> \<turnstile>\<^sub>t
  {s. writable (p s) s \<and> wf_heap s}
  reb_body
  {s. writable (x s) s}"
  unfolding reb_body_def
  apply vcg_step
   prefer 2
   apply vcg_step
   apply vcg_step
  apply (simp add: Let_def)
  by auto

end