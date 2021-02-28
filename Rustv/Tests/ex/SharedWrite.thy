theory SharedWrite
  imports Simpl.Vcg "Rust-Verification.Rust_Semantics"
begin

text \<open>In this section, we explore how we can express shared read write references (raw pointers)
in this framework.\<close>

text \<open>Consider the following Rust program:

fn main() {
  let root = &mut 100;

  let ptr1 = root as *mut i32;
  let ptr2 = ptr1;

  unsafe {
    *ptr1 = 200;
    *ptr2 = 300;
    *ptr1 = 400;
  }
}

Since the raw pointers occupy the same slot of the borrow stack,
they do not invalidate each other. Therefore, the program is valid.

We formulate this program using Isabelle/Simpl below.
\<close>

record shared_env = globals_ram +
  root :: tagged_ref
  ptr1 :: tagged_ref
  ptr2 :: tagged_ref

definition shared_body :: "(shared_env, 'p, rust_error) com" where
  "shared_body ==
    Basic (\<lambda>s. (let (r, s') = heap_new (int_val 100) s in s'\<lparr> root := r \<rparr>));;

    reborrow_stmt SharedReadWrite root (\<lambda>s r. s\<lparr> ptr1 := r \<rparr>);;
    reborrow_stmt SharedReadWrite ptr1 (\<lambda>s r. s\<lparr> ptr2 := r \<rparr>);;

    write_imm ptr1 (int_val 200);;
    write_imm ptr2 (int_val 300);;
    write_imm ptr1 (int_val 400)"

text \<open>Proof of safety (the program doesn't stuck due to alias semantics violation)\<close>

lemma "\<Gamma> \<turnstile>\<^sub>t {s. wf_heap s} shared_body {s. True}"
  unfolding shared_body_def
  apply vcg
  by (auto simp add: Let_def)

lemma "\<Gamma> \<turnstile>\<^sub>t {s. wf_heap s} shared_body {s. wf_heap s}"
  unfolding shared_body_def
  apply vcg
  by (auto simp add: Let_def wf_tags_spec)

lemma "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s}
  shared_body
  {s. memory s ! (the_ptr (pointer (root s))) = int_val 400 \<and>
    writable (root s) s \<and>
    writable (ptr1 s) s \<and>
    writable (ptr2 s) s}"
  unfolding shared_body_def
  apply vcg
  by (auto simp add: Let_def)

end