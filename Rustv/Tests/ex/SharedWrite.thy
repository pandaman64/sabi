theory SharedWrite
  imports "Rust-Verification.Rustv"
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
    *ptr1 = 200;
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
  "shared_body =
    (Seq (Basic (\<lambda>s. (let (r, s') = heap_new (int_val 100) s in
                     s'\<lparr> root := r \<rparr>)))

    (Seq (Guard invalid_ref {s. writable (root s) s}
           (Seq (Basic (\<lambda>s. pop_tags (root s) s))
                (Basic (\<lambda>s.
                  (let (r, s') = reborrow SharedReadWrite (root s) s in
                  s'\<lparr> ptr1 := r \<rparr>)))))
    (Seq (Guard invalid_ref {s. writable (ptr1 s) s}
           (Seq (Basic (\<lambda>s. pop_tags (ptr1 s) s))
                (Basic (\<lambda>s.
                  (let (r, s') = reborrow SharedReadWrite (ptr1 s) s in
                  s'\<lparr> ptr2 := r \<rparr>)))))

    (Seq (Guard invalid_ref {s. writable (ptr1 s) s}
           (Seq (Basic (\<lambda>s. pop_tags (ptr1 s) s))
                (Basic (\<lambda>s. memwrite (ptr1 s) (int_val 200) s))))
    (Seq (Guard invalid_ref {s. writable (ptr2 s) s}
           (Seq (Basic (\<lambda>s. pop_tags (ptr2 s) s))
                (Basic (\<lambda>s. memwrite (ptr2 s) (int_val 300) s))))
         (Guard invalid_ref {s. writable (ptr1 s) s}
           (Seq (Basic (\<lambda>s. pop_tags (ptr1 s) s))
                (Basic (\<lambda>s. memwrite (ptr1 s) (int_val 200) s))))
    )))))"

text \<open>Proof of safety (the program doesn't stuck due to alias semantics violation)\<close>

lemma "\<Gamma> \<turnstile>\<^sub>t {s. wf_heap s} shared_body {s. True}"
  unfolding shared_body_def
  apply vcg
  by (auto simp add: Let_def wf_tags_spec)

lemma "\<Gamma> \<turnstile>\<^sub>t {s. wf_heap s} shared_body {s. wf_heap s}"
  unfolding shared_body_def
  apply vcg
  apply (auto simp add: Let_def wf_tags_spec)
  apply (rule ReborrowSRWSRW, auto)
  by (rule ReborrowUniqueSRW, auto)

end