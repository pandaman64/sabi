theory Swap
  imports Simpl.Vcg "Rust-Verification.Rust_Semantics"
begin

record 'a simple_swap_env =
  x :: 'a
  y :: 'a
  tmp :: 'a

definition simple_swap_body
 :: "('a simple_swap_env, 'c, 'd) com"
where
  "simple_swap_body ==
    Basic (\<lambda>s. s\<lparr> tmp := x s \<rparr>);;
    Basic (\<lambda>s. s\<lparr> x := y s \<rparr>);;
    Basic (\<lambda>s. s\<lparr> y := tmp s \<rparr>)"

lemma simple_swap_values: "\<Gamma> \<turnstile>\<^sub>t
  {s. x s = X \<and> y s = Y}
  simple_swap_body
  {s. x s = Y \<and> y s = X}"
  unfolding simple_swap_body_def
  apply vcg
  done

record rustv_swap_env = globals_ram +
  x :: tagged_ref
  y :: tagged_ref
  tmp :: tagged_ref

definition rustv_swap_body where
  "rustv_swap_body ==
    Basic (\<lambda>s. let (r, s') = heap_new uninit s in s'\<lparr> tmp := r \<rparr>);;
    copy_betw_places x tmp;;
    copy_betw_places y x;;
    copy_betw_places tmp y"

lemma rustv_swap_safety: "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s
  \<and> writable (x s) s \<and> writable (y s) s
  \<and> \<not>(ptr_eq (x s) (y s))}
  rustv_swap_body
  {s. True}"
  unfolding rustv_swap_body_def
  apply vcg
  apply (auto simp add: Let_def nth_append)
  using writable_pop_tags by auto

lemma rustv_swap_correctness: "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s
  \<and> writable (x s) s \<and> writable (y s) s
  \<and> \<not>(ptr_eq (x s) (y s))
  \<and> memread (x s) s = X \<and> memread (y s) s = Y}
  rustv_swap_body
  {s. memread (x s) s = Y \<and> memread (y s) s = X}"
  unfolding rustv_swap_body_def
  apply vcg
  apply (auto simp add: Let_def nth_append)
  using writable_pop_tags by auto

lemma rustv_swap_values_overlapping: "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s
  \<and> writable (x s) s \<and> writable (y s) s
  \<and> (ptr_eq (x s) (y s))
  \<and> memread (x s) s = X \<and> memread (y s) s = Y}
  rustv_swap_body
  {s. memread (x s) s = Y \<and> memread (y s) s = X}"
  unfolding rustv_swap_body_def
  apply vcg
  apply (auto simp add: Let_def nth_append)
  using writable_pop_tags apply auto
  oops

lemma rustv_swap_safety': "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s
  \<and> writable (x s) s \<and> writable (y s) s
  \<and> ptr_eq (x s) (y s)
  \<and> in_same_layer (tag (x s)) (tag (y s)) (tags s ! (the_ptr (pointer (x s))))}
  rustv_swap_body
  {s. True}"
  unfolding rustv_swap_body_def
  apply vcg
  apply (auto simp add: Let_def nth_append)
  (* sledgehammer *)
  using writable_pop_tags apply auto[1]
  apply (simp_all only: wf_tags_in_same_layer_dropWhile)
  (* sledgehammer *)
   apply (metis UnE in_same_layer_same_pos nth_mem set_append set_takeWhileD takeWhile_dropWhile_id)
  (* sledgehammer *)
  using writable_pop_tags by auto

end