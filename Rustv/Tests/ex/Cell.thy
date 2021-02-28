theory Cell
  imports Simpl.Vcg "Rust-Verification.Rust_Semantics"
begin

text \<open>Formalization of Cell<T>. In this theory, we interpret &Cell<T> as
a SharedReadWrite pointer to the location.\<close>

record cell_env = globals_ram +
  self :: tagged_ref
  return :: tagged_ref

record cell_set_env = cell_env +
  val :: tagged_ref

record cell_swap_env = cell_env +
  other :: tagged_ref
  tmp :: tagged_ref \<comment> \<open>inlining local variable for ptr::swap\<close>

(* TODO: Current definition demands only read grant of argument, but it should be owner grant
 * because Cell::set moves the argument.
 *)
definition cell_set_body :: "(cell_set_env, 'p, rust_error) com" where
  "cell_set_body == copy_betw_places val self"

(* TODO: We need to define a "calling convention" for handling arguments/return value.
 *)
definition cell_get_body :: "(cell_env, 'p, rust_error) com" where
  "cell_get_body == copy_betw_places self return"

text \<open>The implementation of Cell::swap is basically along the following lines
(inlining ptr::swap):

``` rust
if ptr::eq(self, other) {
  return
}

let tmp = uninit();
*tmp = *self;
*self = *other;
*other = *tmp;
```

according to \<^url>\<open>https://doc.rust-lang.org/src/core/cell.rs.html#364-375\<close> and
\<^url>\<open>https://doc.rust-lang.org/src/core/ptr/mod.rs.html#373-388\<close>.
\<close>

definition cell_swap_body :: "(cell_swap_env, 'p, rust_error) com" where
  "cell_swap_body ==
    IFR {s. ptr_eq (self s) (other s)}
    THEN
      Skip
    ELSE
      \<comment> \<open>Initializing tmp with uninit\<close>
      Basic (\<lambda>s. (let (r, s') = heap_new uninit s in s'\<lparr> tmp := r \<rparr>));;

      \<comment> \<open>*tmp = *self\<close>
      copy_betw_places self tmp;;
      \<comment> \<open>*self = *other\<close>
      copy_betw_places other self;;
      \<comment> \<open>*self = *tmp\<close>
      copy_betw_places tmp other
    FI
"

lemma cell_set_value_safety: "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s
  \<and> permission_is SharedReadWrite (self s) s
  \<and> readable (val s) s}
  cell_set_body
  {s. True}"
  unfolding cell_set_body_def
  apply vcg
  by (auto simp add: Let_def)

\<comment> \<open>A proof that shows self and val have the same value after Cell::set.\<close>
lemma cell_set_value: "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s
  \<and> permission_is SharedReadWrite (self s) s
  \<and> readable (val s) s}
  cell_set_body
  {s. memread (self s) s = memread (val s) s}"
  unfolding cell_set_body_def
  apply vcg
  apply (auto simp add: Let_def)
  by (metis nth_list_update_eq nth_list_update_neq)

lemma cell_get_value_safety: "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s
  \<and> permission_is SharedReadWrite (self s) s
  \<and> writable (return s) s}
  cell_get_body
  {s. True}"
  unfolding cell_get_body_def
  apply vcg
  by (auto simp add: Let_def)

\<comment> \<open>A proof that shows self and return have the same value after Cell::get.\<close>
lemma cell_get_value: "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s
  \<and> permission_is SharedReadWrite (self s) s
  \<and> writable (return s) s}
  cell_get_body
  {s. memread (self s) s = memread (return s) s}"
  unfolding cell_get_body_def
  apply vcg
  apply (auto simp add: Let_def)
  by (metis nth_list_update_eq nth_list_update_neq)

lemma cell_swap_safety: "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s
  \<and> permission_is SharedReadWrite (self s) s
  \<and> permission_is SharedReadWrite (other s) s}
  cell_swap_body
  {s. True}"
  unfolding cell_swap_body_def
  apply vcg
  apply (auto simp add: Let_def nth_append)
  using permission_is_imp_writable writable_pop_tags by auto

\<comment> \<open>A proof that shows Cell::swap(self, other) swaps the value in the memory.\<close>
lemma cell_swap_correctness: "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s
  \<and> permission_is SharedReadWrite (self s) s
  \<and> permission_is SharedReadWrite (other s) s
  \<and> memread (self s) s = x
  \<and> memread (other s) s = y}
  cell_swap_body
  {s. memread (self s) s = y \<and> memread (other s) s = x}"
  unfolding cell_swap_body_def
  apply vcg
  apply (auto simp add: Let_def nth_append)
  using permission_is_imp_writable writable_pop_tags by auto

end