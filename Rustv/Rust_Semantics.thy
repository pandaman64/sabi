theory Rust_Semantics
  imports Rustv Simpl.Vcg
begin

section \<open>Shallow embedding of Rust Primitives\<close>

(* In this theory, we are translating Rust assignments of the form of
 * *dst = *src;
 * as follows.
 * Note that we are ignoring Drop semantics. Strictly speaking, the following definition
 * models ptr::copy rather than assignment.
 *)
abbreviation copy_betw_places where
  "copy_betw_places src dst ==
     Guard invalid_ref {s. writable (dst s) s \<and> readable (src s) s}
      (Basic (\<lambda>s. pop_tags (dst s) s);;
      Basic (\<lambda>s. pop_tags (src s) s);;
      Basic (\<lambda>s. (let v = memread (src s) s in memwrite (dst s) v s)))"
abbreviation write_imm where
  "write_imm dst value ==
    Guard invalid_ref {s. writable (dst s) s}
      (Basic (\<lambda>s. pop_tags (dst s) s);;
      Basic (\<lambda>s. memwrite (dst s) value s))"
abbreviation reborrow_stmt where
  "reborrow_stmt k from to ==
    Guard invalid_ref {s. writable (from s) s}
      (Basic (\<lambda>s. pop_tags (from s) s);;
      Basic (\<lambda>s. (let (r, s') = reborrow k (from s) s in to s' r)))"

abbreviation ptr_eq :: "tagged_ref \<Rightarrow> tagged_ref \<Rightarrow> bool" where
  "ptr_eq r1 r2 == the_ptr (pointer r1) = the_ptr (pointer r2)"

syntax
  "_Cond'" :: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com => ('a,'p,'f) com"
        ("(0IFR (_)/ (2THEN/ _)/ (2ELSE _)/ FI)" [0, 0, 0] 71)
translations
  "IFR b THEN c1 ELSE c2 FI" == "CONST Cond b c1 c2"


end