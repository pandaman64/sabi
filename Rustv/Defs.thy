theory Defs
  imports Main
begin

datatype rust_error = invalid_ref

datatype pointer = ptr_val nat
datatype tag = tag_val nat
record tagged_ref =
  pointer :: pointer
  tag :: tag
datatype val = uninit | int_val int | ref tagged_ref

fun the_ref where
  "the_ref (ref r) = r" |
  "the_ref _ = undefined"

fun the_ptr :: "pointer \<Rightarrow> nat" where
  "the_ptr (ptr_val p) = p"

fun the_tag :: "tag \<Rightarrow> nat" where
  "the_tag (tag_val t) = t"

datatype ref_kind = Unique | SharedReadWrite | SharedReadOnly
type_synonym 'a stack = "'a list"

end