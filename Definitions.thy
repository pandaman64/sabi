theory Definitions
  imports Main "~~/src/HOL/Library/LaTeXsugar"
begin

section \<open>Definitions and Notations\<close>

type_synonym vname = string
datatype ty = Tbool | Tint | Tref ty
datatype tag = Tag nat
datatype address = Address nat
datatype val = VBool bool | VInt int | Reference address tag

datatype 
  exp = Const val
  | Var vname
  | Box exp
  | Reborrow exp
  | Deref exp
  | Plus exp exp
  | Less exp exp
  | Not exp
  | And exp exp

datatype 
  com = Skip
  | VarAssign vname exp ("_ ::= _" [1000, 61] 61)
  | HeapAssign exp exp  ("*_ ::= _" [1000, 61] 61)
  | Seq com com         ("_;;/ _" [60, 61] 60)
  | If exp com com      ("(IF _/ THEN _/ ELSE _)" [0, 0, 61] 61)
  | WHILE exp com       ("(WHILE _/ DO _)" [0, 61] 61)

type_synonym gamma = "vname \<Rightarrow> val option"
type_synonym heap = "address \<Rightarrow> val option"

type_synonym borrow_list = "tag list"
type_synonym reborrow = "address \<Rightarrow> borrow_list option"
fun kill :: "tag \<Rightarrow> borrow_list \<Rightarrow> borrow_list" where
  "kill t [] = []" |
  "kill t (x # xs) = (if t = x then [x] else
     case kill t xs of
       [] \<Rightarrow> [] |
       xs \<Rightarrow> x # xs)"

lemma [simp]: "t \<notin> set ts \<Longrightarrow> kill t ts = []"
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  then show ?case by auto
qed

lemma [simp]: "t \<in> set ts \<Longrightarrow> kill t ts \<noteq> []"
proof (induction ts)
  case (Cons t' ts)
  then show ?case
    by (metis kill.simps(2) list.case_eq_if list.distinct(1) set_ConsD)
qed auto

lemma kill_lemma: "kill t ts = ts' \<Longrightarrow> ts' = [] \<or> last ts' = t"
proof (induction ts arbitrary: ts')
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  then show ?case
    by (metis (no_types, lifting) kill.simps(2) last.simps list.case_eq_if list.collapse)
qed

lemma [simp]: "t \<in> set ts \<Longrightarrow> last (kill t ts) = t"
proof -
  assume "t \<in> set ts"
  hence "kill t ts \<noteq> []" by simp
  thus "last (kill t ts) = t" using kill_lemma by auto
qed

definition fresh :: "'a \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> bool" where
  "fresh x f \<longleftrightarrow> f x = None"

definition tags :: "reborrow \<Rightarrow> tag set" where
  "tags R = {t. \<exists>p. t \<in> set (the (R p))}"

definition fresh_tag :: "tag \<Rightarrow> reborrow \<Rightarrow> bool" where
  "fresh_tag t R \<longleftrightarrow> t \<notin> tags R"

fun writable :: "address \<Rightarrow> tag \<Rightarrow> reborrow \<Rightarrow> bool" where
  "writable p t R \<longleftrightarrow> t \<in> set (the (R p))"
definition "readable" where "readable = writable"

text \<open>Relations @{const_typ writable} and @{const_typ readable} determine whether the given reference
can be used to write to/read from it. In Unique, we allow only unique references. In other words,
there must be a single path from the root reference acquired at the time of initialization (Box).\<close>

end