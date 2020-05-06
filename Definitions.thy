theory Definitions
  imports Main "HOL-Library.LaTeXsugar"
begin

text \<open>We present an imperative programming language with unique references called Unique, aiming at modeling the semantics of mutable references of Rust.
In Rust, (mutable) references borrow the ownership, the capacity to observe and modify the content they are referring to, for a certain amount of time.
References can borrow not only from a local variable or a heap allocation but also from another reference.
The latter case is called reborrowing. Reborrow forms a tree-like relation between references.
While the borrow checker of the Rust compiler enforces the reborrow relation to be well-formed (mutable xor alias!) statically, Unique tracks it dynamically.
Imagine running an abstract interpreter of Rust with a dynamic borrow checker.
At every point of use of unique references, Unique asserts that the reference is in the reborrow relation (the reference is valid) and removes every other reference reborrowed from it so that it is the only valid unique reference to the location.
We expect that this dynamic nature of Unique will help us deal with (type-) unsafe portion of Rust.
Note that this project is greatly influenced by R. Jung's Stacked Borrows@{cite "DBLP:journals/pacmpl/JungDKD20"}.\<close>

section \<open>Definitions and Notations\<close>

subsection \<open>Basic data types\<close>

type_synonym vname = string
datatype ty = Tbool | Tint | Tref ty
type_synonym tag = nat
type_synonym address = nat

text \<open>References consists of the address of the referent and the tag.
A unique tag is assigned to each reference on creation.\<close>

datatype val = VBool bool | VInt int | Reference address tag

subsection \<open>Expressions\<close>

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

text \<open>@{const_typ Box} allocates memory in the heap, initializing with the argument
(\rust{Box::new} in Rust). @{const Box} returns a new unique reference.
@{const_typ Reborrow} creates a new unique reference reborrowing from the argument
(\rust{&mut *p} in Rust, although most of the reborrows are automatically inserted by Rust).
@{const_typ Deref} retrieves the content from the heap the reference pointing to (\rust{*p} in Rust).\<close>

subsection \<open>Commands\<close>

datatype 
  com = Skip
  | VarAssign vname exp ("_ ::= _" [1000, 61] 61)
  | HeapAssign exp exp  ("*_ ::= _" [1000, 61] 61)
  | Seq com com         ("_;;/ _" [60, 61] 60)
  | If exp com com      ("(IF _/ THEN _/ ELSE _)" [0, 0, 61] 61)
  | WHILE exp com       ("(WHILE _/ DO _)" [0, 61] 61)

type_synonym gamma = "vname \<Rightarrow> val option"
type_synonym borrow_list = "tag list"
type_synonym heap = "(val * borrow_list) list"

fun kill :: "tag \<Rightarrow> borrow_list \<Rightarrow> borrow_list" where
  "kill t [] = []" |
  "kill t (x # xs) = (if t = x then [x] else
     case kill t xs of
       [] \<Rightarrow> [] |
       xs \<Rightarrow> x # xs)"

text \<open>The function @{const kill} calculates references to be invalidated by the use of the given reference.
The following two lemmas show that the used reference will be the ``leaf'' of the borrow tree.\<close>

lemma [simp]: "t \<notin> set ts \<Longrightarrow> kill t ts = []"
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  then show ?case by auto
qed

lemma [simp]: "t \<in> set ts \<Longrightarrow> kill t ts \<noteq> []" \<^marker>\<open>tag invisible\<close>
proof (induction ts) \<^marker>\<open>tag invisible\<close>
  case (Cons t' ts)
  then show ?case
    by (metis kill.simps(2) list.case_eq_if list.distinct(1) set_ConsD)
qed auto

lemma kill_lemma: "kill t ts = ts' \<Longrightarrow> ts' = [] \<or> last ts' = t" \<^marker>\<open>tag invisible\<close>
proof (induction ts arbitrary: ts') \<^marker>\<open>tag invisible\<close>
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  then show ?case
    by (metis (no_types, lifting) kill.simps(2) last.simps list.case_eq_if list.collapse)
qed

lemma [simp]: "t \<in> set ts \<Longrightarrow> last (kill t ts) = t" \<^marker>\<open>tag invisible\<close>
proof - \<^marker>\<open>tag invisible\<close>
  assume "t \<in> set ts"
  hence "kill t ts \<noteq> []" by simp
  thus "last (kill t ts) = t" using kill_lemma by auto
qed

lemma kill_lemma': "\<lbrakk>kill t ts = ts'; ts' \<noteq> []\<rbrakk> \<Longrightarrow> \<exists>ts''. ts' = ts'' @ [t]" \<^marker>\<open>tag invisible\<close>
proof (induction ts arbitrary: ts') \<^marker>\<open>tag invisible\<close>
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  then show ?case
    by (metis kill_lemma snoc_eq_iff_butlast)
qed

lemma "t \<in> set ts \<Longrightarrow> \<exists>ts'. kill t ts = ts' @ [t]"
proof -
  assume "t \<in> set ts"
  hence "kill t ts \<noteq> []" by simp
  thus "\<exists>ts'. kill t ts = ts' @ [t]" using kill_lemma' by auto
qed

fun tags :: "heap \<Rightarrow> tag list" where
  "tags H = fold (\<lambda>e ts. ts @ (snd e)) H []"

fun fresh_tag :: "heap \<Rightarrow> tag" where
  "fresh_tag H = fold max (tags H) 0 + 1"

text \<open>Function @{const_typ fresh_tag} generates a new tag which doesn't exist in the tree.
(FIXME: I figure that @{const fresh_tag} may reuse tags if they have been already killed.
We need to record all the tags generated.)\<close>

fun writable :: "address \<Rightarrow> tag \<Rightarrow> heap \<Rightarrow> bool" where
  "writable p t H \<longleftrightarrow> p < length H \<and> t \<in> set (snd (H ! p))"
definition "readable" where "readable = writable"

text \<open>Functions @{const_typ writable} and @{const_typ readable} determine whether the given reference
can be used to write to/read from it. The validity of references is determined by the existence in the current borrow tree.
In Unique, we allow only unique references. Thus @{const readable} is equivalent to @{const writable}.\<close>

end