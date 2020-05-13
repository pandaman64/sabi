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
datatype tag_kind = Unique

text \<open>References consists of the address of the referent and the tag.
A unique tag is assigned to each reference on creation.\<close>

datatype val = VBool bool | VInt int | Reference address tag

subsection \<open>Expressions\<close>

datatype place = Var vname | Deref place

text \<open>Datatype @{typ place} represents an access path to data.
It corresponds to \rust{Place} in \<^url>\<open>https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.Place.html\<close>\<close>

datatype operand = Place place | Constant val

text \<open>Datatype @{typ operand} describes a value inside an rvalue.
\<^term>\<open>Place\<close> denotes the current value at the place, while \<^term>\<open>Constant\<close> denotes a constant value.
@{typ operand} corrensponds to \rust{Place} in \<^url>\<open>https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.Operand.html\<close>,
though we simplified the differentiation between a move and a copy
(i.e. Unique doesn't track the ownership).\<close>

datatype
  rvalue = Use operand
  | Box operand
  | Ref place
  | Reborrow place
  | Plus operand operand
  | Less operand operand
  | Not operand
  | And operand operand

text \<open>Datatype @{typ rvalue} corresponds to an expression in a usual programming language
(as in the previous version of Unique).
We chose the term rvalue because of parity with Rust MIR
(\<^url>\<open>https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.Rvalue.html\<close>)

Note that @{typ rvalue} is \<^emph>\<open>not\<close> recursive.
Compound expressions need to be broken apart so that intermediate computation is stored to a variable.
\<close>

text \<open>
The semantics of the constructs is as follows:
\<^item> @{const_typ Box} allocates memory in the heap, initializing with the argument
(\rust{Box::new} in Rust). @{const Box} returns a new unique reference.
Note that Box in MIR doesn't initialize the location but only allocates.
The semantics will be adapted to MIR's one as we formalize uninitialized memory.
\<^item> @{const_typ Ref} creates a unique reference pointing to the place.
\<^item> @{const_typ Reborrow} creates a new unique reference reborrowing from the argument
(\rust{&mut *p} in Rust, although most of the reborrows are automatically inserted by Rust).
(TODO: I guess \rust{Use(Copy(mutable ref))} in MIR corresponds to Reborrow in Unique. )
\<close>

subsection \<open>Commands\<close>

datatype
  com = Skip
  | Assign place rvalue ("_ ::= _" [1000, 61] 61)
  | Seq com com         ("_;;/ _" [60, 61] 60)
  | If rvalue com com      ("(IF _/ THEN _/ ELSE _)" [0, 0, 61] 61)
  | WHILE rvalue com       ("(WHILE _/ DO _)" [0, 61] 61)

type_synonym gamma = "vname \<Rightarrow> address * tag"

text \<open>Unique implicitly performs boxing to variables. In other words,
every variable behaves as a root reference to a memory cell.\<close>

type_synonym tags = "tag_kind list"
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

(*<*)
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

lemma kill_lemma': "\<lbrakk>kill t ts = ts'; ts' \<noteq> []\<rbrakk> \<Longrightarrow> \<exists>ts''. ts' = ts'' @ [t]"
proof (induction ts arbitrary: ts')
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  then show ?case
    by (metis kill_lemma snoc_eq_iff_butlast)
qed
(*>*)

lemma "t \<in> set ts \<Longrightarrow> \<exists>ts'. kill t ts = ts' @ [t]"
proof -
  assume "t \<in> set ts"
  hence "kill t ts \<noteq> []" by simp
  thus "\<exists>ts'. kill t ts = ts' @ [t]" using kill_lemma' by auto
qed

fun kill_heap :: "(address * tag) \<Rightarrow> heap \<Rightarrow> heap" where
  "kill_heap (a, t) H = (let (v, ts) = H ! a in H[a := (v, kill t ts)])"
abbreviation kill_all :: "(address * tag) list \<Rightarrow> heap \<Rightarrow> heap" where
  "kill_all refs H == foldr kill_heap refs H"

fun writable :: "heap \<Rightarrow> (address * tag) \<Rightarrow> bool" where
  "writable H (p, t) \<longleftrightarrow> p < length H \<and> t \<in> set (snd (H ! p))"
definition "readable" where "readable = writable"

text \<open>Functions @{const_typ writable} and @{const_typ readable} determine whether the given reference
can be used to write to/read from it. The validity of references is determined by the existence in the current borrow tree.
In Unique, we allow only unique references. Thus @{const readable} is equivalent to @{const writable}.\<close>

definition allocated :: "heap \<Rightarrow> address \<Rightarrow> bool" where
  "allocated H a \<longleftrightarrow> a < length H"

(*<*)
lemma kill_all_head: "kill_all (h # t) H = kill_heap h (kill_all t H)" by simp
lemma kill_all_append[simp]: "kill_all (l1 @ l2) H = kill_all l1 (kill_all l2 H)" by simp

lemma kill_preserve_length: "\<lbrakk>length H = l; H' = kill_heap (a, t) H\<rbrakk> \<Longrightarrow> length H' = l"
  by (simp add: prod.case_eq_if)

lemma kill_all_preserve_length: "\<lbrakk>length H = l; H' = kill_all refs H\<rbrakk> \<Longrightarrow> length H' = l"
proof (induction refs arbitrary: l H H')
  case Nil
  then show ?case by simp
next
  case (Cons h t)
  moreover have "H' = kill_heap h (kill_all t H)" using calculation(3) kill_all_head by blast
  moreover have "length (kill_all t H) = l" using Cons.IH calculation(2) by blast
  moreover have "length H' = l"
    by (metis Cons.IH calculation(2) calculation(3) kill_all_head
              kill_heap.elims kill_preserve_length)
  ultimately show ?case by simp
qed

lemma kill_preserve_allocated: "\<lbrakk>allocated H a; H' = kill_heap (a, t) H\<rbrakk> \<Longrightarrow> allocated H' a"
  using allocated_def kill_preserve_length by force

lemma kill_all_preserve_allocated: "\<lbrakk>allocated H a; H' = kill_all refs H\<rbrakk> \<Longrightarrow> allocated H' a"
  using allocated_def kill_all_preserve_length by force

lemma kill_heap_access: "\<lbrakk>allocated H a; H ! a = (v, ts); H' = kill_heap (a', t) H\<rbrakk> \<Longrightarrow>
  H' ! a = (if a = a' then (v, kill t ts) else (v, ts))"
  by (smt allocated_def fst_conv kill_heap.simps nth_list_update_eq
          nth_list_update_neq prod.case_eq_if snd_conv)

lemma "\<lbrakk>allocated H a; H' = kill_all refs H\<rbrakk> \<Longrightarrow>
  H' ! a = foldr (\<lambda>(a', t) (v, ts). if a = a' then (v, kill t ts) else (v, ts)) refs (H ! a)"
proof (induction refs arbitrary: H')
  case Nil
  then show ?case by auto
next
  case (Cons ata refs H')
  obtain aa ta where ata: "ata = (aa, ta)" by fastforce
  let ?H = "kill_all refs H"
  let ?f = "\<lambda>(a', t) (v, ts). if a = a' then (v, kill t ts) else (v, ts)"

  have "?H ! a = foldr ?f refs (H ! a)" using Cons.IH Cons.prems by blast
  moreover obtain v ts where vts: "?H ! a = (v, ts)" by fastforce
  moreover have mid: "foldr ?f refs (H ! a) = (v, ts)" using calculation by auto
  ultimately have rhs: "foldr ?f (ata # refs) (H ! a) = ?f ata (v, ts)" by (simp add: mid)

  assume "H' = kill_all (ata # refs) H"
  then have "H' = kill_heap (aa, ta) (kill_all refs H)" using ata by auto
  then have lhs: "H' ! a = (if a = aa then (v, kill ta ts) else (v, ts))"
    using Cons.prems(1) kill_all_preserve_allocated kill_heap_access vts by auto

  from lhs rhs show "H' ! a = foldr ?f (ata # refs) (H ! a)" by (simp add: ata)
qed
(*>*)

end