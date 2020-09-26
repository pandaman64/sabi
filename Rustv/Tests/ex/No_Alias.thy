theory No_Alias
  imports "Rust-Verification.Rustv"
begin

record no_alias_env = globals_ram +
  x :: tagged_ref (* locals are represented by owning reference *)
  ref1 :: tagged_ref
  ref2 :: tagged_ref

definition no_alias_body :: "(no_alias_env, 'p, rust_error) com" where
  "no_alias_body =
    (Seq (Basic (\<lambda>s. (let (r, s') = heap_new (int_val 100) s in
                     s'\<lparr> x := r \<rparr>)))

    (Seq (Guard invalid_ref {s. writable (x s) s}
           (Seq (Basic id)
                (Basic (\<lambda>s.
                  (let (r, s') = reborrow Unique (x s) s in
                  s'\<lparr> ref1 := r \<rparr>)))))
    (Seq (Guard invalid_ref {s. writable (ref1 s) s}
           (Seq (Basic (\<lambda>s. pop_tags (ref1 s) s))
                (Basic (\<lambda>s. memwrite (ref1 s) (int_val 200) s))))

    (Seq (Guard invalid_ref {s. writable (x s) s}
           (Seq (Basic id)
                (Basic (\<lambda>s.
                  (let (r, s') = reborrow Unique (x s) s in
                  s'\<lparr> ref2 := r \<rparr>)))))
         (Guard invalid_ref {s. writable (ref2 s) s}
           (Seq (Basic (\<lambda>s. pop_tags (ref2 s) s))
                (Basic (\<lambda>s. memwrite (ref2 s) (int_val 300) s))))
    ))))"


lemma lem: "(The (reborrow' Unique (tag_val
                 (Suc (max (Suc (max_list
  (map the_tag issued)))
                        (max_list (map the_tag issued)))))
               (tag_val
                 (Suc (max_list (map the_tag issued))))
               [(Unique,
                 {tag_val
                   (Suc (max_list
                          (map the_tag issued)))})])) =
  [(Unique, {(tag_val
                 (Suc (max (Suc (max_list
  (map the_tag issued)))
                        (max_list (map the_tag issued)))))}), (Unique,
                 {tag_val
                   (Suc (max_list
                          (map the_tag issued)))})]"
  using DerivUniqueUnique reborrow_by_comp by blast

value "(reborrow_comp Unique 
               (tag_val
                 (Suc (max (Suc (max
  (Suc (max_list (map the_tag issued)))
  (max_list (map the_tag issued))))
                        (max (Suc (max_list
    (map the_tag issued)))
                          (max_list
                            (map the_tag issued))))))
               (tag_val
                 (Suc (max_list (map the_tag issued))))
[(Unique,
                 {tag_val
                   (Suc (max (Suc (max_list
    (map the_tag issued)))
                          (max_list
                            (map the_tag issued))))}),
                (Unique,
                 {tag_val
                   (Suc (max_list
                          (map the_tag issued)))})])
 =[(Unique,
   {tag_val
     (Suc (max (Suc (max (Suc (max_list (map the_tag issued))) (max_list (map the_tag issued))))
            (max (Suc (max_list (map the_tag issued))) (max_list (map the_tag issued)))))}),
  (Unique, {tag_val (Suc (max_list (map the_tag issued)))})]"

value "BorrowStack.reborrow Unique
  (tag_val
    (Suc (max (Suc (max (Suc (max_list (map the_tag issued))) (max_list (map the_tag issued))))
           (max (Suc (max_list (map the_tag issued))) (max_list (map the_tag issued))))))
 [(Unique, {tag_val (Suc (max_list (map the_tag issued)))})]"

lemma x[simp]: "(dropWhile (\<lambda>u. tag_val (Suc (max_list (map the_tag issued))) \<notin> snd u)
    [(Unique,
      {tag_val (Suc (max (Suc (max_list (map the_tag issued))) (max_list (map the_tag issued))))}),
     (Unique, {tag_val (Suc (max_list (map the_tag issued)))})]) = [(Unique, {tag_val (Suc (max_list (map the_tag issued)))})]"
  by simp

lemma lem3: "reborrow' Unique
               (tag_val
                 (Suc (max (Suc (max
  (Suc (max_list (map the_tag issued)))
  (max_list (map the_tag issued))))
                        (max (Suc (max_list
    (map the_tag issued)))
                          (max_list
                            (map the_tag issued))))))
               (tag_val
                 (Suc (max_list (map the_tag issued))))
               [(Unique,
                 {tag_val
                   (Suc (max (Suc (max_list
    (map the_tag issued)))
                          (max_list
                            (map the_tag issued))))}),
                (Unique,
                 {tag_val
                   (Suc (max_list
                          (map the_tag issued)))})]
 [(Unique,
   {tag_val
     (Suc (max (Suc (max (Suc (max_list (map the_tag issued))) (max_list (map the_tag issued))))
            (max (Suc (max_list (map the_tag issued))) (max_list (map the_tag issued)))))}),
  (Unique, {tag_val (Suc (max_list (map the_tag issued)))})]"
  apply (rule DerivPop)
   apply (rule DerivUniqueUnique)
  by auto

lemma lem2: "(The (reborrow' Unique
               (tag_val
                 (Suc (max (Suc (max
  (Suc (max_list (map the_tag issued)))
  (max_list (map the_tag issued))))
                        (max (Suc (max_list
    (map the_tag issued)))
                          (max_list
                            (map the_tag issued))))))
               (tag_val
                 (Suc (max_list (map the_tag issued))))
               [(Unique,
                 {tag_val
                   (Suc (max (Suc (max_list
    (map the_tag issued)))
                          (max_list
                            (map the_tag issued))))}),
                (Unique,
                 {tag_val
                   (Suc (max_list
                          (map the_tag issued)))})])) =[(Unique,
   {tag_val
     (Suc (max (Suc (max (Suc (max_list (map the_tag issued))) (max_list (map the_tag issued))))
            (max (Suc (max_list (map the_tag issued))) (max_list (map the_tag issued)))))}),
  (Unique, {tag_val (Suc (max_list (map the_tag issued)))})]"
  using reborrow_by_comp lem3 by blast

(* Termination, by full VCG *)
lemma "\<Gamma> \<turnstile>\<^sub>t {s. wf_heap s} no_alias_body {s. True}"
  unfolding no_alias_body_def
  apply vcg
  by (auto simp: Let_def lem lem2)

(* Spec of the program *)
lemma "\<Gamma> \<turnstile>\<^sub>t
  {s. wf_heap s}
  no_alias_body
  {s. (let p = the_ptr (pointer (x s)) in
      memory s ! p = int_val 300) \<and>
      writable (x s) s \<and> \<not>writable (ref1 s) s \<and> writable (ref2 s) s}"
  unfolding no_alias_body_def
  apply vcg
  (* This auto takes too long because of the term size *)
  by (auto simp: Let_def lem lem2)

end