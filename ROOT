session "Rust-Verification" in "Rustv" = Simpl +
  options [document = false, document_output = "output", document_variants="document=/proof"]
  sessions
    "Simpl"
  theories [show_question_marks = false]
    Defs
    BorrowStack
    Rustv
  (*
  document_files
    "root.tex"
    "root.bib"
  *)

session "Rust-Verification-Tests" in "Rustv/Tests"  = "Rust-Verification" +
  options [document = false, document_output = "output", document_variants="document=/proof"]
  directories
    ex
  theories [show_question_marks = false]
    Rustv_Tests

session "Old-Theories" in "Unique" = HOL +
  options [document = false, document_output = "output", document_variants="document=/proof", quick_and_dirty]
  sessions
    "HOL-Library" (* for HOL-Library.LaTeXsugar *)
  theories [show_question_marks = false]
    Unique
