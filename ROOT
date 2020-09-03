session "Rust-Verification" = HOL +
  options [document = pdf, document_output = "output", document_variants="document=/proof", quick_and_dirty]
  sessions
    "HOL-Library" (* for HOL-Library.LaTeXsugar *)
    "Simpl"
  directories
    Unique
    Rustv
  theories [show_question_marks = false]
    Unique
    Rustv
  document_files
    "root.tex"
    "root.bib"

session "Rust-Verification-Tests" in "Rustv/Tests"  = "Rust-Verification" +
  options [document = pdf, document_output = "output", document_variants="document=/proof", quick_and_dirty]
  directories
    ex
  theories [show_question_marks = false]
    Rustv_Tests
