# sabi: formal verification framework for Rust programs (including unsafe)

## Dependency

* Isabelle 2020
* Simpl. You can download Simpl from Archive of Formal Proofs. I'm going to vendor it in some future.

## How to develop
### Building sessions

Run the following command in the root directory (the directory with ROOT file):
```
$ isabelle build -d /path/to/Simpl -D . -v
```

### Launching a jEdit session
```
$ isabelle jedit -d /path/to/Simpl -d .
```