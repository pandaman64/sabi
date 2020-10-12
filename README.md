# sabi: formal verification framework for Rust programs (including unsafe)

## Dependency

* Isabelle 2020

The theory depends on [Simpl](https://www.isa-afp.org/entries/Simpl.html), an imperative programming language for formal verification developed in Isabelle.
The vendored version is taken from AFP-2020-06-03.

## How to develop
### Building sessions

Run the following command in the root directory (the directory with ROOT file):
```
$ isabelle build -d ./Simpl -D . -v
```

### Launching a jEdit session
```
$ isabelle jedit -d ./Simpl -d . Rustv/Rustv.thy
```

The `-l` option seems to have Isabelle cache the Simpl heap:
```
$ isabelle jedit -l Simpl -d Simpl -d . Rustv/Rustv.thy
```
