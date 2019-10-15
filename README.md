# GraphCoQL

GraphCoQL is a mechanized formalization of [GraphQL](https://graphql.github.io/graphql-spec/June2018/), written
in the [Coq Proof Assistant](https://coq.inria.fr).

The following sections detail how to setup the project, build it and the current status of the project. For the complete documentation you  may either look at the following [page](graphcoql.netlify.com) or build the project and see the `coqdoc` generated documentation.  

Finally, the README file in the `src` folder specifies how the definitions and proofs are structured.

## Setup

GraphCoQL requires the following packages:
- [Coq v8.9.1](https://coq.inria.fr/download)
- [Equations v.1.2+8.9](http://mattam82.github.io/Coq-Equations/)
- [Mathematical Components v.1.9.0](https://github.com/math-comp/math-comp)

The following setup instructions are based on using [Opam](https://opam.ocaml.org/doc/Install.html) to install the dependencies (so we recommend using it).

### Initialize Opam
After installing Opam, it must be initialized prior to its first usage. The following script initializes it and updates environment variables.

```bash
opam init
eval $(opam env)
```

### Installing Coq
The following script pins Opam to a particular version of Coq and installs it.

```bash
# Pin the coq package to version 8.9.1 and install it.
opam pin add coq 8.9.1
```

For a more precise guide on installing Coq, you may follow the [instructions in the Coq website](https://coq.inria.fr/opam-using.html).

### Installing Equations library
```bash
opam install coq-equations
# Alternatively to install a specific version: opam install coq-equations.1.2+8.9
```

### Installing the Mathematical Components library
```bash
opam install coq-mathcomp-ssreflect
# Alternatively to install a specific version: opam install coq-mathcomp-ssreflect.1.9.0
```


## What's implemented?

Here we briefly describe the features that GraphCoQL currently supports. Each feature is linked to the specific section in the latest release of the GraphQL specification (June 2018).

### [Executable definitions](https://graphql.github.io/graphql-spec/June2018/#ExecutableDefinition)

| Feature                                                                                  |     Supported?     |
|------------------------------------------------------------------------------------------|:------------------:|
| [Query](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Operations)        | :white_check_mark: |
| [Mutation](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Operations)     |         :x:        |
| [Subscription](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Operations) |         :x:        |
| [Fragments](https://graphql.github.io/graphql-spec/June2018/#FragmentDefinition)         |         :x:        |
