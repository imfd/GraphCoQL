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

The specification considers `Query`, `Mutation`, `Subscription` and `Fragment` definition as executable definitions. We list them here, as well as features related to them (variable and directive definitions).

| Feature                                                                                  |     Supported?     |
|------------------------------------------------------------------------------------------|:------------------:|
| [Query](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Operations)        | :white_check_mark: |
| [Mutation](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Operations)     |         :x:        |
| [Subscription](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Operations) |         :x:        |
| [Fragments](https://graphql.github.io/graphql-spec/June2018/#FragmentDefinition)         |         :x:        |
| [Variable Definition](https://graphql.github.io/graphql-spec/June2018/#VariableDefinitions)   | :x:  |
| [Directives](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Directives)  | :x:  |



### [Type System Definitions](https://graphql.github.io/graphql-spec/June2018/#sec-Type-System) & [Type System Extensions](https://graphql.github.io/graphql-spec/June2018/#sec-Type-System-Extensions)

We list here the features related to defining new types in a GraphQL schema.

There is currently no type extension implemented, therefore we omit them from the table to ease reading.

| Feature                                                                                     |     Supported?     |
|---------------------------------------------------------------------------------------------|:------------------:|
| [Schema](https://graphql.github.io/graphql-spec/June2018/#sec-Schema)                       | :white_check_mark: |
| [Scalar Types](https://graphql.github.io/graphql-spec/June2018/#sec-Scalars)                | :white_check_mark: |
| [Object Types](https://graphql.github.io/graphql-spec/June2018/#sec-Objects)                |  :white_check_mark |
| [Interface Types](https://graphql.github.io/graphql-spec/June2018/#sec-Interfaces)          | :white_check_mark: |
| [Union Types](https://graphql.github.io/graphql-spec/June2018/#sec-Unions)                  | :white_check_mark: |
| [Enum Types](https://graphql.github.io/graphql-spec/June2018/#sec-Enums)                    | :white_check_mark: |
| [Input Object Types](https://graphql.github.io/graphql-spec/June2018/#sec-Input-Objects)    |         :x:        |
| [List Types](https://graphql.github.io/graphql-spec/June2018/#sec-Type-System.List)         | :white_check_mark: |
| [Non-Null Types](https://graphql.github.io/graphql-spec/June2018/#sec-Type-System.Non-Null) |         :x:        |
| [Descriptions](https://graphql.github.io/graphql-spec/June2018/#sec-Descriptions)           |         :x:        |
| [Directive Definition](https://graphql.github.io/graphql-spec/June2018/#sec-Type-System.Directives)   |         :x:        |


### [Introspection](https://graphql.github.io/graphql-spec/June2018/#sec-Introspection)

The current version does not support introspection.

### [Selection Set](https://graphql.github.io/graphql-spec/June2018/#sec-Selection-Sets)

Here we list the currently supported features related to selections.

| Feature                                                                                         |     Supported?     |
|-------------------------------------------------------------------------------------------------|:------------------:|
| [Fields](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Fields)                  | :white_check_mark: |
| [Fragment Spreads](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Fragments)     |         :x:        |
| [Inline Fragments](https://graphql.github.io/graphql-spec/June2018/#sec-Inline-Fragments)       | :white_check_mark: |
| [Directives](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Directives)          |         :x:        |
| [Variables](https://graphql.github.io/graphql-spec/June2018/#sec-Language.Variables)            |         :x:        |
| [Input Object Values](https://graphql.github.io/graphql-spec/June2018/#sec-Input-Object-Values) |         :x:        |

### Validation

GraphCoQL also performs validation over the type system and queries.

The validation rules for type definitions may be found in the subsections `Type Validation` for each type, in the  specification. The implementation may also be found in the file [SchemaWellFormedness.v](SchemaWellFormedness.v).

Meanwhile, the validation of GraphQL queries, specified in section [Validation](https://graphql.github.io/graphql-spec/June2018/#sec-Validation) of the spec, is also implemented by GraphCoQL, for the features that it currently supports (e.g. Validation over inline fragments and field merging, but not over variables).

### [Execution of GraphQL Queries](https://graphql.github.io/graphql-spec/June2018/#sec-Query)

We currently define the semantics of GraphQL queries over a graph data model, following the example of Hartig & Pérez.
The specification defers evaluation to `resolvers`, which may contain arbitrary pieces of code. Therefore, to reason over selections it is necessary to use a sensible data model.

The current implementation tries to follow the [algorithmic definition](https://graphql.github.io/graphql-spec/June2018/#sec-Executing-Selection-Sets) provided by the specification, as closely as possible.

Errors are not currently supported by GraphCoQL.
