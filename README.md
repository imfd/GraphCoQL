# GraphCoQL

GraphCoQL is a mechanized formalization of [GraphQL](https://graphql.github.io/graphql-spec/June2018/), written
in the [Coq Proof Assistant](https://coq.inria.fr).

The following sections detail how to setup the project, build it and the current status of the project. For the complete documentation you  may either look at the following [page](graphcoql.netlify.com) or build the project and see the `coqdoc` generated documentation.  

Finally, the README file in the `src` folder specifies how the definitions and proofs are structured.

## Setup & build

In this section we describe how to setup the project, its dependencies and then build it.

First of all, clone the project and then, in a terminal, navigate to the project's folder.
```bash
$ git clone https://github.com/imfd/GraphCoQL.git # Clone the respository
$ cd GraphCoQL/ # Navigate inside the project's folder
```

Then, we proceed to install the dependencies and build the project. We describe how to install each in the following subsections. As a general overview, GraphCoQL depends on the following:
- Coq v8.9.1
- Equations v.1.2+8.9
- Mathematical Components v.1.9.0

### Using [Docker](https://www.docker.com) and Dockerfile

We include a `Dockerfile` with the necessary image and commands to get the project up and running. The image is based on Debian 10 (more information can be found [here](https://github.com/coq-community/docker-coq)) and contains Coq v8.9.1, as well as all necessary dependencies to build the project.

To download the image and setup the necessary environment, run the following command (in the project's root directory), which will search for the `Dockerfile` in the directory where the command is being executed and name the image `gcoql`.

```bash
$ docker build -t gcoql .
```

Once the image is setup, one can start a container and work on the project. The following command starts a container interactively (with a prompt), sets the current directory as a volume (changes made in the container will be reflected in the directory) and sets it as the current working directory.

```bash
$ docker run -it -v "$PWD:$PWD" -w "$PWD" gcoql
```

It is possible to now build the project, by simply running the following command in the interactive console associated to the container.
```bash
$ make
```
It is now possible to start programming in Coq and GraphCoQL or explore its documentation :tada:.

### Manually setup the project (without Docker)

#### Install Opam and initialize it

We describe the process of installing the GraphCoQL dependencies by means of the Ocaml Package Manager ([Opam](https://opam.ocaml.org/)).

Installation of Opam may vary from distribution and operating system, hence we defer the appropriate instructions to their [installation site](https://opam.ocaml.org/doc/Install.html).

After installing Opam, it must be initialized prior to its first usage. The following script initializes it and updates environment variables.

```bash
$ opam init # initializes opam
$ eval $(opam env) # updates opam environment variables
```

#### Install Coq

First, we install [Coq](https://coq.inria.fr/download) using the following command. This command pins Opam to a particular version of Coq (particularly, version 8.9.1) and installs Coq in the system.

```bash
# Pin the coq package to version 8.9.1 and install it.
$ opam pin add coq 8.9.1
```

For a more precise guide on installing Coq, you may follow the [instructions in the Coq website](https://coq.inria.fr/opam-using.html).

#### Install the Equations library
Next, we install the [Equations](http://mattam82.github.io/Coq-Equations/) library, by means of the two following command.

The first command allows Opam to find Coq packages. As stated in the Coq installation site:
> Coq packages live in a repository separate from the standard OCaml repository. This commands makes them available:

```bash
$ opam repo add coq-released https://coq.inria.fr/opam/released
```

Once that step is performed, one can install the Equations package, by means of the following command.

```bash
$ opam install coq-equations.1.2+8.9
```

#### Install the Mathematical Components library

Then, we install the [Mathematical Components](https://github.com/math-comp/math-comp) library.

```bash
$ opam install coq-mathcomp-ssreflect.1.9.0
```

#### Build the project

Finally, once all dependencies have been installed, it is possible to build the project. This is simply done by calling `make` in the top directory.
```bash
$ make
```

The process will then compile all required `*.v` files and generate the html documentation, stored in the directory `docs`.

It is now possible to start programming in Coq and GraphCoQL or explore its documentation :tada:.

## What GraphQL features does GraphCoQL support?

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
