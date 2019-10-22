# Code structure

We briefly describe how the code is structured to ease navigation. The filenames are quite explicit in their content, however we will try and make them more explicit (or at least the reasoning behind them).

The code is structured in three sections:

1. Source : The code contained in the current `src` folder includes the definitions of schemas, the graph data model and queries (including their semantics, normal form property, among others).
1. Theory : Proofs and tactics used for our definitions are stored in the `theory` folder.
1. Examples : We implement several examples, coming from different sources, in order to validate our implementation. These can be found in the `examples` folder.

## Values

The file `Value.v` contains the definition of the `Value` type, which represents either scalar or list of values, and is used in graphs and queries (to define properties's values or arguments).

## Schema

The formalization of GraphQL schemas, from their definition to their validation is defined in the files `Schema*.v`.
1. `Schema.v` : Contains the base definitions to build a schema (Type definitions, fields, arguments, the schema itself).
2. `SchemaAux.v` : Contains auxiliary definitions over schemas (such as looking up the type of a name, among others).
3. `SchemaWellFormedness.v` : Contains the necessary predicates to establish when a schema is _well-formed_. This file includes the definition of a `wfGraphQLSchema`, containing both a schema and a proof of its _well-formedness_.

The corresponding file with proofs over schemas is `SchemaLemmas.v`.

## Graph

The formalization of the graph data model, from its definition to its validation is defined in the files `Graph*.v`.

1. `Graph.v` : Contains the base definitions to build a graph (nodes, labels, the graph itself).
2. `GraphConformance.v` : Contains auxiliary definitions as well as the predicates to establish when a graph _conforms_ to a given schema.

The corresponding file with proofs over graphs is `GraphLemmas.v`.

## Query

The formalization of GraphQL queries, from their definition to their validation and their semantics is defined in the files `Query*.v`.

1. `Query.v` : Contains the base definitions to build queries (selections and query itself).
2. `QueryAux.v` : Contains auxiliary definitions over queries and selections (such as size of selections, among others).
3. `QueryConformance.v` : Contains the necessary predicates to establish when a query and its selection set _conform_ to a given schema.
4. `QuerySemantics.v` : Contains the definition of the semantics of queries over a graph data model, as well as the simplified semantics for queries in normal form (partially based on Hartig & Pérez definition).
5. `QueryTactics.v` : Contains a single tactic to facilitate reasoning over the size of selections (used throughout our formalization to define multiple recursive functions).

The files containing proofs about queries are in:
1. `QueryAuxLemmas.v` : Contains proofs over definitions in `QueryAux.v`.
2. `QueryConformanceLemmas.v` : Contains proofs over definitions in `QueryConformance.v`.
3. `QuerySemanticsLemmas.v` : Contains proofs about the semantics of queries.

## Normal Form

The formalization of the property of queries being in _normal form_ (defined by Hartig & Pérez), as well as the normalization procedure, is defined in the file `QueryNormalForm.v`.

The files containing proofs about normal form are in:
2. `QueryNormalFormLemmas.v` : Contains proofs over definitions in `QueryNormalForm.v`, including the correctness proof for the normalization function (that its output is indeed a query in normal form).
3. `QuerySemanticsLemmas.v` : Contains the proof that the normalization function preserves the queries's semantics.

## Response

Responses are simply defined in the `Response.v` file.

## Examples

We implement the following examples:
1. `HPExample.v` : Contains the example used in Hartig&Pérez [WWW'18], including the schema definition, graph, query and response.
2. `SpecExamples.v` : Contains the examples defined in the GraphQL specification, section [Validation](https://graphql.github.io/graphql-spec/June2018/#sec-Validation). These are examples over selections that are (in)valid in different contexts.
3. `GraphQLJSExamples.v` : Contains the [StarWars example](https://github.com/graphql/graphql-js/tree/master/src/__tests__) used in the GraphQL reference implementation. It includes the schema, a graph modeling the data used in the example, as well as the execution of a set of queries, along with their expected outputs.
4. `GoodBoisExample.v` : Contains the `GoodBois` example used in the GraphCoQL paper.
