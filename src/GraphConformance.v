(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import String.
Require Import QString.


Require Import Schema.
Require Import SchemaWellFormedness.
Require Import SchemaAux.
Require Import Graph.
Require Import GraphAux.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Graph Conformance</h1>
        <p class="lead">
         This file contains the necessary definitions to validate when a GraphQL Graph
         is valid wrt. to a Schema. 
        </p>
         <p>
         This notion includes things such as: 
          <ul>
           <li> Root node's type is same as the root query operation type. </li>
           <li> Fields in edges are defined in the Schema. </li>
           <li> Values for arguments and properties correspond to the expected type in the Schema. </li>
           <li> Etc. </li>
         </ul>
        </p>
         <p>
         We will progressively define predicates that check different aspects of a graph.
         From these we will ultimately define the predicate and structure for conformed graphs.
        </p>
  </div>
</div>#
 *)


Section Conformance.


  Variables (Vals: eqType).

  
  Implicit Type schema : @wfGraphQLSchema Vals.
  Implicit Type graph : @graphQLGraph Vals. 

  (** ---- *)
  (** 
      #<strong>root_type_conforms</strong># : wfGraphQLSchema → graphQLSchema → Bool

      This predicate checks that a Graph's root node must have the same type as the Schema's query type.
   **)
  Definition root_type_conforms schema graph : bool := graph.(root).(ntype) == schema.(query_type).
  

  (** ---- *)
  (** 
      #<strong>arguments_conform</strong># : wfGraphQLSchema → graphQLSchema → fld → Bool

      This predicate checks a field's arguments conform to 
      what the Schema requires of them.
      - The arguments must be declared in the given type for that given field.
      - The arguments' values must be of the type declared for each argument in the schema.  
 
   **)     
  Definition argument_conforms schema (ty fname : Name) (arg : Name * Vals) : bool :=
    let: (argname, value) := arg in
    match lookup_argument_in_type_and_field schema ty fname argname with
    | Some field_arg => (has_type schema) field_arg.(argtype) value    (* If the argument is declared then check its value's type *)
    | _ => false
    end.


  (** Checks whether all of the field's arguments conform to the schema **)
  Definition arguments_conform schema ty (f : fld) : bool :=
    all (argument_conforms schema ty f.(label)) f.(args).
 

    


  


  (** ---- *)
  (**
     #<strong>edges_conform</strong># : wfGraphQLSchema → graphQLSchema → Bool

     This predicate checks whether a graph's edges conform to a Schema.
     
     This checks the following:
     - There are no repeated edges. 
     - Each edge conforms.

     And the latter is done by checking that:
     - The edge's field is defined is defined in source node.
     - The target node's type is a subtype of the return type associated to the field of the edge.
     - If the field's return type is not a List type, then this is the only edge connecting the source node 
       with the target node using the given field. 
     - The field's arguments conform.
   **)
 
  Definition edges_conform schema graph :=
    let edge_conforms (edge : node * fld * @node Vals) : bool :=
        let: (src, fld, target) := edge in
        match lookup_field_in_type schema src.(ntype) fld.(label) with
        | Some fdef =>
          if ~~is_list_type fdef.(return_type) then
            [&& target.(ntype) \in get_possible_types schema fdef.(return_type),
                is_field_unique_for_src_node graph src fld &
                arguments_conform schema src.(ntype) fld]
          else
            (target.(ntype) \in get_possible_types schema fdef.(return_type)) && arguments_conform schema src.(ntype) fld
        | _ => false     
        end
    in
    uniq graph.(E) && all edge_conforms graph.(E).


  
  (** ---- *)
  (**
     It states whether a field conforms to the Schema.

     ∀ u ∈ N, f ∈ fld, v ∈ Vals ⋃ [Vals], λ (u, f[α]) = v 
     then it must be that:
     1. f ∈ fields (τ(u)) : 
          Field 'f' must be declared in the type associated to node 'u' in the Schema.

     2. v ∈ values (type (f)) :
          The value must be of the type declared for that field in the Schema.
    
     3. The arguments of 'f' must conform to what the Schema requires of them.

   **)
  
  Definition nodes_conform schema graph :=
    let field_conforms ty (fd : fld * (Vals + seq Vals)) : bool :=
        match lookup_field_in_type schema ty fd.1.(label) with
        | Some fdef =>
          arguments_conform schema ty fd.1 &&
                            match fd.2 with
                            | (inl value) => schema.(has_type) fdef.(return_type) value
                            | (inr values) => all (schema.(has_type) fdef.(return_type)) values
                            end
        | _ => false
        end
    in
    let node_conforms (u : node) :=
        is_object_type schema u.(ntype) &&
        all (field_conforms u.(ntype)) u.(nfields)
    in
    all node_conforms graph.(nodes).

  
  (**
     A GraphQL graph conforms to a given Schema if:
     1. Its root conforms to the Schema.
     2. Its edges conform to the Schema.
     4. Its nodes conform to the Schema.

   **)
  Record conformedGraph schema := ConformedGraph {
                                                graph;
                                                _ : root_type_conforms schema graph;
                                                _ : edges_conform schema graph;
                                                _ : nodes_conform schema graph
                                      }.

  Coercion graph_of_conformed_graph schema (g : conformedGraph schema) := let: ConformedGraph g _ _ _ := g in g.


               
    

End Conformance.

Arguments conformedGraph [Vals]. 