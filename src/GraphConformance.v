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

  Section GraphAux.

    Variable (graph :  @graphQLGraph Vals).
    Implicit Type edge : @node Vals * @fld Vals * @node Vals.

    
    
    (** Extractors for an edge **)


    Definition etarget edge : node :=
      let: (_, _, v) := edge in v.

    Definition esource edge : node :=
      let: (u, _, _) := edge in u.

    Definition efield edge : fld :=
      let: (_, f, _) := edge in f.

    Definition enodes edge : seq node := [:: edge.(esource) ; edge.(etarget)].
    
    (** Get all nodes from a graph **)
    Definition nodes graph : seq node :=
      undup (graph.(root) ::  flatten [seq edge.(enodes) | edge <- graph.(E)]).



    (** Get all neighbours of a node irrespective of the field in the edge 
      connecting the two **)
    Definition neighbours (u : node) (edges : seq (node * fld * node)) : seq node :=
      undup [seq edge.(etarget) | edge <- edges & edge.(esource) == u]. 

    


    (** Get all neighbours of a node that are linked via an edge with a given
      field. **)
    Definition neighbours_with_field (u : node) (f : fld) : seq node :=
      undup [seq edge.(etarget) |  edge <- [seq edge <- graph.(E) | (esource edge == u) & (efield edge == f)]].


    (** 
      Checks whether there is only one edge coming out of the source node and 
      having the given field.
     **)
    Definition is_field_unique_for_src_node graph (src_node : node) (f : fld) : bool :=
      uniq [seq edge <- graph.(E) | (esource edge == src_node) & (efield edge == f)].
    
    
    

  End GraphAux.

  

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
 
      This is used when validating edges' fields and nodes' properties.
   **)
  
  Definition arguments_conform schema ty (f : fld) : bool :=
    let argument_conforms (fname : Name) (arg : Name * Vals) : bool :=
        let: (argname, value) := arg in
        match lookup_argument_in_type_and_field schema ty fname argname with
        | Some field_arg => (has_type schema) field_arg.(argtype) value    (* If the argument is declared then check its value's type *)
        | _ => false
        end
    in
    all (argument_conforms f.(label)) f.(args).
 

    


  


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
     #<strong>nodes_conform</strong># : wfGraphQLSchema → graphQLGraph → Bool 

     The following predicate checks whether a graph's nodes conform to a given Schema.
     This is done by checking that:
     - Every node's type is an Object type.
     - Every property conforms.

     The latter is done by checking that:
     - The properties are actually defined in the type of the node.
     - The field's arguments conform.
     - The properties values have a valid type wrt. to what is expected in the Schema 
       (If we expect a field to have Int type then the value should ressemble an Int).
   **)
  
  Definition nodes_conform schema graph :=
    let property_conforms ty (fd : fld * (Vals + seq Vals)) : bool :=
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
        all (property_conforms u.(ntype)) u.(nprops)
    in
    all node_conforms graph.(nodes).

  
  (** ---- *)
  (**
     A GraphQL graph conforms to a given Schema if:
     - Its root conforms to the Schema.
     - Its edges conform to the Schema.
     - Its nodes conform to the Schema.

   **)
  Record conformedGraph schema := ConformedGraph {
                                                graph;
                                                _ : root_type_conforms schema graph;
                                                _ : edges_conform schema graph;
                                                _ : nodes_conform schema graph
                                      }.

  Coercion graph_of_conformed_graph schema (g : conformedGraph schema) := let: ConformedGraph g _ _ _ := g in g.


               
    

End Conformance.



(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.Graph.html' class="btn btn-light" role='button'> Previous ← GraphQL Graph</a>
        <a href='GraphCoQL.Response.html' class="btn btn-info" role='button'>Continue Reading → GraphQL Response </a>
    </div>#
*)