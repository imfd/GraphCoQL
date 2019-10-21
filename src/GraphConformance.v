(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import String.
Require Import QString.
Require Import SeqExtra.

Require Import Value.

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
         This file contains the necessary definitions to check when a GraphQL Graph
         is valid wrt. to a GraphQL Schema. 
        </p>
         <p>
         This notion includes validations such as: 
          <ul>
           <li> Root node's type is same as the root query operation type. </li>
           <li> Fields in edges are defined in the Schema. </li>
           <li> Values used in arguments and properties correspond to the expected type in the Schema. </li>
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


(** * Conformance Predicates *)
(** ---- *)
Section Conformance.


  Variable (Scalar : eqType).

  (** ** Auxiliary definitions 
      ----

      In this section we define some auxiliary definitions.
   *)
  Section GraphAux.

    Variable (graph :  @graphQLGraph Scalar).
    Implicit Type edge : @node Scalar * @label Scalar * @node Scalar.

    
    
    (** *** Extractors for an edge *)
    (** ---- *)

    (**
       Returns an edge's target node.
     *)
    Definition etarget edge : node :=
      let: (_, _, v) := edge in v.

    (** ---- *)
    (**
       Returns an edge's source node.
     *)
    Definition esource edge : node :=
      let: (u, _, _) := edge in u.

    (** ---- *)
    (**
       Returns an edge's label.
     *)
    Definition efield edge : label :=
      let: (_, f, _) := edge in f.

    (** ---- *)
    (**
       Returns the nodes of an edge (source and target).
     *)
    Definition enodes edge : seq node := [:: edge.(esource) ; edge.(etarget)].

    (** *** Node related functions *)
    (** ---- *)
    
    (** 
        Returns all nodes from a graph.
     *)
    Definition nodes graph : seq node :=
      undup (graph.(root) ::  flatten [seq edge.(enodes) | edge <- graph.(edges)]).


    (** ---- *)
    (**
       Get the value of the property with the given label.
     *)
    Definition property (u : node) (lab : label) : option (@Value Scalar) :=
      if get_first (fun prop => prop.1 == lab) u.(nprops) is Some (_, value) then
        Some value
      else
        None.
  
    (** ---- *)
    (**
       Returns a node's neighbors.
     *)
    Definition neighbors (u : node) (edges : seq (node * label * node)) : seq node :=
      undup [seq edge.(etarget) | edge <- edges & edge.(esource) == u]. 

    

    (** ---- *)
    (**
       Get a node's neighbors connected via an edge with a given field. 
     *)
    Definition neighbors_with_label (u : node) (f : label) : seq node :=
      undup [seq edge.(etarget) |  edge <- [seq edge <- graph.(edges) | (esource edge == u) & (efield edge == f)]].


    (** ---- *)
    (** 
      This predicate checks whether there is only one edge coming out of the source node and 
      having the given field.
     *)
    Definition is_field_unique_for_src_node graph (src_node : node) (f : label) : bool :=
      uniq [seq edge <- graph.(edges) | (esource edge == src_node) & (efield edge == f)].
    
    
    

  End GraphAux.
  


  (** ** Predicates 
      ----

      In this section we define predicates to establish when a graph conforms 
      to a given schema.
   *)

  Section Predicates.

    (** In order to determine whether a value used in the graph correspond to the 
        expected type in the schema, we parameterize it with a predicate 
        that resolves it *)
    Variables (s : wfGraphQLSchema)
              (is_valid_scalar_value : graphQLSchema -> Name -> Scalar -> bool).


      
    (** *** Root type conforms
        ----

        This predicate checks that a Graph's root node must have the same type as the Schema's query type.
     **)
    Definition root_type_conforms (root : @node Scalar) : bool := (root).(ntype) == s.(query_type).
    

    (** *** Arguments conform
        ----

      This predicate checks a field's arguments conform to 
      what the Schema requires of them.
      - The arguments must be declared in the given type for that given field.
      - The arguments' values must be of the type declared for each argument in the schema.  
 
      This is used when validating edges' fields and nodes' properties.
     **)
    
    Definition arguments_conform ty (f : label) : bool :=
      let argument_conforms (fname : Name) (arg : Name * @Value Scalar) : bool :=
          let: (argname, value) := arg in
          match lookup_argument_in_type_and_field s ty fname argname with
          | Some field_arg => is_valid_value s is_valid_scalar_value field_arg.(argtype) value
          | _ => false
          end
      in
      all (argument_conforms f.(lname)) f.(args).
    



    (** *** Edges conform 
        ----

        This predicate checks whether a graph's edges conform to a Schema.
     
        This checks the following:
        - There are no repeated edges. 
        - Each edge conforms.

        And the latter is done by checking that:
        - The edge's field is defined in the source node.
        - The target node's type is a subtype of the edge's field type.
        - If the field's type is not a List type, then there must be only one edge connecting the source node 
        with the target node using the given label. 
       - The field's arguments conform.

       #<div class="hidden-xs hidden-md hidden-lg"><br></div>#    
       When checking that the target node's type is a subtype of the field's type, 
       the predicate simply ignores whether there is any nesting of list type. It takes the 
       base wrapped type and uses it to compare. This is due to the open question on how to
       properly model nested list types in a graph.
     **)    
    Definition edges_conform graph :=
      let edge_conforms (edge : node * label * @node Scalar) : bool :=
          let: (src, label, target) := edge in
          match lookup_field_in_type s src.(ntype) label.(lname) with
          | Some fdef =>
            if ~~is_list_type fdef.(ftype) then
              [&& target.(ntype) \in get_possible_types s fdef.(ftype),
                                     is_field_unique_for_src_node graph src label &
                                     arguments_conform src.(ntype) label]
            else
              (target.(ntype) \in get_possible_types s fdef.(ftype)) && arguments_conform src.(ntype) label
          | _ => false     
          end
      in
      uniq graph.(edges) && all edge_conforms graph.(edges).
    

    
    (** *** Nodes conform
        ----

        The following predicate checks whether a graph's nodes conform to a given Schema.
        This is done by checking that:
        - Every node's type is an object type.
        - Every property conforms.

        The latter is done by checking that:
        - The properties are actually defined in the type of the node.
        - The field's arguments conform.
        - The properties values have a valid type wrt. to what is expected in the Schema.
       
     **)    
    Definition nodes_conform (nodes : seq (@node Scalar)) :=
      let property_conforms ty (fd : label * @Value Scalar) : bool :=
          match lookup_field_in_type s ty fd.1.(lname) with
          | Some fdef => arguments_conform ty fd.1 && is_valid_value s is_valid_scalar_value fdef.(ftype) fd.2
          | _ => false
          end
      in
      let node_conforms (u : node) :=
          is_object_type s u.(ntype) &&
                                     all (property_conforms u.(ntype)) u.(nprops)
      in
      all node_conforms nodes.

  End Predicates.

  Variable (is_valid_scalar_value : graphQLSchema -> Name -> Scalar -> bool).

  (** *** Conforming graph
      ----

     The following predicate checks whether a graph conforms to a given schema.
     
     A GraphQL graph conforms to a given Schema if:
     - Its root conforms to the Schema.
     - Its edges conform to the Schema.
     - Its nodes conform to the Schema.

   *)
  Definition is_a_conforming_graph (s : wfGraphQLSchema)
             (is_valid_scalar_value : graphQLSchema -> Name -> Scalar -> bool)
             (graph : @graphQLGraph Scalar) : bool :=
    [&& root_type_conforms s graph.(root),
        edges_conform s is_valid_scalar_value graph &
        nodes_conform s is_valid_scalar_value graph.(nodes)].

  
  (** * Conformed GraphQL Graph
      ----

     A conformed GraphQL graph is a graph which conforms to a given schema.

   **)
  Record conformedGraph (s : wfGraphQLSchema)
         (is_valid_scalar_value : graphQLSchema -> Name -> Scalar -> bool) :=
    ConformedGraph {
        graph : graphQLGraph;
        _ : is_a_conforming_graph s is_valid_scalar_value graph
      }.

  Coercion graph_of_conformed_graph s vsv (g : conformedGraph s vsv) := let: ConformedGraph g _ := g in g.             
    

End Conformance.




(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.Graph.html' class="btn btn-light" role='button'>Previous ← Graph</a>
        <a href='GraphCoQL.Query.html' class="btn btn-info" role='button'>Continue Reading → Query</a>
    </div>#
*)