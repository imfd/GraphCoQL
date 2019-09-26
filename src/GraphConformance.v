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


(** * Conformance Predicates *)
Section Conformance.


  Variables (Vals: eqType).

  (** ---- *)
  (** ** Auxiliary definitions 

      In this section we define some auxiliary definitions.
   *)
  (** ---- *)
  Section GraphAux.

    Variable (graph :  @graphQLGraph Vals).
    Implicit Type edge : @node Vals * @fld Vals * @node Vals.

    
    
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
       Returns an edge's field (label).
     *)
    Definition efield edge : fld :=
      let: (_, f, _) := edge in f.

    (** ---- *)
    (**
       Returns the nodes of an edge (source and target).
     *)
    Definition enodes edge : seq node := [:: edge.(esource) ; edge.(etarget)].
    
    (** ---- *)
    (** 
        Returns all nodes from a graph.
     *)
    Definition nodes graph : seq node :=
      undup (graph.(root) ::  flatten [seq edge.(enodes) | edge <- graph.(E)]).


    (** ---- *)
    (**
       Returns a node's neighbours.
     *)
    Definition neighbours (u : node) (edges : seq (node * fld * node)) : seq node :=
      undup [seq edge.(etarget) | edge <- edges & edge.(esource) == u]. 

    

    (** ---- *)
    (**
       Get a node's neighbours connected via an edge with a given field. 
     *)
    Definition neighbours_with_field (u : node) (f : fld) : seq node :=
      undup [seq edge.(etarget) |  edge <- [seq edge <- graph.(E) | (esource edge == u) & (efield edge == f)]].


    (** ---- *)
    (** 
      This predicate checks whether there is only one edge coming out of the source node and 
      having the given field.
     *)
    Definition is_field_unique_for_src_node graph (src_node : node) (f : fld) : bool :=
      uniq [seq edge <- graph.(E) | (esource edge == src_node) & (efield edge == f)].
    
    
    

  End GraphAux.
  (** ---- *)
  


  (** ** Predicates 
      
      In this section we define predicates to establish when a graph conforms 
      to a given schema.
   *)

  Section Predicates.

    Variable (s : @wfGraphQLSchema Vals).


      
    (** ---- *)
    (** *** Root type conforms

      #<strong>root_type_conforms</strong># : wfGraphQLSchema → graphQLSchema → Bool

      This predicate checks that a Graph's root node must have the same type as the Schema's query type.
     **)
    Definition root_type_conforms (root : @node Vals) : bool := (root).(ntype) == s.(query_type).
    

    (** ---- *)
    (** *** Arguments conform

      #<strong>arguments_conform</strong># : wfGraphQLSchema → graphQLSchema → fld → Bool

      This predicate checks a field's arguments conform to 
      what the Schema requires of them.
      - The arguments must be declared in the given type for that given field.
      - The arguments' values must be of the type declared for each argument in the schema.  
 
      This is used when validating edges' fields and nodes' properties.
     **)
    
    Definition arguments_conform ty (f : fld) : bool :=
      let argument_conforms (fname : Name) (arg : Name * Vals) : bool :=
          let: (argname, value) := arg in
          match lookup_argument_in_type_and_field s ty fname argname with
          | Some field_arg => s.(is_valid_value) field_arg.(argtype) value    (* If the argument is declared then check its value's type *)
          | _ => false
          end
      in
      all (argument_conforms f.(label)) f.(args).
    



    (** ---- *)
    (** *** Edges conform 
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

       #<div class="hidden-xs hidden-md hidden-lg"><br></div>#    
       When checking that the target node's type is a subtype of the field's return type, 
       the predicate simply ignores whether there is any nesting of list type. It takes the 
       base wrapped type and uses it to compare. For instance, if the type is [[Human]] 
       then it checks for the Human type, but not [Human]. This is a limitation on how to model
       these types in a graph. More is discussed in the corresponding paper.     
     **)    
    Definition edges_conform graph :=
      let edge_conforms (edge : node * fld * @node Vals) : bool :=
          let: (src, fld, target) := edge in
          match lookup_field_in_type s src.(ntype) fld.(label) with
          | Some fdef =>
            if ~~is_list_type fdef.(return_type) then
              [&& target.(ntype) \in get_possible_types s fdef.(return_type),
                                     is_field_unique_for_src_node graph src fld &
                                     arguments_conform src.(ntype) fld]
            else
              (target.(ntype) \in get_possible_types s fdef.(return_type)) && arguments_conform src.(ntype) fld
          | _ => false     
          end
      in
      uniq graph.(E) && all edge_conforms graph.(E).
    

    
    (** ---- *)
    (** *** Nodes conform
        #<strong>nodes_conform</strong># : wfGraphQLSchema → graphQLGraph → Bool 

        The following predicate checks whether a graph's nodes conform to a given Schema.
        This is done by checking that:
        - Every node's type is an Object type.
        - Every property conforms.

        The latter is done by checking that:
        - The properties are actually defined in the type of the node.
        - The field's arguments conform.
        - The properties values have a valid type wrt. to what is expected in the Schema 
          (If a field has an Int type then the value should represent an integer value).
       
     **)    
    Definition nodes_conform (nodes : seq (@node Vals)) :=
      let property_conforms ty (fd : fld * Vals) : bool :=
          match lookup_field_in_type s ty fd.1.(label) with
          | Some fdef => arguments_conform ty fd.1 && s.(is_valid_value) fdef.(return_type) fd.2
          | _ => false
          end
      in
      let node_conforms (u : node) :=
          is_object_type s u.(ntype) &&
                                     all (property_conforms u.(ntype)) u.(nprops)
      in
      all node_conforms nodes.

  End Predicates.

  (** ---- *)
  (** *** Conforming graph *)
  (**
     #<strong>is_a_conforming_graph</strong># : wfGraphQLSchema → graphQLGraph → Bool

     The following predicate checks whether a graph conforms to a given schema.
     
     A GraphQL graph conforms to a given Schema if:
     - Its root conforms to the Schema.
     - Its edges conform to the Schema.
     - Its nodes conform to the Schema.

   *)
  Definition is_a_conforming_graph (s : wfGraphQLSchema) (graph : graphQLGraph) : bool :=
    [&& root_type_conforms s graph.(root),
        edges_conform s graph &
        nodes_conform s graph.(nodes)].

  
  (** ---- *)
  (** * Conformed GraphQL Graph *)
  (** ---- *)
  (**
     A conformed GraphQL graph is a graph which conforms to a given schema.

   **)
  Record conformedGraph (s : wfGraphQLSchema) := ConformedGraph {
                                                    graph : graphQLGraph;
                                                    _ : is_a_conforming_graph s graph
                                                  }.

  Coercion graph_of_conformed_graph s (g : conformedGraph s) := let: ConformedGraph g _ := g in g.


               
    

End Conformance.



(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.Graph.html' class="btn btn-light" role='button'> Previous ← GraphQL Graph</a>
        <a href='GraphCoQL.Response.html' class="btn btn-info" role='button'>Continue Reading → GraphQL Response </a>
    </div>#
*)