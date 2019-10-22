(* begin hide *)

From mathcomp Require Import all_ssreflect.

Require Import String.
Require Import QString.

Require Import Value.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.

Require Import Graph.
Require Import GraphConformance.

Require Import Query.
Require Import QueryAux.
Require Import QueryConformance.

Require Import Response.

Require Import QuerySemantics.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GoodBois Example</h1>
        <p class="lead">
         This file contains the GoodBois example used in the paper.
         </p>
  </div>
</div>#
 *)

Open Scope string_scope.


(** *** Values 
    ----

    We first need to define the values used in the system, the coercion
    of values and the predicate to check when a scalar value respects the
    expected type by the schema.
*)
Section Values.

  (** **** Scalar  
     ----

     Type that wraps all possible values present in the system, which in this 
     case correspond to: integer, string and floats (we model integers as nat and floats as two nats 
     for simplicity).
   *)
  Inductive Scalar : Type :=
  | VInt : nat -> Scalar
  | VString : string -> Scalar
  | VFloat : nat -> nat -> Scalar.
 
  

  (** We need to prove that Value has a decidable equality procedure,
      we hide it to unclutter the docs
   *)
  (* begin hide *)
  Notation vtype := (nat + string + (nat * nat))%type.

  Definition tuple_of_scalar (v : Scalar) :=
    match v with
    | VInt n => inl (inl n)
    | VString s => inl  (inr s)
    | VFloat n1 n2 => inr (n1, n2)
    end.

  Definition scalar_of_tuple (t : vtype) : Scalar :=
    match t with
    | inl (inl n) => VInt n
    | inl (inr s) => VString s
    | inr (n1, n2) => VFloat n1 n2
    end.

  Lemma tuple_of_scalarK : cancel tuple_of_scalar scalar_of_tuple.
  Proof. by case; case.
  Qed.
   
  Canonical scalar_eqType := EqType Scalar (CanEqMixin tuple_of_scalarK).
  (* end hide *)

  (** **** Coerce function
      ----
 
      This is the function used in the semantics to coerce 
      results into "proper" values.
      
      Since we use the same type of data everywhere, we
      actually don't need to coerce, hence coerce is the id function.
      One could imagine that a technology implementing GraphQL
      might have different types to represent their values.
   *)
  Definition coerce : Scalar -> Scalar := id.


  (** **** Is valid scalar value?
      ---- 

      The following predicate checks whether a value respects its
      expected type. 
   *)
  Variable (schema : graphQLSchema).
  
  Fixpoint check_scalar (ty : type) (v : Scalar) : bool :=
    match v with
    | VInt _ => if ty is NamedType name then
                 name == "Int"
               else
                 false
     
    | VString s => if ty is NamedType name then
                    (name == "String")
                    ||
                    if lookup_type schema name is Some (enum _ { members }) then
                      s \in members
                    else
                      false
                  else
                    false
                      
    | VFloat _ _ => if ty is NamedType name then
                     name == "Float"
                   else
                     false
                      
    end.

End Values.



(** *** GoodBois example
    ----
 *)
Section GoodBoisExample.

 
  Coercion namedType_of_string (s : string) := NamedType s.

  (** **** Schema
      ----
      First, we define the schema. 

      #<div class="row">
            <div class="col-md-6">
                 <img src="../imgs/GoodBoisExample/schema.png" class="img-fluid" alt="Schema definition">
            </div>
      </div>#

   *)
  (**
     We start by defining the scalar types used in this system.
   *)
  Let IntType := scalar "Int".
  Let StringType := scalar "String".
  Let FloatType := scalar "Float".


  (** Then the objects and interfaces *)
  Let AnimalType := interface "Animal" {
                                  [::
                                     Field "name" [::] "String";
                                     Field "age" [::] "Int";
                                     Field "friends" [::] ["Animal"]
                                    ]
                                  }.

  
  Let DogType := object "Dog" implements [:: "Animal"] {
                         [::
                            Field "name" [::] "String";
                            Field "age" [::] "Int";
                            Field "friends" [::] [ "Animal" ];
                            Field "favoriteToy" [::] "Toy"
                         ]
                       }.
  
  
  Let PigType := object "Pig" implements [:: "Animal"] {
                         [::
                            Field "name" [::] "String";
                            Field "age" [::] "Int";
                            Field "friends" [::] [ "Animal" ];
                            Field "oink" [::] "Int"
                         ]
                       }.

  Let ToyType := object "Toy" implements [::] {
                         [::
                            Field "chewiness" [::] "Float"
                         ]
                       }.


  (** The enum and union types *)
  Let GoodType := enum "Good" { [:: "BESTBOI" ; "GOODBOI" ; "OKBOI"; "BADBOI" ] }.


  Let SearchType := union "Search" { [:: "Dog"; "Pig" ; "Toy"] }.


  (** And finally the Query type *)
  Let QueryType := object "Query" implements [::] {
                           [::
                              Field "goodboi" [:: FieldArgument "goodness" "Good"] "Animal";
                              Field "search" [:: FieldArgument "text" "String"] [ "Search" ]
                           ]
                         }.


  (**
     We then define the schema as the root operation type and its type definitions.
   *)
  Let GoodBoisSchema  := GraphQLSchema "Query"  [:: IntType; StringType; FloatType;
                                                  AnimalType; DogType; PigType; ToyType;
                                                    GoodType; SearchType; QueryType].


  
  (**
     Next, we prove that the schema is well-formed by simple computation.
   *)
  Let wf_schema : GoodBoisSchema.(is_a_wf_schema). Proof. by []. Qed.
  

  (**
     Finally, we build the well-formed schema with the schema and the proof of its well-formedness.
   *)
  Let ValidGoodBoisSchema : wfGraphQLSchema := WFGraphQLSchema wf_schema.


  
  (** **** Graph 
      ----
      Secondly, we define the graph. 

      #<div class="row">
            <div class="col-md-6">
            <img src="../imgs/GoodBoisExample/graph.png" class="img-fluid" alt="Graph">
            </div>
       </div>#
        
   *)

  
  (**
     Some auxiliary definitions.
   *)
  Let name (val : string) := (@Label scalar_eqType "name" [::], SValue (VString val)).
  Let age (val : nat) :=  (@Label scalar_eqType "age" [::],  SValue (VInt val)).

  (**
     We define the nodes of the graph, starting with the root node.
   *)
  Let Root := @Node scalar_eqType "Query" [::].

 
  Let Casel := Node "Dog" [::
                             name "Casel";
                             age 10
                         ].

  Let ChrisPBacon := Node "Pig" [::
                                  name "Chris P. Bacon";
                                  age 18;
                                  (Label "oink" [::], SValue (VInt 9000))
                               ].
  
  Let Marle := Node "Dog" [::
                            name "Marle";
                            age 4
                         ].

  Let MarlesToy := Node "Toy" [::
                                (Label "chewiness" [::], SValue (VFloat 23 0))
                             ].
  
  (**
     Then the labels on edges.
   *)
  Let goodboi (val : string) := Label "goodboi" [:: ("goodness", SValue (VString val))].
  Let friends := @Label scalar_eqType "friends" [::].
  Let favoriteToy := @Label scalar_eqType "favoriteToy" [::].


  (**
     And finally the edges themselves.
   *)
  Let edges : seq (@node scalar_eqType * label * node) :=
    [::
       Root ⟜ (goodboi "BESTBOI") → Casel;
       Root ⟜ (goodboi "BADBOI") → ChrisPBacon;
       
       Casel ⟜ friends → Marle;
       Marle ⟜ friends → Casel;
       Casel ⟜ friends → ChrisPBacon;
       ChrisPBacon ⟜ friends → Casel;

       Marle ⟜ favoriteToy → MarlesToy 
    ].
    

  (**
       We define the graph as the root node and the edges in the graph.
   *)
  Let GoodBoisGraph := GraphQLGraph Root edges.


  (**
       Then, we prove that the graph conforms to the previous well-formed schema and the 
       predicate on valage values, by simple computation.
   *)
  Let graph_conforms : is_a_conforming_graph ValidGoodBoisSchema check_scalar GoodBoisGraph. Proof. by []. Qed.
    
  (**
       Finally, we build the conformed graph, using the graph and the proof of its conformance.
   *)
  Let ValidGoodBoisGraph := ConformedGraph graph_conforms.


  (** **** Query 
      ----
      
      Thirdly, we define the query.

        #<div class="row">
              <div class="col-md-4">
              <img src="../imgs/GoodBoisExample/query.png" class="img-fluid" alt="Query">
              </div>
         </div>#

   *)
  Let example_query :=
    Query None
    [::
       "goodboi" [[ [:: ("goodness", SValue (VString "BESTBOI")) ] ]] {
         [::
            "name" [[ [::] ]] ;
            "friends" [[ [::] ]] {
                        [::
                           "name" [[ [::] ]];
                           on "Dog" {
                                [::
                                   "favoriteToy" [[ [::] ]] {
                                     [::
                                        "chewiness" [[ [::] ]]
                                     ]
                                   }
                                ]
                              };
                           
                           on "Pig" {
                                [::
                                   "loudness" : "oink" [[ [::] ]]
                                ]
                              }
                        ]
                      }
         ]
       }
    ].


  (**
       We prove it conforms to the schema and has valage values, by simple computation.     
   *)
  Let example_query_conforms : query_conforms check_scalar ValidGoodBoisSchema example_query. Proof. by []. Qed.
  


  (** **** Response
      ----
      
      Fourthly, we define the response expected for the previous query.

        #<div class="row">
              <div class="col-md-4">
              <img src="../imgs/GoodBoisExample/response.png" class="img-fluid" alt="Response">
              </div>
         </div>#

   *)
  Let expected_response :=
    [::
       ("goodboi",
        {-
         [::
            ("name", Leaf (Some (VString "Casel")));
            ("friends",
             (Array
                [::
                   {-
                    [::
                       ("name", Leaf (Some (VString "Marle")));
                       ("favoriteToy",
                        {-
                         [::
                            ("chewiness", Leaf (Some (VFloat 23 0)))
                         ]
                         -}
                       )
                    ]
                    -};
                   {-
                    [::
                       ("name", Leaf (Some (VString "Chris P. Bacon")));
                       ("loudness", Leaf (Some (VInt 9000)))
                    ]
                    -}
                ]
             )
            )
         ]
         -}
       )
    ].
  

  
  (** **** Evaluation
      ----

      Lastly, we show that executing the previous query in the context of the well-formed schema, and over the conformed graph, starting from the root node, gives us the expected response (by computation).
   *)
  Goal (execute_query ValidGoodBoisSchema check_scalar ValidGoodBoisGraph coerce example_query = expected_response).
  Proof.
      by [].
  Qed.
  


End GoodBoisExample.