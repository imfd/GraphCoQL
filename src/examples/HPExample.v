(* begin hide *)

From mathcomp Require Import all_ssreflect.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Value.

Require Import GeneralTactics.
Require Import Ssromega.

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
        <h1 class="display-4">HP Example</h1>
        <p class="lead">
         This file contains the example used in [Hartig & Pérez, 2017]; schema,
         graph, query and response.
         </p>
  </div>
</div>#
 *)

Open Scope string_scope.


(** * Values 
    
    We first need to define the values used in the system, the coercion
    from a value to a JSON object, etc.
*)
Section Values.

  (* Unset Elimination Schemes. *)
  (** ---- *)
  (** *** Value 
     
     Type that wraps all possible values present in the system.
   *)
  Inductive Scalar : Type :=
  | VInt : nat -> Scalar
  | VString : string -> Scalar
  | VFloat : nat -> nat -> Scalar.
 
  

  (** We need to prove that Value has a decidable equality procedure,
      we hide it to unclutter the docs
   *)
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


  (** ---- *)
  (** *** Coerce function

      #<strong>coerce</strong># : Value → ResponseValue
 
      This is the function used in the semantics to coerce 
      results into JSON values.

      Scalar value are  simply translated as leaf values, while 
      list values have to be properly formatted as array values.
   *)
  Definition coerce : Scalar -> Scalar := id.


  (** ---- *)
  (** *** Is valid scalar value?
      #<strong>is_valid_scalar_value</strong># : type → Value → Bool

      The following predicate checks whether a given value respects 
      the given type. This is used when checking that argument values 
      are used accordingly to the schema, and similarly for graphs.

      For instance, an integer value in this scenario is valid if the 
      type is the ID type. However, a string value is valid for the type 
      String or if it refers to an enum value.
   *)
  Variable (schema : graphQLSchema). 
  Fixpoint is_valid_scalar_value (ty : type) (v : Scalar) : bool :=
    match v with
    | VInt _ => if ty is NamedType name then
                 name == "ID"
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



(** * Hartig & Pérez GraphQL Example

 *)
Section HPExample.

 
  Coercion namedType_of_string (s : string) := NamedType s.

  (** ---- *)
  (** ** Schema
      
      As described in HP, the schema is the following:

      #<img src="../imgs/HPExample/schema.png" class="img-fluid" alt="Schema definition">#

   *)
  (**
     We first define the scalar types used in this system.
   *)
  Let IDType := scalar "ID".
  Let StringType := scalar "String".
  Let FloatType := scalar "Float".


  
  Let StarshipType := object "Starship" implements [::] {
                              [:: Field "id" [::] "ID";
                                  Field "name" [::] "String";
                                  Field "length" [::] "Float"
                              ]
                            }.

  Let CharacterType := interface "Character" {
                                  [::
                                     Field "id" [::] "ID" ;
                                     Field "name" [::] "String";
                                     Field "friends" [::] [ "Character" ]
                                    ]
                                  }.

  
  Let DroidType := object "Droid" implements [:: "Character"] {
                           [::
                              Field "id" [::] "ID" ;
                              Field "name" [::] "String";
                              Field "friends" [::] [ "Character" ];
                              Field "primaryFunction" [::] "String"
                           ]
                         }.
  
  
  Let HumanType := object "Human" implements [:: "Character"] {
                           [::
                              Field "id" [::] "ID" ;
                              Field "name" [::] "String";
                              Field "friends" [::] [ "Character" ];
                              Field "starships" [::] [ "Starship" ]
                           ]
                         }.

  Let EpisodeType := enum "Episode" { [:: "NEWHOPE" ; "EMPIRE" ; "JEDI" ] }.


  Let SearchResultType := union "SearchResult" { [:: "Human" ; "Droid" ; "Starship"] }.


  Let QueryType := object "Query" implements [::] {
                           [::
                              Field "hero" [:: FieldArgument "episode" "Episode"] "Character";
                              Field "search" [:: FieldArgument "text" "String"] [ "SearchResult" ]
                           ]
                         }.


  (** ---- *)
  (**
     We define the schema as the root operation type and its type definitions.
   *)
  Let StarWarsSchema  := GraphQLSchema "Query"  [:: IDType; StringType; FloatType;  StarshipType;  CharacterType; DroidType; HumanType; EpisodeType; SearchResultType; QueryType].


  
  (** ---- *)
  (**
     We prove that the schema is well-formed by simple computation.
   *)
  Let wf_schema : StarWarsSchema.(is_a_wf_schema). Proof. by []. Qed.
  


 
  (** ---- *)
  (**
     We build the well-formed schema with the schema, the proof of its well-formedness
     and the predicate that helps determine when a value respects the type.
   *)
  Let ValidStarWarsSchema : wfGraphQLSchema := WFGraphQLSchema wf_schema.

  (** ---- *)
  (** ** Graph 
        
      We then define the graph displayed in HP.
        
      #<img src="../imgs/HPExample/graph.png" class="img-fluid" alt="Graph">#
        
   *)

  (**
     We first define the root node.
   *)
  Let Root := @Node scalar_eqType "Query" [::].

  (**
     Some auxiliary definitions to define the graph
   *)
  Let id (val : nat) :=  (@Label scalar_eqType "id" [::],  SValue (VInt val)).
  Let name (val : string) := (@Label scalar_eqType "name" [::], SValue (VString val)).

  (**
     We define the nodes of the graph.
   *)
  Let Falcon := Node "Starship" [::
                                  id 3000;
                                  name "Falcon"; 
                                  (Label "length" [::], SValue (VFloat 34 37))
                               ].

  Let Luke := Node "Human" [::
                             id 1000;
                             name "Luke"
                          ].

  Let Han := Node "Human" [::
                            (Label "id" [::], SValue (VInt 1002));
                            (Label "name" [::], SValue (VString "Han"))
                         ].
  
  Let Artoo := Node "Droid" [::
                              (Label "id" [::], SValue (VInt 2001));
                              (Label "name" [::], SValue (VString "R2-D2"));
                              (Label "primaryFunction" [::], SValue (VString "Astromech"))
                           ].

  (**
     Then the labelds on edges.
   *)
  Let search := Label "search" [:: ("text", SValue (VString "L"))].
  Let hero (val : string) := Label "hero" [:: ("episode", SValue (VString val))].
  Let friends := @Label scalar_eqType "friends" [::].
  Let starships := @Label scalar_eqType "starships" [::].


  (**
     And finally the edges themselves.
   *)
  Let edges : seq (@node scalar_eqType * label * node) :=
    [::
       Root ⟜ search → Falcon;
       Root ⟜ search → Luke;
       Root ⟜ (hero "EMPIRE") → Luke;
       Root ⟜ (hero "NEWHOPE") → Artoo;
       
       Luke ⟜ friends → Artoo;
       Luke ⟜ friends → Han;
       
       Artoo ⟜ friends → Luke;

       Han ⟜ friends → Luke;

       Han ⟜ starships → Falcon
    ].
    

  (** ---- *)
  (**
       We define the graph as the root node and the edges in the graph.
   *)
  Let StarWarsGraph := GraphQLGraph Root edges.


  (** ---- *)
  (**
       We prove that the graph conforms to the previous well-formed schema, by simple computation.
   *)
  Let graph_conforms : is_a_conforming_graph ValidStarWarsSchema is_valid_scalar_value StarWarsGraph. Proof. by []. Qed.
    

  (** ---- *)
  (**
       We build the conformed graph, using the graph and the proof of its conformance.
   *)
  Let ValidStarWarsGraph := ConformedGraph graph_conforms.


  (** ---- *)
  (** ** Query 
        
        We then define the query.

        #<img src="../imgs/HPExample/query.png" class="img-fluid" alt="Query">#

   *)
  Let example_query :=
    Query None
    [::
       "hero" [[ [:: ("episode", SValue (VString "EMPIRE")) ] ]] {
         [::
            "name" [[ [::] ]] ;
            "friends" [[ [::] ]] {
                        [::
                           on "Human" {
                             [::
                                "humanFriend" : "name" [[ [::] ]] ;
                                "starships" [[ [::] ]] {
                                              [::
                                                 "starship" : "name" [[ [::] ]] ;
                                                 "length" [[ [::] ]]
                                              ]
                                            }
                             ]
                           } ;
                           
                           on "Droid" {
                                [::
                                   "droidFriend" : "name" [[ [::] ]] ;
                                   "primaryFunction" [[ [::] ]]
                                ]
                              }
                        ]
                      }
         ]
       }
    ].


  (** ---- *)
  (**
       We prove it conforms to the schema by simple computation.     
   *)
  Let example_query_conforms : query_conforms is_valid_scalar_value ValidStarWarsSchema example_query. Proof. by []. Qed.
  


  (** ---- *)
  (** ** Response
        
        We define the response expected for the previous query.

        #<img src="../imgs/HPExample/response.png" class="img-fluid" alt="Response">#

   *)
  Let expected_response :=
    [::
       ("hero",
        {-
         [::
            ("name", Leaf (Some (VString "Luke")));
            ("friends",
             Array
               [::
                  {-
                   [::
                      ("droidFriend", Leaf (Some (VString "R2-D2")));
                      ("primaryFunction", Leaf (Some (VString "Astromech")))
                   ]
                   -};
                  {-
                   [::
                      ("humanFriend", Leaf (Some (VString "Han")));
                      ("starships",
                       Array
                         [::
                            {-
                             [::
                                ("starship", Leaf (Some (VString "Falcon")));
                                ("length", Leaf (Some (VFloat 34 37)))
                             ]
                             -}
                         ]
                      )
                   ]
                   -}
               ]
            )
         ]
         -}
       )
    ].
 

  
  (** ---- *)
  (**
     Finally, we show that executing the previous query in the context of the well-formed schema, and over the conformed graph, starting from the root node, gives us the expected response.
   *)
  Goal (execute_query ValidStarWarsSchema is_valid_scalar_value ValidStarWarsGraph coerce example_query = expected_response).
  Proof.
      by [].
  Qed.
  


End HPExample.

