(* begin hide *)

From mathcomp Require Import all_ssreflect.

From Equations Require Import Equations.

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
Require Import QueryTactics.

Require Import Response.

Require Import QuerySemantics.
Require Import QuerySemanticsLemmas.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GraphQLJS Example</h1>
        <p class="lead">
         This file contains the <a href='https://github.com/graphql/graphql-js/tree/master/src/__tests__'>Star Wars example</a>
         used in the GraphQL reference implementation.         
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

  Unset Elimination Schemes.

  (** **** Scalar  
     ----
     
     In this example, the only value used are strings.    
   *)
  Notation Scalar := string.


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
  Definition is_valid_scalar_value (ty : type) (v : Scalar) : bool :=
    if ty is NamedType name then
      (name == "String")
      ||
      if lookup_type schema name is Some (enum _ { members }) then
        v \in members
      else
        false
    else
      false.

End Values.




(** *** Star Wars Example
    ----
 *)
Section Example.

 
  Coercion namedType_of_string (s : string) := NamedType s.

  (** **** Schema
      ----
      First, we define the schema. 

       #<div class="row">
        <div class="col-md-5">
          <img src="../imgs/GQLJSExample/schema1.png" class="img-fluid" alt="Schema definition">
        </div>
        <div class="col-md-5">
          <img src="../imgs/GQLJSExample/schema2.png" class="img-fluid" alt="Schema definition">
        </div>
      
      </div>#
   *)
  (**
     We start by defining the scalar types used in this system.
   *)
  Let StringType := scalar "String".


  (** Then the left hand side *)
  Let EpisodeType := enum "Episode" { [:: "NEWHOPE" ; "EMPIRE" ; "JEDI" ] }.

  (* The secret backstory is actually implemented as a function that throws error, so
     we omit it for now *)
  Let CharacterType := interface "Character" {
                                  [::
                                     Field "id" [::] "String" ;
                                     Field "name" [::] "String";
                                     Field "friends" [::] [ "Character" ];
                                     Field "appearsIn" [::] [ "Episode" ]
                                     (* Field "secretBackstory" [::] "String" *)
                                    ]
                                  }.

  Let HumanType := object "Human" implements [:: "Character"] {
                           [::
                              Field "id" [::] "String" ;
                              Field "name" [::] "String";
                              Field "friends" [::] [ "Character" ];
                              Field "appearsIn" [::] [ "Episode" ];
                              (* Field "secretBackstory" [::] "String"; *)
                              Field "homePlanet" [::] "String"
                           ]
                         }.

  (** And the right hand side *)
  Let DroidType := object "Droid" implements [:: "Character"] {
                           [::
                              Field "id" [::] "String" ;
                              Field "name" [::] "String";
                              Field "friends" [::] [ "Character" ];
                              Field "appearsIn" [::] [ "Episode" ];
                              (* Field "secretBackstory" [::] "String"; *)
                              Field "primaryFunction" [::] "String"
                           ]
                         }.


  Let QueryType := object "Query" implements [::] {
                           [::
                              Field "hero" [:: FieldArgument "episode" "Episode"] "Character";
                              Field "human" [:: FieldArgument "id" "String"] "Human";
                              Field "droid" [:: FieldArgument "id" "String"] "Droid"
                           ]
                         }.


  (**
     We then define the schema as the root operation type and its type definitions.
   *)
  Let StarWarsSchema  := GraphQLSchema "Query"  [:: StringType; EpisodeType; CharacterType; HumanType; DroidType; QueryType].


  
  
  (**
     Followed by a proof that the schema is well-formed, by simple computation.
   *)
  Let wf_schema : StarWarsSchema.(is_a_wf_schema). Proof. by []. Qed.
  


  (**
     Finally, we build the well-formed schema with the schema and the proof of its well-formedness.
   *)
  Let ValidStarWarsSchema : wfGraphQLSchema := WFGraphQLSchema wf_schema.

  
  (** **** Graph 
      ----
      Secondly, we define the graph. 

        
   *)

  (**
     We define the nodes of the graph.
   *)
  Let Luke := Node "Human" [::
                             (Label "id" [::], SValue "1000");
                             (Label "name" [::], SValue "Luke Skywalker");
                             (Label "appearsIn" [::], LValue [::
                                                                SValue "NEWHOPE";
                                                                SValue "EMPIRE";
                                                                SValue "JEDI"
                                                             ]
                             );
                             (Label "homePlanet" [::], SValue "Tatooine")
                          ].
  
  Let Vader := Node "Human" [::
                              (Label "id" [::], SValue "1001");
                              (Label "name" [::], SValue "Darth Vader");
                              (Label "appearsIn" [::], LValue [::
                                                                 SValue "NEWHOPE";
                                                                 SValue "EMPIRE";
                                                                 SValue "JEDI"
                                                              ]
                              );
                              (Label "homePlanet" [::], SValue "Tatooine")
                           ].
  
  Let Han := Node "Human" [::
                            (Label "id" [::], SValue "1002");
                            (Label "name" [::], SValue "Han Solo");
                            (Label "appearsIn" [::], LValue [::
                                                               SValue "NEWHOPE";
                                                               SValue "EMPIRE";
                                                               SValue "JEDI"
                                                            ]
                            )
                         ].
  
  Let Leia := Node "Human" [::
                             (Label "id" [::], SValue "1003");
                             (Label "name" [::], SValue "Leia Organa");
                             (Label "appearsIn" [::], LValue [::
                                                                SValue "NEWHOPE";
                                                                SValue "EMPIRE";
                                                                SValue "JEDI"
                                                             ]
                             );
                             (Label "homePlanet" [::], SValue "Alderaan")
                          ].
  
  Let Tarkin := Node "Human" [::
                               (Label "id" [::], SValue "1004");
                               (Label "name" [::], SValue "Wilhuff Tarkin");
                               (Label "appearsIn" [::], LValue [::
                                                                  SValue "NEWHOPE"
                                                               ]
                               )
                            ].
  
  Let Threepio := Node "Droid" [::
                                 (Label "id" [::], SValue "2000");
                                 (Label "name" [::], SValue "C3-PO");
                                 (Label "appearsIn" [::], LValue [::
                                                                    SValue "NEWHOPE";
                                                                    SValue "EMPIRE";
                                                                    SValue "JEDI"
                                                                 ]
                                 );
                                 (Label "primaryFunction" [::], SValue "Protocol")
                              ].

  
  Let Artoo := Node "Droid" [::
                              (Label "id" [::], SValue "2001");
                              (Label "name" [::], SValue "R2-D2");
                              (Label "appearsIn" [::], LValue [::
                                                                 SValue "NEWHOPE";
                                                                 SValue "EMPIRE";
                                                                 SValue "JEDI"
                                                              ]
                              );
                              (Label "primaryFunction" [::], SValue "Astromech")
                           ].


  (** The root node *)
  Let Root := @Node string_eqType "Query" [::].

  (**
     Then the labels on edges.
   *)
  Let human (id : string) := @Label string_eqType "human" [:: ("id", SValue id)].

  Let droid (id : string) := @Label string_eqType "droid" [:: ("id", SValue id)].

  Let hero (episode : string) := (Label "hero" [:: ("episode", SValue episode)]).
  
  Let friends := @Label string_eqType "friends" [::].

  Let appearsIn := @Label string_eqType "appearsIn" [::].


  (**
     And finally the edges themselves.
   *)
  Let edges : seq (@node string_eqType * label * node) :=
    [::
       (* Heroes *)
       pair (pair Root (hero "EMPIRE")) Luke;

       pair (pair Root (Label "hero" [::])) Artoo;

       pair (pair Root (hero "NEWHOPE")) Artoo;
       
       pair (pair Root (hero "JEDI")) Artoo;

       (* Character by id *)
       pair (pair Root (human "1000")) Luke;
       pair (pair Root (human "1001")) Vader;
       pair (pair Root (human "1002")) Han;
       pair (pair Root (human "1003")) Leia;
       pair (pair Root (human "1000")) Tarkin;
       
       pair (pair Root (droid "2000")) Threepio;
       pair (pair Root (droid "2001")) Artoo;
       
       (* Luke's friends *)
       pair (pair Luke friends) Han;
       pair (pair Luke friends) Leia;
       pair (pair Luke friends) Threepio;
       pair (pair Luke friends) Artoo;
       
       (* Vader's friends *)
       pair (pair Vader friends) Tarkin;

       (* Han's friends *)
       pair (pair Han friends) Luke;
       pair (pair Han friends) Leia;
       pair (pair Han friends) Artoo;

       (* Leia's friends *)
       pair (pair Leia friends) Luke;
       pair (pair Leia friends) Han;
       pair (pair Leia friends) Threepio;
       pair (pair Leia friends) Artoo;

       (* Tarkin's friends *)
       pair (pair Tarkin friends) Vader;

       
       (* Threepio's friends *)
       pair (pair Threepio friends) Luke;
       pair (pair Threepio friends) Han;
       pair (pair Threepio friends) Leia;
       pair (pair Threepio friends) Artoo;

       (* Artoo's friends *)
       pair (pair Artoo friends) Luke;
       pair (pair Artoo friends) Han;
       pair (pair Artoo friends) Leia

    ].


  (**
       We define the graph as the root node and the edges in the graph.
   *)
  Let StarWarsGraph := GraphQLGraph Root edges.



  (**
       Then, we prove that the graph conforms to the previous well-formed schema and the 
       predicate on valid values, by simple computation.
   *) 
  Let graph_conforms : is_a_conforming_graph ValidStarWarsSchema is_valid_scalar_value StarWarsGraph.
  Proof.
      by [].
  Qed.
    

  (**
       Finally, we build the conformed graph, using the graph and the proof of its conformance.
   *)
  Let ValidStarWarsGraph := ConformedGraph graph_conforms.




  (** **** Query 
        
        We then define the queries.
   *)

  (* Simple commodity *)
  Let val (v : string) := Leaf (Some v).
  
  (** **** #<a href='https://github.com/graphql/graphql-js/blob/master/src/__tests__/starWarsQuery-test.js##L11'>Basic Queries</a>#
      ----
   *)
  
  (** It correctly identifies R2-D2 as the hero of the Star Wars Saga.
      ----
   *)
  Let q1 := @Query string_eqType (Some "HeroNameQuery")
                  [::
                     "hero" [[ [::] ]] {
                       [::
                          "name" [[ [::] ]]
                       ]
                     }
                  ].

  (** We prove it is a valid query *)
  Let q1_conforms : query_conforms is_valid_scalar_value ValidStarWarsSchema q1. by []. Qed.
  
  Let result1 :=   [::
                     ("hero",
                      Response.Object
                        [::
                           ("name", val "R2-D2")
                        ]
                     )
                  ].

  (** And that it evaluates correctly *)
  Goal execute_query ValidStarWarsSchema is_valid_scalar_value ValidStarWarsGraph coerce q1 = result1.
       by [].
   Qed.

  (** ---- *)
   (** It allows us to query for the ID and friends of R2-D2
       ----
    *)  

   Let q2 := @Query string_eqType (Some "HeroNameAndFriendsQuery")
                  [::
                     "hero" [[ [::] ]] {
                       [::
                          "id" [[ [::] ]];
                          "name" [[ [::] ]];
                          "friends" [[ [::] ]] {
                                      [::
                                         "name" [[ [::] ]]
                                      ]
                                    }
                       ]
                     }
                  ].

   (** We prove it is a valid query *) 
   Let q2_conforms : query_conforms is_valid_scalar_value ValidStarWarsSchema q2. by []. Qed.

   Let result2 :=   [::
                     ("hero",
                      Response.Object
                        [::
                           ("id", val "2001");
                           ("name", val "R2-D2");
                           ("friends",
                            Array
                              [::
                                 Response.Object
                                 [::
                                    ("name", val "Luke Skywalker")
                                 ];
                                 Response.Object
                                   [::
                                      ("name", val "Han Solo")
                                   ];
                                 Response.Object
                                   [::
                                      ("name", val "Leia Organa")
                                   ]
                              ]
                           )
                        ]
                     )
                  ].

   (** And that it evaluates correctly *)
   Goal execute_query ValidStarWarsSchema is_valid_scalar_value ValidStarWarsGraph coerce q2 = result2.
       by [].
   Qed.


  (** **** #<a href='https://github.com/graphql/graphql-js/blob/master/src/__tests__/starWarsQuery-test.js##L86'>Nested Queries</a>#
      ----
   *)
  (** It allows us to query for the friends of friends of R2-D2
      ----
   *)

   Let q3 := @Query string_eqType (Some "HeroNameAndFriendsQuery")
                   [::
                      "hero" [[ [::] ]] {
                        [::
                           "name" [[ [::] ]];
                           "friends" [[ [::] ]] {
                                       [::
                                          "name" [[ [::] ]];
                                          "appearsIn" [[ [::] ]];
                                          "friends" [[ [::] ]] {
                                                      [::
                                                         "name" [[ [::] ]]
                                                      ]
                                                    }
                                       ]
                                     }
                       ]
                     }
                   ].

   (** We prove it is a valid query *) 
   Let q3_conforms : query_conforms is_valid_scalar_value ValidStarWarsSchema q3. by []. Qed.


   Let result3 := [::
                    ("hero",
                     Response.Object
                       [::
                          ("name", val "R2-D2");
                          
                          ("friends",
                           Array
                             [::
                                Response.Object
                                [::
                                   ("name", val "Luke Skywalker");
                                   ("appearsIn", Array [:: val "NEWHOPE";
                                                          val "EMPIRE";
                                                          val "JEDI"
                                                       ]
                                   );
                                   ("friends",
                                    Array
                                      [::
                                         Response.Object
                                         [::
                                            ("name", val "Han Solo")
                                         ];
                                         Response.Object
                                           [::
                                              ("name", val "Leia Organa")
                                           ];
                                         Response.Object
                                           [::
                                              ("name", val "C3-PO")
                                           ];
                                         Response.Object
                                           [::
                                              ("name", val "R2-D2")
                                           ]
                                      ]
                                   )
                                ];
                                Response.Object
                                  [::
                                     ("name", val "Han Solo");
                                     ("appearsIn", Array [:: val "NEWHOPE";
                                                            val "EMPIRE";
                                                            val "JEDI"
                                                         ]
                                     );
                                     ("friends",
                                      Array
                                        [::
                                           Response.Object
                                           [::
                                              ("name", val "Luke Skywalker")
                                           ];
                                           Response.Object
                                             [::
                                                ("name", val "Leia Organa")
                                             ];
                                           Response.Object
                                             [::
                                                ("name", val "R2-D2")
                                             ]
                                        ]
                                     )
                                  ];
                                Response.Object
                                  [::
                                     ("name", val "Leia Organa");
                                     ("appearsIn", Array [:: val "NEWHOPE";
                                                            val "EMPIRE";
                                                            val "JEDI"
                                                         ]
                                     );
                                     ("friends",
                                      Array
                                        [::
                                           Response.Object
                                           [::
                                              ("name", val "Luke Skywalker")
                                           ];
                                           
                                           Response.Object
                                             [::
                                                ("name", val "Han Solo")
                                             ];
                                           Response.Object
                                             [::
                                                ("name", val "C3-PO")
                                             ];
                                           Response.Object
                                             [::
                                                ("name", val "R2-D2")
                                             ]
                                        ]
                                     )
                                  ]
                             ]
                          )
                       ]
                    )
                 ].
   (** And that it evaluates correctly *)
   Goal execute_query ValidStarWarsSchema is_valid_scalar_value ValidStarWarsGraph coerce q3 = result3.
       by [].
   Qed.

   
   (** **** #<a href='https://github.com/graphql/graphql-js/blob/master/src/__tests__/starWarsQuery-test.js##L166'>Using IDs and query parameters to refetch objects</a>#
       ----
    *)
   (** It allows us to query for Luke Skywalker directly, using his ID
       ----
    *)   
   Let q4 := @Query string_eqType (Some "FetchLukeQuery")
                   [::
                      "human" [[ [:: ("id", SValue "1000")] ]] {
                        [::
                           "name" [[ [::] ]]
                        ]
                      }
                   ].
   
   (** We prove it is a valid query *)
   Let q4_conforms : query_conforms is_valid_scalar_value ValidStarWarsSchema q4. by []. Qed.

   Let result4 := [::
                    ("human",
                     Response.Object
                       [::
                          ("name", val "Luke Skywalker")
                       ]
                    )
                 ].
   (** And that it evaluates correctly *)
   Goal execute_query ValidStarWarsSchema is_valid_scalar_value ValidStarWarsGraph coerce q4 = result4.
       by [].
   Qed.


   (** ---- *)
   (** Pass an invalid ID to get null back.
       ----
    *)
 
  Let q5 := @Query string_eqType (Some "humanQuery")
                   [::
                      "human" [[ [:: ("id", SValue "not a valid id")] ]] {
                        [::
                           "name" [[ [::] ]]
                        ]
                      }
                   ].

  (** We prove it is a valid query *)
   Let q5_conforms : query_conforms is_valid_scalar_value ValidStarWarsSchema q5. by []. Qed.

   Let result5 := [::
                    ("human", (@Leaf string_eqType None))
                 ].
   (** And that it evaluates correctly *)
   Goal execute_query ValidStarWarsSchema is_valid_scalar_value ValidStarWarsGraph coerce q5 = result5.
       by [].
   Qed.



   (** **** #<a href='https://github.com/graphql/graphql-js/blob/master/src/__tests__/starWarsQuery-test.js##L241'>Using aliases to change the key in the response</a>#
       ----
    *)
   (** Allows us to query for Luke, changing his key with an alias
       ----
    *)

   Let q6 := @Query string_eqType (Some "FetchLukeAliased")
                   [::
                      "luke":"human" [[ [:: ("id", SValue "1000")] ]] {
                        [::
                           "name" [[ [::] ]]
                        ]
                      }
                   ].

   (** We prove it is a valid query *)
   Let q6_conforms : query_conforms is_valid_scalar_value ValidStarWarsSchema q6. by []. Qed.

   Let result6 := [::
                    ("luke",
                     Response.Object
                       [::
                          ("name", val "Luke Skywalker")
                       ]
                    )
                 ].
   (** And that it evaluates correctly *)
   Goal execute_query ValidStarWarsSchema is_valid_scalar_value ValidStarWarsGraph coerce q6 = result6.
       by [].
   Qed.

   
   (** ---- *)
   (** Allows us to query for both Luke and Leia, using two root fields and an alias
       ----
    *)
   Let q7 := @Query string_eqType (Some "FetchLukeAndLeiaAliased")
                   [::
                      "luke":"human" [[ [:: ("id", SValue "1000")] ]] {
                                       [::
                                          "name" [[ [::] ]]
                                       ]
                                     };
                      "leia":"human" [[ [:: ("id", SValue "1003")] ]] {
                                       [::
                                          "name" [[ [::] ]]
                                       ]
                                     }
                   ].

   (** We prove it is a valid query *)
   Let q7_conforms : query_conforms is_valid_scalar_value ValidStarWarsSchema q7. by []. Qed.

   Let result7 := [::
                    ("luke",
                     Response.Object
                       [::
                          ("name", val "Luke Skywalker")
                       ]
                    );
                    ("leia",
                     Response.Object
                       [::
                          ("name", val "Leia Organa")
                       ]
                    )
                 ].
   (** And that it evaluates correctly *)
   Goal execute_query ValidStarWarsSchema is_valid_scalar_value ValidStarWarsGraph coerce q7 = result7.
       by [].
   Qed.



   (** **** #<a href='https://github.com/graphql/graphql-js/blob/master/src/__tests__/starWarsQuery-test.js##L285'>Uses fragments to express more complex queries</a>#
       ----
    *)

   (** Allows us to query using duplicated content
       ----
    *)
   Let q8 := @Query string_eqType (Some "DuplicateFields")
                   [::
                      "luke":"human" [[ [:: ("id", SValue "1000")] ]] {
                                       [::
                                          "name" [[ [::] ]];
                                          "homePlanet" [[ [::] ]]
                                       ]
                                     };
                      "leia":"human" [[ [:: ("id", SValue "1003")] ]] {
                                       [::
                                          "name" [[ [::] ]];
                                          "homePlanet" [[ [::] ]]
                                       ]
                                     }
                   ].

   (** We prove it is a valid query *)
   Let q8_conforms : query_conforms is_valid_scalar_value ValidStarWarsSchema q8. by []. Qed.

   Let result8 := [::
                    ("luke",
                     Response.Object
                       [::
                          ("name", val "Luke Skywalker");
                          ( "homePlanet", val "Tatooine")
                       ]
                    );
                    ("leia",
                     Response.Object
                       [::
                          ("name", val "Leia Organa");
                          ("homePlanet", val "Alderaan")
                       ]
                    )
                 ].
   (** And that it evaluates correctly *)
   Goal execute_query ValidStarWarsSchema is_valid_scalar_value ValidStarWarsGraph coerce q8 = result8.
       by [].
   Qed.


   (** ---- *)
   (** Allows us to use a fragment to avoid duplicating content
       ----
       Not doing it bc fragments are not implemented. Instead, checking that inline fragments 
       are still ok.
    *)

   Let q9 := @Query string_eqType (Some "DuplicateFields")
                   [::
                      "luke":"human" [[ [:: ("id", SValue "1000")] ]] {
                                       [::
                                          on "Human" {
                                            [::
                                               "name" [[ [::] ]];
                                               "homePlanet" [[ [::] ]]
                                            ]
                                          }
                                       ]
                                     };
                      "leia":"human" [[ [:: ("id", SValue "1003")] ]] {
                                       [::
                                          on "Human" {
                                            [::
                                               "name" [[ [::] ]];
                                               "homePlanet" [[ [::] ]]
                                            ]
                                          }
                                       ]
                                     }
                   ].

   (** We prove it is a valid query *)
   Let q9_conforms : query_conforms is_valid_scalar_value ValidStarWarsSchema q9. by []. Qed.

   Let result9 := [::
                    ("luke",
                     Response.Object
                       [::
                          ("name", val "Luke Skywalker");
                          ( "homePlanet", val "Tatooine")
                       ]
                    );
                    ("leia",
                     Response.Object
                       [::
                          ("name", val "Leia Organa");
                          ("homePlanet", val "Alderaan")
                       ]
                    )
                 ].
   (** And that it evaluates correctly *)
   Goal execute_query ValidStarWarsSchema is_valid_scalar_value ValidStarWarsGraph coerce q9 = result9.
       by [].
   Qed.


End Example.
     