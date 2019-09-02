(* begin hide *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Schema.
Require Import SchemaAux.

Require Import SchemaWellFormedness.


Require Import Graph.
Require Import GraphAux.

Require Import GraphConformance.


Require Import Query.
Require Import QueryAux.

Require Import QueryConformance.


Require Import Response.

Require Import NRGTNF.


Require Import QueryNormalization.


Require Import SeqExtra.
Require Import QueryTactics.

Require Import QuerySemantic.

Open Scope string_scope.

(* end hide *)


(** This file includes some examples of schemas, graphs and queries. 
    The base schema is the one used in [Hartig & Pérez, 2017];

    Section HP includes the whole example used in [Hartig & Pérez, 2017],
    while the other sections may vary.
 **)
Section Example.
 
  Coercion namedType_of_string (s : string) := NamedType s.
  
  Let IDType := Scalar "ID".
  Let StringType := Scalar "String".
  Let FloatType := Scalar "Float".


  
  Let StarshipType := Object "Starship" implements [::] {
                              [:: Schema.Field "id" [::] "ID";
                                  Schema.Field "name" [::] "String";
                                  Schema.Field "length" [::] "Float"
                              ]
                            }.

  Let CharacterType := Interface "Character" {
                                  [::
                                     Schema.Field "id" [::] "ID" ;
                                     Schema.Field "name" [::] "String";
                                     Schema.Field "friends" [::] [ "Character" ]
                                    ]
                                  }.

  
  Let DroidType := Object "Droid" implements [:: "Character"] {
                           [::
                              Schema.Field "id" [::] "ID" ;
                              Schema.Field "name" [::] "String";
                              Schema.Field "friends" [::] [ "Character" ];
                              Schema.Field "primaryFunction" [::] "String"
                           ]
                         }.
  
  
  Let HumanType := Object "Human" implements [:: "Character"] {
                           [::
                              Schema.Field "id" [::] "ID" ;
                              Schema.Field "name" [::] "String";
                              Schema.Field "friends" [::] [ "Character" ];
                              Schema.Field "starships" [::] [ "Starship" ]
                           ]
                         }.

  Let EpisodeType := Enum "Episode" { [:: "NEWHOPE" ; "EMPIRE" ; "JEDI" ] }.


  Let SearchResultType := Union "SearchResult" { [:: "Human" ; "Droid" ; "Starship"] }.


  Let QueryType := Object "Query" implements [::] {
                           [::
                              Schema.Field "hero" [:: FieldArgument "episode" "Episode"] "Character";
                              Schema.Field "search" [:: FieldArgument "text" "String"] [ "SearchResult" ]
                           ]
                         }.

  Let schema  := GraphQLSchema "Query"  [:: IDType; StringType; FloatType;  StarshipType;  CharacterType; DroidType; HumanType; EpisodeType; SearchResultType; QueryType].


  Lemma sdf : schema.(is_wf_schema).
  Proof. by []. Qed.
  



  Let wf_schema : @wfGraphQLSchema string_eqType := WFGraphQLSchema (fun n v => true) sdf.
  
  Section HP.


    (* Close Scope query_eval. *)
    
    Let edges : seq (node * fld * node) :=
      [::
         pair (pair (Node "Query" [::])
                    (Graph.Field "search" [:: (pair "text" "L")]))
         (Node "Starship" [::
                             (pair (Graph.Field "id" [::])  (inl "3000"));
                             (pair (Graph.Field "name" [::]) (inl "Falcon")); 
                             (pair (Graph.Field "length" [::]) (inl "34.37"))
         ]);
         pair (pair (Node "Query" [::])
                    (Graph.Field "search" [:: (pair "text" "L")]))
              (Node "Human" [::
                               pair (Graph.Field "id" [::]) (inl "1000");
                               pair (Graph.Field "name" [::]) (inl "Luke")
              ]);
         pair (pair (Node "Query" [::])
                    (Graph.Field "hero" [:: pair "episode" "EMPIRE"]))
              (Node "Human" [::
                               pair (Graph.Field "id" [::]) (inl "1000");
                               pair (Graph.Field "name" [::]) (inl "Luke")
              ]);
         pair (pair (Node "Query" [::])
                    (Graph.Field "hero" [:: pair "episode" "NEWHOPE"]))
              (Node "Droid" [::
                               (pair (Graph.Field "id" [::]) (inl "2001"));
                               (pair (Graph.Field "name" [::]) (inl "R2-D2"));
                               (pair (Graph.Field "primaryFunction" [::]) (inl "Astromech"))
              ]);
         
         pair (pair (Node "Human" [::
                                     pair (Graph.Field "id" [::]) (inl "1000");
                                     pair (Graph.Field "name" [::]) (inl "Luke")
                    ])
                    (Graph.Field "friends" [::]))
              (Node "Droid" [::
                               (pair (Graph.Field "id" [::]) (inl "2001"));
                               (pair (Graph.Field "name" [::]) (inl "R2-D2"));
                               (pair (Graph.Field "primaryFunction" [::]) (inl "Astromech"))
              ]);

         pair (pair (Node "Droid" [::
                                     (pair (Graph.Field "id" [::]) (inl "2001"));
                                     (pair (Graph.Field "name" [::]) (inl "R2-D2"));
                                     (pair (Graph.Field "primaryFunction" [::]) (inl "Astromech"))
                    ])
                    (Graph.Field "friends" [::]))
              (Node "Human" [::
                               pair (Graph.Field "id" [::]) (inl "1000");
                               pair (Graph.Field "name" [::]) (inl "Luke")
              ]);
         
         pair (pair (Node "Human" [::
                                     pair (Graph.Field "id" [::]) (inl "1000");
                                     pair (Graph.Field "name" [::]) (inl "Luke")
                    ])
                    (Graph.Field "friends" [::]))
              (Node "Human" [::
                               pair (Graph.Field "id" [::]) (inl "1002");
                               pair (Graph.Field "name" [::]) (inl "Han")
              ]);
         
         pair (pair (Node "Human" [::
                                     pair (Graph.Field "id" [::]) (inl "1002");
                                     pair (Graph.Field "name" [::]) (inl "Han")
                    ])
                    (Graph.Field "friends" [::]))
              (Node "Human" [::
                               pair (Graph.Field "id" [::]) (inl "1000");
                               pair (Graph.Field "name" [::]) (inl "Luke")
              ]);
         
         pair (pair (Node "Human" [::
                                     pair (Graph.Field "id" [::]) (inl "1002");
                                     pair (Graph.Field "name" [::]) (inl "Han")
                    ])
                    (Graph.Field "starships" [::]))
              (Node "Starship" [:: (pair (Graph.Field "id" [::]) (inl "3000"));
                                  (pair (Graph.Field "name" [::]) (inl "Falcon")); 
                                  (pair (Graph.Field "length" [::]) (inl "34.37"))])
      ].
    
    
    Let r : @node string_eqType := Node "Query" [::].
    
    
    Let g := GraphQLGraph r edges.


    Lemma rtc : root_type_conforms wf_schema g.
    Proof.    by [].  Qed.

    
    Lemma ec : edges_conform wf_schema g.
    Proof.
      by [].
    Qed.

    Lemma fc : fields_conform wf_schema g.
    Proof.
        by [].
    Qed.
    
    Lemma nhot : nodes_have_object_type wf_schema g.
    Proof.
      by [].
    Qed.
    

    Let wf_graph := ConformedGraph rtc ec fc nhot.


    
    Let q :=
      [::
         "hero" [[ [:: (pair "episode" "EMPIRE") ] ]] {
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


    (* Transparent find_fields_with_response_name have_compatible_response_shapes. *)
  Lemma qbc : queries_conform  wf_schema wf_schema.(query_type) q.
  Proof.
      by [].
  Qed.
        




  Let query_response :=
    [::
       (pair "hero"
             {-
                [::
                   (pair "name" (Leaf (Some "Luke")));
                   (pair "friends"
                         (Array
                            [::
                               {-
                                [::
                                   (pair "droidFriend" (Leaf (Some "R2-D2")));
                                   (pair "primaryFunction" (Leaf (Some "Astromech")))
                                ]
                                -};
                               {-
                                [::
                                   (pair "humanFriend" (Leaf (Some "Han")));
                                   (pair "starships"
                                         (Array
                                            [::
                                               {-
                                                [::
                                                   (pair "starship" (Leaf (Some "Falcon")));
                                                   (pair "length" (Leaf (Some "34.37")))
                                                ]
                                                -}
                                            ]
                                         )
                                   )
                                ]
                                -}
                            ]
                         )
                   )
                ]
             -}
       )
    ].
     


                
  Example ev_query_eq_response :  (execute_selection_set wf_schema wf_graph wf_graph.(root) q) = query_response.
  Proof.
      by [].
  Qed.

    

    Let q' := [::
                ("hero" [[ [:: (pair "episode" "EMPIRE") ] ]] {
                          [::
                             ("name" [[ [::] ]]);
                             ("name" [[ [::] ]]);
                             ("id" [[ [::] ]]);
                             ("name" [[ [::] ]])
                          ]
                        }
                )
             ].
    
             
     Lemma qbc' : queries_conform wf_schema wf_schema.(query_type) q'.
     Proof. by []. Qed.
  


     Goal (wf_schema, wf_graph ⊢  ⟦ q' ⟧ˢ in wf_graph.(root) =
            [::
               (pair "hero" {-
                             [::
                                (pair "name" (Leaf (Some "Luke")));
                                (pair "id" (Leaf (Some "1000")))
                             ]
                             -}
               )
          ]).
         by [].
     Qed.
    
    
  End HP.
  

  Section WrongGraph.
    (** Some examples of graph's not conforming to the schema **)

    Let r : @node string_eqType := Node "Query" [::].
        
    (** Root node does not have same type as query type **)
    Let edges1 : seq (@node string_eqType * @fld string_eqType * @node string_eqType) := [::].
    
    Let r1 : @node string_eqType := Graph.Node "Human" [::].
    
    Let g := GraphQLGraph r1 edges1.

    Example rtNc : ~ root_type_conforms wf_schema g.
    Proof. by []. Qed.



    
    (** Arguments are incorrect **)

    Let edges2 : seq (@node string_eqType * @fld string_eqType * @node string_eqType) :=
      [:: (pair
             (pair
                (Node "Query" [::])

                (Graph.Field "search" [:: pair "wrong_Arg" "L"]))          (* <--- Wrong name for argument *)

                (Node "Starship" [::
                                   (pair (Graph.Field  "id" [::]) (inl "3000"));
                                   (pair (Graph.Field "name" [::]) (inl "Falcon")); 
                                   (pair (Graph.Field "length" [::]) (inl "34.37"))
                                 ]
                )
          )
      ].

    
    Let g2 := GraphQLGraph r edges2.
    
    Example eNc : ~ edges_conform wf_schema g2.
    Proof. by [].
    Qed.
    
    
    (** Types are incorrect **)
    
    Let edges3 : seq (@node string_eqType * @fld string_eqType * @node string_eqType) :=
      [:: pair
          (pair (Node "Human" [::
                                 (pair (Graph.Field "id" [::]) (inl "1000"));
                                 (pair (Graph.Field "name" [::]) (inl "Luke"))
                              ]
                )
                (Graph.Field "friends" [::])
          )
          (Node "Starship" [::
                             (pair (Graph.Field "id" [::]) (inl "2001"));
                             (pair (Graph.Field "name" [::]) (inl "R2-D2"));
                             (pair (Graph.Field "primaryFunction" [::]) (inl "Astromech"))
                           ]
          )
      ].
    
    Let r3 : @node string_eqType := Node "Query" [::].
    
    Let g3 := GraphQLGraph r edges3.
    
    Example eNc3 : ~ edges_conform wf_schema g3.
    Proof. by [].
    Qed.




    Let edges4 : seq (@node string_eqType * @fld string_eqType * @node string_eqType) :=
      [:: pair
          (pair (Node "Query" [::])
                (Graph.Field "search" [:: (pair "wrong_Arg" "L")])
          )
          (Node "Other" [::
                           (pair (Graph.Field "id" [::]) (inl "3000")); (* <--- Type is not in union *)
                           (pair (Graph.Field "name" [::]) (inl "Falcon")); 
                           (pair (Graph.Field "length" [::]) (inl "34.37"))
                        ]
          )
      ].

    Let r4 : @node string_eqType := Node "Query" [::].

    Let g4 := GraphQLGraph r edges4.
    
    Example eNc4 : ~ edges_conform wf_schema g4.
    Proof. by [].
    Qed.



    (** Field's are incorrect **)

     Let edges5 : seq (@node string_eqType * @fld string_eqType * @node string_eqType) :=
       [:: pair
           (pair (Node "Query" [::])
                 (Graph.Field "search" [:: (pair "wrong_Arg" "L")])
           )
           (Node "Starship" [::
                               (pair (Graph.Field "id" [::]) (inl "3000"));
                               (pair (Graph.Field "name" [:: (pair "wrong" "arg")]) (inl "Falcon")); (* <--- invalid argument in field*) 
                               (pair (Graph.Field "length" [::]) (inl "34.37"))
                            ]
           )
       ].

    
    Let g5 := GraphQLGraph r edges5.

    
    Example fNc : ~ fields_conform wf_schema g5.
    Proof. by [].
    Qed.
    
  End WrongGraph.


End Example.


Section GraphQLSpecExamples.
  (**
     Examples from section Validation in the specification.

     https://graphql.github.io/graphql-spec/June2018/#sec-Validation

   *)
  
  Let StringScalar := Scalar "String".
  Let BooleanScalar := Scalar "Boolean".
  Let IntScalar := Scalar "Int".
  Let FloatScalar := Scalar "Float".


  Let QueryType := Object "Query" implements [::] {
                         [::
                            (Schema.Field "dog" [::] "Dog")
                         ]
                       }.
  
  Let DogCommandEnum := Enum "DogCommand" { [:: "SIT"; "DOWN"; "HEEL"] }.

  Let DogType := Object "Dog" implements [:: "Pet"] {
                         [::
                            (Schema.Field "name" [::] "String");
                            (Schema.Field "nickname" [::] "String");
                            (Schema.Field "barkVolume" [::] "Int");
                            (Schema.Field "doesKnowCommand" [:: (FieldArgument "dogCommand" "DogCommand")] "Boolean");
                            (Schema.Field "isHousetrained" [:: (FieldArgument "atOtherHomes" "Boolean")] "Boolean");
                            (Schema.Field "owner" [::] "Human")
                         ]
                       }.

  Let SentientInterface := Interface "Sentient" {
                                      [::
                                         (Schema.Field "name" [::] "String")
                                      ]
                                    }.
  
  Let PetInterface := Interface "Pet" {
                                 [::
                                    (Schema.Field "name" [::] "String")
                                 ]
                               }.



  Let AlienType := Object "Alien" implements [:: "Sentient"] {
                           [::
                              (Schema.Field "name" [::] "String");
                              (Schema.Field "homePlanet" [::] "String")
                           ]
                         }.

  Let HumanType := Object "Human" implements [:: "Sentient"] {
                           [::
                              (Schema.Field "name" [::] "String")
                           ]
                         }.

  Let CatCommandEnum := Enum "CatCommand" {[:: "JUMP" ]}.

  Let CatType := Object "Cat" implements [:: "Pet" ] {
                         [::
                            (Schema.Field "name" [::] "String");
                            (Schema.Field "nickname" [::] "String");
                            (Schema.Field "doesKnowCommand" [:: (FieldArgument "catCommand" "CatCommand")] "Boolean");
                            (Schema.Field "meowVolume" [::] "Int")
                         ]
                       }.

  Let CatOrDogUnion := Union "CatOrDog" { [:: "Cat"; "Dog"] }.

  Let DogOrHumanUnion := Union "DogOrHuman" { [:: "Dog"; "Human"] }.

  Let HumanOrAlienUnion := Union "HumanOrAlien" { [:: "Human"; "Alien"] }.
  

  Let schema := GraphQLSchema "Query" [:: StringScalar; BooleanScalar; IntScalar; FloatScalar;
                                 QueryType;
                                 DogCommandEnum; DogType;
                                   SentientInterface; PetInterface;
                                     AlienType; HumanType;
                                       CatCommandEnum; CatType;
                                         CatOrDogUnion; DogOrHumanUnion; HumanOrAlienUnion].

  Let schwf : schema.(is_wf_schema).
  Proof. by []. Qed.

  Let wf_schema : @wfGraphQLSchema string_eqType   := WFGraphQLSchema (fun n v => true) schwf.

  Section FieldValidation.
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Validation.Fields
     *)

    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selections-on-Objects-Interfaces-and-Unions-Types
     *)
    Let example102 : seq (@Query string_eqType) :=  [::
                                                      on "Dog" {
                                                        [::
                                                           "meowVolume" [[ [::] ]]
                                                        ]
                                                      }
                                                   ].
    
    Let example102' :  seq (@Query string_eqType) := [::
                                                       on "Dog" {
                                                         [::
                                                            "barkVolume" : "kawVolume" [[ [::] ]]
                                                         ]
                                                       }
                                                    ].

    (**
     This is not exactly the same as in the spec, but in that example they are checking 
     defined fragment spreads, not inline fragments.
     *)
    Example e102 : ~~ (queries_conform wf_schema "Dog" example102 || queries_conform wf_schema "Dog" example102').
    Proof. by []. Qed.


    Let example103 : seq (@Query string_eqType) := [::
                                                     (* on "Pet" { *)
                                                     (* [:: *)
                                                     "name" [[ [::] ]]
                                                     (* ] *)
                                                     (* } *)
                                                  ].

    
    Example e103 : queries_conform wf_schema "Pet" example103.
    Proof. by []. Qed.

    

    Let example104 : seq (@Query string_eqType) := [::
                                                     (* on "Pet" { *)
                                                     (* [:: *)
                                                     "nickname" [[ [::] ]]
                                                     (* ] *)
                                                     (* } *)
                                                  ].

    Example e104 : ~~ queries_conform wf_schema "Pet" example104.
    Proof. by []. Qed.

    Example e104' : all (fun implementor => queries_conform wf_schema implementor example104) (get_possible_types wf_schema "Pet").
    Proof.
        by [].
    Qed.
    

    Let example105 : seq (@Query string_eqType) := [::
                                                     (* on "CatOrDog" { *)
                                                     (* [:: *)
                                                     on "Pet" {
                                                       [::
                                                          "name" [[ [::] ]]
                                                       ]
                                                     };
                                                     on "Dog" {
                                                          [::
                                                             "barkVolume" [[ [::] ]]
                                                          ]
                                                        }
                                                        (* ] *)
                                                        (* } *)
                                                  ].

    Example e105 : queries_conform wf_schema "CatOrDog" example105.
    Proof. by []. Qed.

    Let example106 : seq (@Query string_eqType) := [::
                                                     "name" [[ [::] ]];
                                                     "barkVolume" [[ [::] ]]
                                                  ].

    Example e106 : ~~ queries_conform wf_schema "CatOrDog" example106.
    Proof. by []. Qed.

    

    Section FieldSelectionMerging.

      Let example107_1 : seq (@Query string_eqType) := [::
                                                         "name" [[ [::] ]];
                                                         "name" [[ [::] ]]
                                                      ].
      Let example107_2 : seq (@Query string_eqType) := [::
                                                         "otherName" : "name" [[ [::] ]];
                                                         "otherName" : "name" [[ [::] ]]
                                                      ].

      Example e107_1 : is_field_merging_possible wf_schema "Dog" example107_1.
      Proof.
          by [].
      Qed.

      Example e107_2 : is_field_merging_possible wf_schema "Dog" example107_2.
      Proof.
          by [].
      Qed.


      Let example108 : seq (@Query string_eqType) := [::
                                                       "name" : "nickname" [[ [::] ]];
                                                       "name" [[ [::] ]]
                                                    ].

      Example e108 : ~~ is_field_merging_possible wf_schema "Dog" example108.
      Proof.
          by [].
      Qed.

      Let example109 := [::
                          "doesKnowCommand" [[ [:: pair "dogCommand" "SIT"] ]];
                          "doesKnowCommand" [[ [:: pair "dogCommand" "SIT"] ]]
                       ].

      Example e109 : is_field_merging_possible wf_schema "Dog" example109.
      Proof.
          by [].
      Qed.
      
      (**
       Omitting examples with variables since they are not implemented. 
       *)
      Let example110_1 := [::
                            "doesKnowCommand" [[ [:: pair "dogCommand" "SIT"] ]];
                            "doesKnowCommand" [[ [:: pair "dogCommand" "HEEL"] ]]
                         ].
      
      Let example110_2 := [::
                            "doesKnowCommand" [[ [:: pair "dogCommand" "SIT"] ]];
                            "doesKnowCommand" [[ [::] ]]
                         ].

      Example e110_1 : ~~ is_field_merging_possible wf_schema "Dog" example110_1.
      Proof.
          by [].
      Qed.
      
      Example e110_2 : ~~ is_field_merging_possible wf_schema "Dog" example110_2.
      Proof.
          by [].
      Qed.


      Let example111_1 : seq (@Query string_eqType) := [::
                                                         on "Dog" {
                                                           [::
                                                              "volume": "barkVolume" [[ [::] ]]
                                                           ]
                                                         };
                                                         
                                                         on "Cat" {
                                                              [::
                                                                 "volume": "meowVolume" [[ [::] ]]
                                                              ]
                                                            }
                                                      ].

      Example e111_1 : is_field_merging_possible wf_schema "Pet" example111_1.
      Proof.
          by [].
      Qed.

      Let example111_2 : seq (@Query string_eqType) := [::
                                                         on "Dog" {
                                                           [::
                                                              "doesKnowCommand" [[ [:: pair "dogCommand" "SIT"] ]]
                                                           ]
                                                         };
                                                         
                                                         on "Cat" {
                                                              [::
                                                                 "doesKnowCommand" [[ [:: pair "catCommand" "JUMP"] ]]
                                                              ]
                                                            }
                                                      ].

      Example e111_2 : is_field_merging_possible wf_schema "Pet" example111_2.
      Proof.
          by [].
      Qed.
      

      Let example112 : seq (@Query string_eqType) := [::
                                                       on "Dog" {
                                                         [::
                                                            "someValue": "nickname" [[ [::] ]]
                                                         ]
                                                       };
                                                       
                                                       on "Cat" {
                                                            [::
                                                               "someValue": "meowVolume" [[ [::] ]]
                                                            ]
                                                          }
                                                    ].

      Example e112 : ~~ have_compatible_response_shapes wf_schema [seq pair "Pet" q | q <- example112].
      Proof.
          by [].
      Qed.

      Example e112' : ~~ queries_conform wf_schema "Pet" example112.
      Proof.
          by [].
      Qed.
      
      
    End FieldSelectionMerging.


    Section LeafFieldSelections.
      (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Leaf-Field-Selections
       *)

      Let example113 : seq (@Query string_eqType) := [::
                                                       "barkVolume" [[ [::] ]]
                                                    ].
      
      Example e113 : queries_conform wf_schema "Dog" example113.
      Proof.
          by [].
      Qed.

      Let example114 : seq (@Query string_eqType) :=
        [::
           "barkVolume" [[ [::] ]] {
             [::
                "sinceWhen" [[ [::] ]]
             ]
           }
        ].

      Example e114 : ~~ queries_conform wf_schema "Dog" example114.
      Proof.
          by [].
      Qed.


      (**
       Example 115 uses schema extension, which is not implemented but we can manage around it.
       *)
      Let ExtendedQueryType := Object "ExtendedQuery" implements [::] {
                                       [::
                                          (Schema.Field "dog" [::] "Dog");
                                          (Schema.Field "human" [::] "Human");
                                          (Schema.Field "pet" [::] "Pet");
                                          (Schema.Field "catOrDog" [::] "CatOrDog")
                                       ]
                                     }.
      (* For some reason this gets stuck trying to compute wf... ? *)
      (* Let extended_schema := GraphQLSchema "ExtendedQuery" *)
      (*                                     (ExtendedQueryType :: schema.(type_definitions)). *)

      Let extended_schema := GraphQLSchema "ExtendedQuery"
                                          [:: StringScalar; BooleanScalar; IntScalar; FloatScalar;
                                             ExtendedQueryType;
                                             DogCommandEnum; DogType;
                                               SentientInterface; PetInterface;
                                                 AlienType; HumanType;
                                                   CatCommandEnum; CatType;
                                                     CatOrDogUnion; DogOrHumanUnion; HumanOrAlienUnion].

      Let extended_schwf : extended_schema.(is_wf_schema).
      Proof. by []. Qed.

      Let extended_wf_schema : @wfGraphQLSchema string_eqType   := WFGraphQLSchema (fun n v => true) extended_schwf.

      Let example116_1 : seq (@Query string_eqType) :=
        [::
           "human" [[ [::] ]]
        ].

      Example e116_1 : ~~queries_conform extended_wf_schema "ExtendedQuery" example116_1.
      Proof.
          by [].
      Qed.

      Let example116_2 : seq (@Query string_eqType) :=
        [::
           "pet" [[ [::] ]]
        ].

      Example e116_2 : ~~queries_conform extended_wf_schema "ExtendedQuery" example116_2.
      Proof.
          by [].
      Qed.

      Let example116_3 : seq (@Query string_eqType) :=
        [::
           "catOrDog" [[ [::] ]]
        ].

      Example e116_3 : ~~queries_conform extended_wf_schema "ExtendedQuery" example116_3.
      Proof.
          by [].
      Qed.
      
    End LeafFieldSelections.

  End FieldValidation.


  Section ValidArguments.
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Argument-Names
     *)

    Let example117_1 : seq (@Query string_eqType) :=
      [::
         "doesKnowCommand" [[ [:: pair "dogCommand" "SIT"] ]]
      ].

    Example e117_1 : queries_conform wf_schema "Dog" example117_1.
    Proof.
        by [].
    Qed.

    (**
       Not including the directive @include since directives are not implemented.
     *)
    Let example117_2 : seq (@Query string_eqType) :=
      [::
         "isHousetrained" [[ [:: pair "atOtherHomes" "true" ] ]]
      ].

    Example e117_2 : queries_conform wf_schema "Dog" example117_2.
    Proof.
      by [].
    Qed.


    Let example_118 : seq (@Query string_eqType) :=
      [::
         "doesKnowCommand" [[ [:: pair "command" "CLEAN_UP_HOUSE" ] ]]
      ].

    Example e118 : ~~queries_conform wf_schema "Dog" example_118.
    Proof.
        by [].
    Qed.

    (**
       Example 119 is not included since it checks the directive @include
       and directives are not implemented.
     *)


    Let ArgumentsType := Object "Arguments" implements [::] {
                                 [::
                                    (Schema.Field "multipleReqs" [::
                                                                    FieldArgument "x" "Int";
                                                                    FieldArgument "y" "Int"
                                                                 ]
                                                  "Int");
                                    (Schema.Field "booleanArgField" [::
                                                                       FieldArgument "booleanArg" "Boolean"
                                                                    ]
                                                  "Boolean");
                                    (Schema.Field "floatArgField" [::
                                                                     FieldArgument "floatArg" "Float"
                                                                  ]
                                                  "Float");
                                    (Schema.Field "intArgField" [::
                                                                   FieldArgument "intArg" "Int"
                                                                ]
                                                  "Int");
                                    (* (Schema.Field "nonNullBooleanArgField" *)
                                    (*               [:: *)
                                    (*                  FieldArgument "nonNullBooleanArg" "Boolean" *)
                                    (*               ] *)
                                    (*               "Boolean"); *)

                                    (Schema.Field "booleanListArgField"
                                                  [::
                                                     FieldArgument "booleanListArg" [ "Boolean" ]
                                                  ]
                                                  [ "Boolean" ])

                                      (* (Schema.Field "optionalNonNullBooleanArgField" *)
                                      (*               [:: *)
                                      (*                  FieldArgument "optionalNonNullBooleanArgField" "Boolean" *)
                                      (*               ] *)
                                      (*               "Boolean") *)
                                      
                                                                              
                                 ]
                               }.

    Let ExtendedQueryType := Object "ExtendedQuery" implements [::] {
                                     [::
                                        (Schema.Field "dog" [::] "Dog");
                                        (Schema.Field "arguments" [::] "Arguments")

                                     ]
                                   }.

    Let extended_schema := GraphQLSchema "ExtendedQuery"
                                        [:: StringScalar; BooleanScalar; IntScalar; FloatScalar;
                                           ExtendedQueryType;
                                           DogCommandEnum; DogType;
                                           SentientInterface; PetInterface;
                                           AlienType; HumanType;
                                           CatCommandEnum; CatType;
                                           CatOrDogUnion; DogOrHumanUnion; HumanOrAlienUnion;
                                           ArgumentsType
                                        ].

    Let extended_schwf : extended_schema.(is_wf_schema).
    Proof.
      (* For some reason just computing gets stuck - using by [] *)
      rewrite /is_wf_schema /= ?andbT; simp is_interface_type.
    Qed.

    Let extended_wf_schema : @wfGraphQLSchema string_eqType   := WFGraphQLSchema (fun n v => true) extended_schwf.

    Let example121_1 : seq (@Query string_eqType) :=
      [::
         "multipleReqs" [[ [:: (pair "x" "1"); (pair "y" "2")] ]]
      ].

    Example e121_1 : queries_conform extended_wf_schema "Arguments" example121_1.
    Proof.
        by [].
    Qed.

    Let example121_2 : seq (@Query string_eqType) :=
      [::
         "multipleReqs" [[ [:: (pair "y" "1"); (pair "x" "2")] ]]
      ].

    Example e121_2 : queries_conform extended_wf_schema "Arguments" example121_2.
    Proof.
        by [].
    Qed.

    (**
       Examples 122 - 125 are meant for required arguments, which is not implemented.
       We omit them here.
     *)

  End ValidArguments.

  Section Fragments.
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Validation.Fragments
     *)

    (**
       Examples 126 & 127 use defined fragments, which is not implemented.
       We omit them here.
     *)


    (**
       The spec checks whether the type condition on a fragment exists. 
       We check this indirectly when checking if the fragments spread.
       If a fragment does not exist in the schema, it will never spread.
     *)
    Let example128 : seq (@Query string_eqType) :=
      [::
         on "Dog" {
           [::
              "name" [[ [::] ]]
           ]
         }
      ].

    Example e128 : queries_conform wf_schema "Dog" example128 &&
                   queries_conform wf_schema "Pet" example128.                
    Proof.
        by [].
    Qed.


    Let example129 : seq (@Query string_eqType) :=
      [::
         on "NotInSchema" {
           [::
              "name" [[ [::] ]]
           ]
         }
      ].

    Example e129 : ~~queries_conform wf_schema "Dog" example129.
    Proof.
        by [].
    Qed.

    Example e129' : all (fun name => ~~queries_conform wf_schema name example129) wf_schema.(schema_names).
    Proof.
        by [].
    Qed.

    Let example130_1 : @Query string_eqType := on "Dog" {
                                                   [::
                                                      "name" [[ [::] ]]
                                                   ]
                                                 }.
    Example e130_1 : query_conforms wf_schema "Dog" example130_1 &&
                     query_conforms wf_schema "Pet" example130_1.
    Proof.
        by [].
    Qed.

    Let example130_2 : @Query string_eqType := on "Pet" {
                                                   [::
                                                      "name" [[ [::] ]]
                                                   ]
                                                 }.
    Example e130_2 : query_conforms wf_schema "Dog" example130_2 &&
                     query_conforms wf_schema "Pet" example130_2.
    Proof.
        by [].
    Qed.

     Let example130_3 : @Query string_eqType := on "CatOrDog" {
                                                    [::
                                                       on "Dog" {
                                                         [::
                                                            "name" [[ [::] ]]
                                                         ]
                                                       }
                                                    ]
                                                 }.
    Example e130_3 : query_conforms wf_schema "CatOrDog" example130_3.
    Proof.
        by [].
    Qed.

    Let example131_1 : (@Query string_eqType) := on "Int" {
                                                     [::
                                                        "something" [[ [::] ]]
                                                     ]
                                                   }.

    Example e131_1 : all (fun name => ~~query_conforms wf_schema name example131_1) wf_schema.(schema_names).
    Proof.
        by [].
    Qed.

    Let example131_2 : (@Query string_eqType) := on "Dog" {
                                                     [::
                                                        on "Boolean" {
                                                          [::
                                                             "somethingElse" [[ [::] ]]
                                                          ]
                                                        }
                                                     ]
                                                   }.

    Example e131_2 : all (fun name => ~~query_conforms wf_schema name example131_2) wf_schema.(schema_names).
    Proof.
        by [].
    Qed.


    (**
       Example 132-136 refer to fragment definitions. We don't implement 
       that so we omit those examples.

       https://graphql.github.io/graphql-spec/June2018/#example-9e1e3
       https://graphql.github.io/graphql-spec/June2018/#example-28421
       https://graphql.github.io/graphql-spec/June2018/#example-9ceb4
       https://graphql.github.io/graphql-spec/June2018/#example-08734
       https://graphql.github.io/graphql-spec/June2018/#example-6bbad
     *)



    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Object-Spreads-In-Object-Scope
     *)
    Let example137 : @Query string_eqType := on "Dog" {
                                                 [::
                                                    "barkVolume" [[ [::] ]]
                                                 ]
                                               }.
    Example e137' : is_fragment_spread_possible wf_schema "Dog" "Dog".
    Proof.
        by [].
    Qed.
    
    Example e137 : query_conforms wf_schema "Dog" example137.
    Proof.
        by [].
    Qed.

    Let example138 : @Query string_eqType := on "Cat" {
                                                 [::
                                                    "meowVolume" [[ [::] ]]
                                                 ]
                                               }.
     
    Example e138' : ~~ is_fragment_spread_possible wf_schema "Cat" "Dog".
    Proof.
        by [].
    Qed.

    Example e138 : ~~ query_conforms wf_schema "Dog" example138.
    Proof.
        by [].
    Qed.

    
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Abstract-Spreads-in-Object-Scope
     *)
    Let example139 : @Query string_eqType := on "Pet" {
                                                 [::
                                                    "name" [[ [::] ]]
                                                 ]
                                                }.

    
    Example e139' : is_fragment_spread_possible wf_schema "Pet" "Dog".
    Proof.
        by [].
    Qed.
    
    Example e139 : query_conforms wf_schema "Dog" example139.
    Proof.
        by [].
    Qed.

    Let example140 : @Query string_eqType := on "CatOrDog" {
                                                 [::
                                                    on "Cat" {
                                                      [::
                                                         "meowVolume" [[ [::] ]]
                                                      ]
                                                    }
                                                 ]
                                               }.
    
    Example e140' : is_fragment_spread_possible wf_schema "CatOrDog" "Dog".
    Proof.
        by [].
    Qed.
    
    Example e140 : query_conforms wf_schema "Dog" example140.
    Proof.
        by [].
    Qed.


    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Object-Spreads-In-Abstract-Scope
     *)
    Let example141_1 : seq (@Query string_eqType) :=
      [::
         "name" [[ [::] ]];
         on "Dog" {
              [::
                 "barkVolume" [[ [::] ]]
              ]
            }
      ].

    Example e141_1' : is_fragment_spread_possible wf_schema "Dog" "Pet".
    Proof.
        by [].
    Qed.

    
    Example e141_1 : queries_conform wf_schema "Pet" example141_1.
    Proof.
        by [].
    Qed.

    Let example141_2 : seq (@Query string_eqType) :=
      [::
         on "Cat" {
           [::
              "meowVolume" [[ [::] ]]
           ]
         }
      ].

    Example e141_2' : is_fragment_spread_possible wf_schema "Cat" "CatOrDog".
    Proof.
        by [].
    Qed.
    
    Example e141_2 : queries_conform wf_schema "CatOrDog" example141_2.
    Proof.
        by [].
    Qed.
    
    
    Let example142_1 : @Query string_eqType := on "Dog" {
                                                 [::
                                                    "barkVolume" [[ [::] ]]
                                                 ]
                                                 }.

    Example e142_1' : ~~ is_fragment_spread_possible wf_schema "Dog" "Sentient".
    Proof.
        by [].
    Qed.

    Example e142_1 : ~~ query_conforms wf_schema "Sentient" example142_1.
    Proof.
        by [].
    Qed.

    
    Let example142_2 : @Query string_eqType := on "Cat" {
                                                 [::
                                                    "meowVolume" [[ [::] ]]
                                                 ]
                                                 }.

    Example e142_2' : ~~ is_fragment_spread_possible wf_schema "Cat" "HumanOrAlien".
    Proof.
        by [].
    Qed.
    
    Example e142_2 : ~~ query_conforms wf_schema "HumanOrAlien" example142_2.
    Proof.
        by [].
    Qed.


    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Abstract-Spreads-in-Abstract-Scope
     *)
    Let example143 : seq (@Query string_eqType) :=
      [::
         on "DogOrHuman" {
           [::
              on "Dog" {
                [::
                   "barkVolume" [[ [::] ]]
                ]
              }
           ]
         }
      ].

    Example e143' : is_fragment_spread_possible wf_schema "DogOrHuman" "Pet".
    Proof.
        by [].
    Qed.

    Example e143 : queries_conform wf_schema "Pet" example143.
    Proof.
        by [].
    Qed.

    Let example144 : @Query string_eqType := on "Sentient" {
                                                 [::
                                                    "name" [[ [::] ]]
                                                 ]
                                               }.

    Example e144' : ~~ is_fragment_spread_possible wf_schema "Sentient" "Pet".
    Proof.
        by [].
    Qed.

    Example e144 : ~~ query_conforms wf_schema "Pet" example144.
    Proof.
        by [].
    Qed.
    
    
    
  End Fragments.

  Section ValuesValidation.
    (**
       Not adding examples of value validation.

       https://graphql.github.io/graphql-spec/June2018/#sec-Values
     *)
  End ValuesValidation.

    
    
    
End GraphQLSpecExamples.