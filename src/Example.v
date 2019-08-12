From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From CoqUtils Require Import string.

From Equations Require Import Equations.
From CoqUtils Require Import string.


Require Import Base.
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
                   (pair "name" (Leaf (SingleValue "Luke")));
                   (pair "friends"
                         (Array
                            [::
                               {-
                                [::
                                   (pair "droidFriend" (Leaf (SingleValue "R2-D2")));
                                   (pair "primaryFunction" (Leaf (SingleValue "Astromech")))
                                ]
                                -};
                               {-
                                [::
                                   (pair "humanFriend" (Leaf (SingleValue "Han")));
                                   (pair "starships"
                                         (Array
                                            [::
                                               {-
                                                [::
                                                   (pair "starship" (Leaf (SingleValue "Falcon")));
                                                   (pair "length" (Leaf (SingleValue "34.37")))
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
                                (pair "name" (Leaf (SingleValue "Luke")));
                                (pair "id" (Leaf (SingleValue "1000")))
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
  

  Let schema := GraphQLSchema "Query" [:: StringScalar; BooleanScalar; IntScalar;
                                 QueryType;
                                 DogCommandEnum; DogType;
                                   SentientInterface; PetInterface;
                                     AlienType; HumanType;
                                       CatCommandEnum; CatType;
                                         CatOrDogUnion; DogOrHumanUnion; HumanOrAlienUnion].

  Lemma schwf : schema.(is_wf_schema).
  Proof. by []. Qed.

  Let wf_schema : @wfGraphQLSchema string_eqType   := WFGraphQLSchema (fun n v => true) schwf.

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
  
End GraphQLSpecExamples.