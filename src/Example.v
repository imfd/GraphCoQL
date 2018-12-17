From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.

From Coq Require Import String Ascii List.
From CoqUtils Require Import string.


Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Graph.
Require Import GraphAux.
Require Import GraphConformance.
Require Import Query.
Require Import QueryConformance.
Require Import QuerySemantic.



(** This file includes some examples of schemas, graphs and queries. 
    The base schema is the one used in [Hartig & Pérez, 2017];

    Section HP includes the whole example used in [Hartig & Pérez, 2017],
    while the other sections may vary.
 **)
Section Example.

  Local Open Scope string_scope.
  

  Delimit Scope schema_scope with schema.
  Open Scope schema_scope.
  
  Notation "'type' O 'implements' I {{ F }}" := (ObjectTypeDefinition O I F) (at level 0, no associativity) : schema_scope.

  Notation "'interface' I {{ F }}" := (InterfaceTypeDefinition I F) (at level 0, no associativity) : schema_scope.

  Notation "'enum' E { EV }" := (EnumTypeDefinition E EV) (at level 0, E at next level,  EV at level 0) : schema_scope.

  Notation "'union' U 'of' Uv" := (UnionTypeDefinition U Uv) (at level 0, no associativity) : schema_scope.

  Notation "'scalar' S" := (ScalarTypeDefinition S) (at level 60).
  
  Notation "f : t" := (Schema.Field f [::] t).

  Notation "'[' s ']'" := (ListType s) (at level 0, s at next level).

  
  Coercion namedType_of_string (s : string) := NamedType s.
  
  Let IDType := scalar "ID".
  Let StringType := scalar "String".
  Let FloatType := scalar "Float".

  Let StarshipType := (ObjectTypeDefinition "Starship" [::]
                                           [:: ("id" : "ID");
                                              ("name" : "String");
                                              ("length" : "Float")
                     ]).

  Let CharacterType := interface "Character" {{[::
                                                 ("id" : "ID");
                                                 ("name" : "String");
                                                 ("friends" : ["Character"])]
                                            }}.

  
  Let DroidType := type "Droid" implements [:: (NamedType "Character")] {{[::
                                                                            ("id" : "ID");
                                                                            ("name" : "String");
                                                                            ("friends" : ["Character"]);
                                                                            ("primaryFunction" : "String")
                                                                              
                                                                       ]}}.
  
  
  Let HumanType := type "Human" implements [:: (NamedType "Character")] {{[::
                                                                            ("id" : "ID");
                                                                            ("name" : "String");
                                                                            ("friends" : ["Character"]);
                                                                            ("starships" : ["Starship"])
                                                                              
                                                                       ]}}.

  Let EpisodeType := enum "Episode" { [:: "NEWHOPE" ; "EMPIRE" ; "JEDI" ] }.


  Let SearchResultType := union "SearchResult" of [:: (NamedType "Human") ; (NamedType "Droid") ; (NamedType "Starship")].


  Let QueryType := type "Query" implements [::] {{ [::
                                                     (Schema.Field "hero" [:: (FieldArgument "episode" "Episode")] "Character");
                                                     (Schema.Field "search" [:: (FieldArgument "text" "String")] ["SearchResult"])]
                                               }}.

  Let schema  := Schema "Query"  [:: IDType; StringType; FloatType;  StarshipType;  CharacterType; DroidType; HumanType; EpisodeType; SearchResultType; QueryType].


  Lemma sdf : is_schema_wf schema.
  Proof. by []. Qed.
  



  Let wf_schema : @wfSchema string_ordType string_ordType   := WFSchema (fun n v => true) sdf.
  
  Section HP.


    
    Let edges : {fset node * fld * node} :=
      fset [:: (Graph.Node 0 "Query" emptym ,
                Graph.Field "search" [fmap ("text", "L")],
                Graph.Node 4 "Starship" [fmap (Graph.Field "id" emptym, (inl "3000"));
                                           (Graph.Field "name" emptym, (inl "Falcon")); 
                                           (Graph.Field "length" emptym, (inl "34.37"))]);
              (Graph.Node 0 "Query" emptym,
               Graph.Field "search" [fmap ("text", "L")],
               Graph.Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                       (Graph.Field "name" emptym, (inl "Luke"))]);
              (Graph.Node 0 "Query" emptym,
               Graph.Field "hero" [fmap ("episode", "EMPIRE")],
               Graph.Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                       (Graph.Field "name" emptym, (inl "Luke"))]);
              (Graph.Node 0 "Query" emptym,
               Graph.Field "hero" [fmap ("episode", "NEWHOPE")],
               Graph.Node 2 "Droid" [fmap  (Graph.Field "id" emptym, (inl "2001"));
                                       (Graph.Field "name" emptym, (inl "R2-D2"));
                                       (Graph.Field "primaryFunction" emptym, (inl "Astromech"))]);
              (Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                 (Graph.Field "name" emptym, (inl "Luke"))],
               Graph.Field "friends" emptym,
               Graph.Node 2 "Droid" [fmap  (Graph.Field "id" emptym, (inl "2001"));
                                       (Graph.Field "name" emptym, (inl "R2-D2"));
                                       (Graph.Field "primaryFunction" emptym, (inl "Astromech"))]);
              (Node 2 "Droid" [fmap  (Graph.Field "id" emptym, (inl "2001"));
                                 (Graph.Field "name" emptym, (inl "R2-D2"));
                                 (Graph.Field "primaryFunction" emptym, (inl "Astromech"))],
               Graph.Field "friends" emptym,
               Graph.Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                       (Graph.Field "name" emptym, (inl "Luke"))]);
              (Graph.Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                       (Graph.Field "name" emptym, (inl "Luke"))],
               Graph.Field "friends" emptym,
               Graph.Node 3 "Human" [fmap (Graph.Field "id" emptym, (inl "1002"));
                                       (Graph.Field "name" emptym, (inl "Han"))]);
              (Graph.Node 3 "Human" [fmap (Graph.Field "id" emptym, (inl "1002"));
                                       (Graph.Field "name" emptym, (inl "Han"))],
               Graph.Field "friends" emptym,
               Graph.Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                       (Graph.Field "name" emptym, (inl "Luke"))]);
              (Graph.Node 3 "Human" [fmap (Graph.Field "id" emptym, (inl "1002"));
                                       (Graph.Field "name" emptym, (inl "Han"))],
               Graph.Field "starships" emptym,
               Graph.Node 4 "Starship" [fmap (Graph.Field "id" emptym, (inl "3000"));
                                          (Graph.Field "name" emptym, (inl "Falcon")); 
                                          (Graph.Field "length" emptym, (inl "34.37"))])
           ].
    
    
    Let r : @node nat_ordType string_ordType string_ordType := Graph.Node 0 "Query" emptym.
    
    
    Let g := GraphQLGraph r edges.


    Lemma rtc : root_type_conforms wf_schema g.
    Proof.    by [].  Qed.

    
    Lemma ec : edges_conform wf_schema edges.
    Proof.
        by rewrite /edges_conform /edges [fset]unlock.
    Qed.

    Lemma fc : fields_conform wf_schema g.
    Proof.
        by rewrite /fields_conform /graph_s_nodes /= /edges [fset]unlock /=. Qed.

    Lemma nhot : nodes_have_object_type wf_schema g.
    Proof.
        by rewrite /nodes_have_object_type /graph_s_nodes /= /edges [fset]unlock.
    Qed.
    

    Let wf_graph := ConformedGraph rtc ec fc nhot.


    
    Let q := (SingleSelection
               (NestedField "hero" [fmap ("episode", "EMPIRE")]
                  (MultipleSelection
                     (SingleField "name" emptym)
                     (SingleSelection
                        (NestedField "friends" emptym
                           (MultipleSelection
                              (InlineFragment "Droid"
                                    (MultipleSelection
                                       (LabeledField "droidFriend" "name" emptym)
                                       (SingleSelection (SingleField "primaryFunction" emptym))
                                    )
                                 )
                              (SingleSelection
                                 (InlineFragment "Human"
                                 (MultipleSelection
                                    (LabeledField "humanFriend" "name" emptym)
                                    (SingleSelection
                                       (NestedField "starships" emptym
                                          (MultipleSelection
                                             (LabeledField "starship" "name" emptym)
                                             (SingleSelection (SingleField "length" emptym))
                                          )
                                       )
                                    )
                                    
                                 )
                              )
                              )
                           )
                        )
                     )
                  )
               )
            ).
             
  (*
  Lemma qc : SelectionConforms wf_schema q wf_schema.(query_type).
  Proof.
    rewrite /q /query_type /=.
    apply: NestedFieldConforms.
      by rewrite /lookup_field_in_type /=.
      by [].
    apply: SelectionSetConforms.
    apply: FieldConforms.  
      by rewrite /lookup_field_in_type /=.
      by [].
    apply: NestedFieldConforms.
      by rewrite /lookup_field_in_type /=.
      by [].
    apply: SelectionSetConforms; rewrite /name_of_type /=.

    apply: InlineFragmentConforms "Human" _ _.
      by [].
      by exists "Human".
      apply: SelectionSetConforms.
      apply: LabeledFieldConforms.
        by rewrite /lookup_field_in_type /=.
        by [].
      apply: NestedFieldConforms.
        by rewrite /lookup_field_in_type /=.
        by [].
      apply: SelectionSetConforms.
      apply: LabeledFieldConforms.
        by rewrite /lookup_field_in_type /=.
        by [].
      apply: FieldConforms.
        by rewrite /lookup_field_in_type /=.
        by [].
    apply: InlineFragmentConforms.
      by [].
      by exists "Droid".
      apply: SelectionSetConforms.
      apply: LabeledFieldConforms.
         by rewrite /lookup_field_in_type /=.
         by [].
      apply: FieldConforms.
         by rewrite /lookup_field_in_type /=.
         by [].
  Qed.  *)

  Lemma qbc : selection_conforms wf_schema q wf_schema.(query_type).
  Proof. by []. Qed.



  Let conformed_query := ConformedQuery qbc. 




  Let query_response :=
    (SingleResponse
       (NestedResult "hero"
          (MultipleResponses
             (SingleResult "name" "Luke")
             (SingleResponse
                (NestedListResult "friends"
                   [::
                      (MultipleResponses
                         (SingleResult "droidFriend" "R2-D2")
                         (MultipleResponses
                            (SingleResult "primaryFunction" "Astromech")
                            (SingleResponse Empty)
                          )
                      );
                      (MultipleResponses
                         Empty
                         (MultipleResponses
                            (SingleResult "humanFriend" "Han")
                            (SingleResponse
                               (NestedListResult "starships"
                                  [::
                                     (MultipleResponses
                                        (SingleResult "starship" "Falcon")
                                        (SingleResponse (SingleResult "length" "34.37"))
                                     )
                                  ]
                               )
                            )
                         )  
                      )
                   ]
                )
             )
          )
       )
    ).
     


   

                
    Example ev_query_eq_response :  (eval_selection  wf_graph conformed_query) = query_response.
    Proof.
      rewrite /eval_selection /eval /=.
      rewrite /get_target_nodes_with_field /=.
      rewrite /edges [fset]unlock /=.
      do ?[rewrite ?collect_eq ?/indexed_map /=]. by [].
      Admitted.
    


    Let q' :=
      (SingleSelection
         (NestedField "hero" [fmap ("episode", "EMPIRE")]
            (MultipleSelection
               (SingleField "name" emptym)
               (MultipleSelection
                  (SingleField "name" emptym)
                  (MultipleSelection                  
                     (SingleField "id" emptym)
                     (SingleSelection (SingleField "name" emptym))
                  )
               )
            )
         )
      ).

     Lemma qbc' : selection_conforms wf_schema q' wf_schema.(query_type).
  Proof. by []. Qed.
  


    Let conformed_query' := ConformedQuery qbc'. 

    Goal (eval_selection wf_graph conformed_query') =
    (SingleResponse
       (NestedResult "hero"
                     (MultipleResponses
                        (SingleResult "name" "Luke")
                        (MultipleResponses
                           Empty
                           (MultipleResponses
                              (SingleResult "id" "1000")
                              (SingleResponse Empty)
                           )
                        )
                     )
       )
    ).
      rewrite /eval_selection /eval /=.
      rewrite /get_target_nodes_with_field /=.
      rewrite /edges [fset]unlock /=.
      do ?[rewrite ?collect_eq ?/indexed_map /=].  by [].
      Admitted.

    Example ex7 :
      let r := [::
                 (SingleResult "name" "Luke");
                 (NestedListResult "friends"
                                   [::
                                      (ResponseList [:: (SingleResult "id" "2001")]);
                                      (ResponseList [:: (SingleResult "id" "1002")])
                                   ]
                 );
                 (NestedListResult "friends"
                                   [::
                                      (ResponseList [::
                                                       (SingleResult "id" "2001");
                                                       (SingleResult "name" "R2-D2")
                                      ]);
                                      (ResponseList [::
                                                       (SingleResult "id" "1002");
                                                       (SingleResult "name" "Han")
                                      ])
                                   ]
                 )
              ]
      in
      let expected := [::
                        (SingleResult "name" "Luke");
                        (NestedListResult "friends"
                                   [::
                                      (ResponseList [::
                                                       (SingleResult "id" "2001");
                                                       (SingleResult "name" "R2-D2")
                                      ]);
                                      (ResponseList [::
                                                       (SingleResult "id" "1002");
                                                       (SingleResult "name" "Han")
                                      ])
                                   ]
                        )
                     ]
      in
      @collect nat_ordType string_ordType string_ordType r = expected.
    intros.
    rewrite collect_equation /=.
    rewrite collect_equation.
    rewrite /indexed_map /=.
    rewrite collect_equation /=.
    rewrite collect_equation /=.
      by do ?[rewrite ?collect_equation ?/indexed_map /=].
      Qed.
    
  End HP.
  

  Section WrongGraph.
    (** Some examples of graph's not conforming to the schema **)

    Let r : @node nat_ordType string_ordType string_ordType := Graph.Node 0 "Query" emptym.
        
    (** Root node does not have same type as query type **)
    Let edges1 : {fset @node nat_ordType string_ordType string_ordType * @fld string_ordType string_ordType  * @node nat_ordType string_ordType string_ordType } := fset0.
    
    Let r1 : @node nat_ordType string_ordType string_ordType := Graph.Node 0 "Human" emptym.
    
    Let g := GraphQLGraph r1 edges1.

    Example rtNc : ~ root_type_conforms wf_schema g.
    Proof. by []. Qed.



    
    (** Arguments are incorrect **)

    Let edges2 : {fset @node nat_ordType string_ordType string_ordType * fld * node} :=
      fset  [:: (Graph.Node 0 "Query" emptym ,
                 Graph.Field "search" [fmap ("wrong_Arg", "L")],          (* <--- Wrong name for argument *)
                 Graph.Node 4 "Starship" [fmap (Graph.Field "id" emptym, (inl "3000"));
                                            (Graph.Field "name" emptym, (inl "Falcon")); 
                                            (Graph.Field "length" emptym, (inl "34.37"))])].

    
    Let g2 := GraphQLGraph r edges2.
    
    Example eNc : ~ edges_conform wf_schema edges2.
    Proof. by rewrite /edges_conform /edges2 [fset]unlock. Qed. 
    
    
    (** Types are incorrect **)
    
    Let edges3 : {fset @node nat_ordType string_ordType string_ordType * @fld string_ordType string_ordType * node} :=
      fset  [:: (Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                   (Graph.Field "name" emptym, (inl "Luke"))],
                 Graph.Field "friends" emptym,
                 Graph.Node 2 "Starship" [fmap  (Graph.Field "id" emptym, (inl "2001"));
                                            (Graph.Field "name" emptym, (inl "R2-D2"));
                                            (Graph.Field "primaryFunction" emptym, (inl "Astromech"))])].
    
    Let r3 : @node nat_ordType string_ordType string_ordType := Graph.Node 0 "Query" emptym.
    
    Let g3 := GraphQLGraph r edges3.
    
    Example eNc3 : ~ edges_conform wf_schema edges3.
    Proof. by rewrite /edges_conform /edges3 [fset]unlock. Qed.




    Let edges4 : {fset @node nat_ordType string_ordType string_ordType * fld * node} :=
      fset  [:: (Graph.Node 0 "Query" emptym ,
                 Graph.Field "search" [fmap ("wrong_Arg", "L")],          
                 Graph.Node 4 "Other" [fmap (Graph.Field "id" emptym, (inl "3000")); (* <--- Type is not in union *)
                                         (Graph.Field "name" emptym, (inl "Falcon")); 
                                         (Graph.Field "length" emptym, (inl "34.37"))])].

    Let r4 : @node nat_ordType string_ordType string_ordType := Graph.Node 0 "Query" emptym.

    Let g4 := GraphQLGraph r edges4.
    
    Example eNc4 : ~ edges_conform wf_schema edges4.
    Proof. by rewrite /edges_conform /edges4 [fset]unlock. Qed.



    (** Field's are incorrect **)

     Let edges5 : {fset @node nat_ordType string_ordType string_ordType * fld * node} :=
      fset  [:: (Graph.Node 0 "Query" emptym ,
                 Graph.Field "search" [fmap ("wrong_Arg", "L")],          
                 Graph.Node 4 "Starship" [fmap (Graph.Field "id" emptym, (inl "3000"));
                                         (Graph.Field "name" [fmap ("wrong", "arg")], (inl "Falcon")); (* <--- invalid argument in field*) 
                                         (Graph.Field "length" emptym, (inl "34.37"))])].

    
    Let g5 := GraphQLGraph r edges5.

    
    Example fNc : ~ fields_conform wf_schema g5.
    Proof. rewrite /fields_conform /graph_s_nodes /= /edges5 [fset]unlock //=. Qed.
    
  End WrongGraph.


End Example.


Section GraphQLSpecExamples.


  Local Open Scope string_scope.
  

  Delimit Scope schema_scope with schema.
  Open Scope schema_scope.
  
  Notation "'type' O 'implements' I { F }" := (ObjectTypeDefinition O I F) (at level 0, O at next level, I at next level, F at next level, no associativity) : schema_scope.

  Notation "'interface' I { F }" := (InterfaceTypeDefinition I F) (at level 0, I at next level, F at next level, no associativity) : schema_scope.

  Notation "'enum' E { EV }" := (EnumTypeDefinition E EV) (at level 0, E at next level,  EV at level 0) : schema_scope.

  Notation "'union' U 'of' Uv" := (UnionTypeDefinition U Uv) (at level 0, no associativity) : schema_scope.

  Notation "'scalar' S" := (ScalarTypeDefinition S) (at level 60).
  
  Notation "f : t" := (Schema.Field f [::] t).

  Notation "'[' s ']'" := (ListType s) (at level 0, s at next level).
  
  
  Let StringScalar := scalar "String".
  Let BooleanScalar := scalar "Boolean".
  Let IntScalar := scalar "Int".


  Let QueryType := type "Query" implements [::] {[::
                                                   ("dog" : "Dog")
                                               ]}.
  
  Let DogCommandEnum := enum "DogCommand" {[:: "SIT"; "DOWN"; "HEEL"]}.

  Let DogType := type "Dog" implements [:: (NamedType "Pet")] {[::
                                                     ("name" : "String");
                                                     ("nickname" : "String");
                                                     ("barkVolume" : "Int");
                                                     (Schema.Field "doesKnowCommand" [:: (FieldArgument "dogCommand" "DogCommand")] "Boolean");
                                                     (Schema.Field "isHousetrained" [:: (FieldArgument "atOtherHomes" "Boolean")] "Boolean");
                                                     ("owner" : "Human")
                                                             ]}.

  Let SentientInterface := interface "Sentient" {[::
                                                   ("name" : "String")
                                               ]}.
  Let PetInterface := interface "Pet" {[::
                                    ("name" : "String")
                                ]}.



  Let AlienType := type "Alien" implements [:: (NamedType "Sentient")] {[::
                                                                          ("name" : "String");
                                                                          ("homePlanet" : "String")
                                                                       ]}.

  Let HumanType := type "Human" implements [:: (NamedType "Sentient")] {[::
                                                                          ("name" : "String")
                                                                      ]}.

  Let CatCommandEnum := enum "CatCommand" {[:: "JUMP" ]}.

  Let CatType := type "Cat" implements [:: (NamedType "Pet")] {[::
                                                                 ("name" : "String");
                                                                 ("nickname" : "String");
                                                                 (Schema.Field "doesKnowCommand" [:: (FieldArgument "catCommand" "CatCommand")] "Boolean");
                                                                 ("meowVolume" : "Int")
                                                             ]}.

  Let CatOrDogUnion := union "CatOrDog" of [:: (NamedType "Cat"); (NamedType "Dog")].

  Let DogOrHumanUnion := union "DogOrHuman" of [:: (NamedType "Dog"); (NamedType "Human")].

  Let HumanOrAlienUnion := union "HumanOrAlien" of [:: (NamedType "Human"); (NamedType "Alien")].
  

  Let schema := Schema "Query" [:: StringScalar; BooleanScalar; IntScalar;
                                 QueryType;
                                 DogCommandEnum; DogType;
                                   SentientInterface; PetInterface;
                                     AlienType; HumanType;
                                       CatCommandEnum; CatType;
                                         CatOrDogUnion; DogOrHumanUnion; HumanOrAlienUnion].

  Lemma schwf : is_schema_wf schema.
  Proof. by []. Qed.

  Let wf_schema : @wfSchema string_ordType string_ordType   := WFSchema (fun n v => true) schwf.

  Let example102 : @Query string_ordType string_ordType := (InlineFragment "Dog" (SingleField "meowVolume" emptym)).
  Let example102' :  @Query string_ordType string_ordType := (InlineFragment "Dog" (LabeledField "barkVolume" "kawVolume" emptym)).

  Example e102 : ~ selection_conforms wf_schema example102 "Dog" /\ (~ selection_conforms wf_schema example102' "Dog").
  Proof. by []. Qed.

  Example e102' :  ~ selection_conforms wf_schema example102 "Query" /\ (~ selection_conforms wf_schema example102' "Query").
  Proof. by []. Qed.


  Let example103 : @Query string_ordType string_ordType := (InlineFragment "Pet" (SingleField "name" emptym)).

  Example e103 : selection_conforms wf_schema example103 "Dog".
  Proof. by []. Qed.

  Example e103' : ~ selection_conforms wf_schema example103 "Query".
  Proof. by []. Qed.


  Let example104 : @Query string_ordType string_ordType := (InlineFragment "Pet" (SingleField "nickname" emptym)).

  Example e104 : ~ selection_conforms wf_schema example104 "Dog".
  Proof. by []. Qed.


  Let example105 : @Query string_ordType string_ordType :=
    (InlineFragment "CatOrDog" (SelectionSet
                                  (InlineFragment "Pet" (SingleField "name" emptym))
                                  (InlineFragment "Dog" (SingleField "barkVolume" emptym)))).

  Example e105 : selection_conforms wf_schema example105 "CatOrDog".
  Proof. by []. Qed.

  Let example106 : @Query string_ordType string_ordType :=
    (InlineFragment "CatOrDog" (SelectionSet
                                  (SingleField "name" emptym)
                                  (SingleField "barkVolume" emptym))).

  Example e106 : ~ selection_conforms wf_schema example106 "CatOrDog".
  Proof. by []. Qed.
  
End GraphQLSpecExamples.