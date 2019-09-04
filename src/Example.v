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
Require Import GraphConformance.


Require Import Query.
Require Import QueryAux.

Require Import QueryConformance.


Require Import Response.

Require Import QueryNormalForm.


Require Import SeqExtra.
Require Import QueryTactics.

Require Import QuerySemantic.

Open Scope string_scope.

(* end hide *)




Section Values.

  Inductive Value : Type :=
  | VInt : nat -> Value
  | VBool: bool -> Value            
  | VString : string -> Value
  | VList : seq Value -> Value
  | VFloat : nat -> nat -> Value.

  Notation vtype := (nat + bool + string + (nat * nat))%type.

  Fixpoint tree_of_value (v : Value) : GenTree.tree vtype  :=
    match v with
    | VInt n => GenTree.Node 0 [:: GenTree.Leaf (inl (inl (inl n)))]
    | VBool b => GenTree.Node 4 [:: GenTree.Leaf (inl (inl (inr b)))]                            
    | VString s => GenTree.Node 1 [:: GenTree.Leaf (inl (inr s))]
    | VFloat f1 f2 => GenTree.Node 2 [:: GenTree.Leaf (inr (pair f1 f2))]
    | VList ls => GenTree.Node 3 [seq tree_of_value x | x <- ls]
    end.

  Fixpoint value_of_tree (t : GenTree.tree vtype) : option Value :=
    match t with
    | GenTree.Node 0 [:: GenTree.Leaf (inl (inl (inl n)))] => Some (VInt n)
    | GenTree.Node 4 [:: GenTree.Leaf (inl (inl (inr b)))] => Some (VBool b)
    | GenTree.Node 1 [:: GenTree.Leaf (inl (inr s))] => Some (VString s)
    | GenTree.Node 2 [:: GenTree.Leaf (inr (pair f1 f2))] => Some (VFloat f1 f2)
    | GenTree.Node 3 vals =>
      Some (VList (pmap value_of_tree vals))
    | _ => None
    end.

  Lemma tree_of_valueK : pcancel tree_of_value value_of_tree.
  Proof.
    rewrite /pcancel; case => //=.
    elim=> //= x xs IH.
  Admitted.

  Canonical value_eqType := EqType Value (PcanEqMixin tree_of_valueK).

  Fixpoint coerce (v : Value) : @ResponseNode (option Value) :=
    match v with
    | VList ls => Array [seq coerce x | x <- ls]
    | _ => Leaf (Some v)
    end.
  
  Coercion v_of_nat (n : nat) := VInt n.
  Coercion v_of_bool (b : bool) := VBool b.
  Coercion v_of_str (s : string) := VString s.


  Variable (schema : graphQLSchema). 
  Fixpoint is_valid_value (ty : type) (v : Value) : bool :=
    match v with
    | VInt _ => if ty is NamedType name then
                 (name == "Int") || (name == "ID")
               else
                 false
                   
    | VBool _ => if ty is NamedType name then
                  name == "Boolean"
                else
                  false 
                    
    | VString s => if ty is NamedType name then
                    (name == "String")
                    ||
                    if lookup_type schema name is Some (Enum _ { members }) then
                      s \in members
                    else
                      false
                  else
                    false
                      
    | VFloat _ _ => if ty is NamedType name then
                     name == "Float"
                   else
                     false
                       
    | VList ls => if ty is ListType ty' then
                   all (is_valid_value ty') ls
                 else
                   false

    end.

End Values.



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
  


 

  Let wf_schema : wfGraphQLSchema := WFGraphQLSchema sdf (is_valid_value schema).
  
  Section HP.


    (* Close Scope query_eval. *)
    
    Let edges : seq (@node value_eqType * fld * node) :=
      [::
         pair (pair (Node "Query" [::])
                    (Graph.Field "search" [:: (pair "text" (VString "L"))]))
         (Node "Starship" [::
                             (pair (Graph.Field "id" [::])  (VInt 3000));
                             (pair (Graph.Field "name" [::]) (VString "Falcon")); 
                             (pair (Graph.Field "length" [::]) (VFloat 34 37))
         ]);
         pair (pair (Node "Query" [::])
                    (Graph.Field "search" [:: (pair "text" (VString "L"))]))
              (Node "Human" [::
                               pair (Graph.Field "id" [::]) (VInt 1000);
                               pair (Graph.Field "name" [::]) (VString "Luke")
              ]);
         pair (pair (Node "Query" [::])
                    (Graph.Field "hero" [:: pair "episode" (VString "EMPIRE")]))
              (Node "Human" [::
                               pair (Graph.Field "id" [::]) (VInt 1000);
                               pair (Graph.Field "name" [::]) (VString "Luke")
              ]);
         pair (pair (Node "Query" [::])
                    (Graph.Field "hero" [:: pair "episode" (VString "NEWHOPE")]))
              (Node "Droid" [::
                               (pair (Graph.Field "id" [::]) (VInt 2001));
                               (pair (Graph.Field "name" [::]) (VString "R2-D2"));
                               (pair (Graph.Field "primaryFunction" [::]) (VString "Astromech"))
              ]);
         
         pair (pair (Node "Human" [::
                                     pair (Graph.Field "id" [::]) (VInt 1000);
                                     pair (Graph.Field "name" [::]) (VString "Luke")
                    ])
                    (Graph.Field "friends" [::]))
              (Node "Droid" [::
                               (pair (Graph.Field "id" [::]) (VInt 2001));
                               (pair (Graph.Field "name" [::]) (VString "R2-D2"));
                               (pair (Graph.Field "primaryFunction" [::]) (VString "Astromech"))
              ]);

         pair (pair (Node "Droid" [::
                                     (pair (Graph.Field "id" [::]) (VInt 2001));
                                     (pair (Graph.Field "name" [::]) (VString "R2-D2"));
                                     (pair (Graph.Field "primaryFunction" [::]) (VString "Astromech"))
                    ])
                    (Graph.Field "friends" [::]))
              (Node "Human" [::
                               pair (Graph.Field "id" [::]) (VInt 1000);
                               pair (Graph.Field "name" [::]) (VString "Luke")
              ]);
         
         pair (pair (Node "Human" [::
                                     pair (Graph.Field "id" [::]) (VInt 1000);
                                     pair (Graph.Field "name" [::]) (VString "Luke")
                    ])
                    (Graph.Field "friends" [::]))
              (Node "Human" [::
                               pair (Graph.Field "id" [::]) (VInt 1002);
                               pair (Graph.Field "name" [::]) (VString "Han")
              ]);
         
         pair (pair (Node "Human" [::
                                     pair (Graph.Field "id" [::]) (VInt 1002);
                                     pair (Graph.Field "name" [::]) (VString "Han")
                    ])
                    (Graph.Field "friends" [::]))
              (Node "Human" [::
                               pair (Graph.Field "id" [::]) (VInt 1000);
                               pair (Graph.Field "name" [::]) (VString "Luke")
              ]);
         
         pair (pair (Node "Human" [::
                                     pair (Graph.Field "id" [::]) (VInt 1002);
                                     pair (Graph.Field "name" [::]) (VString "Han")
                    ])
                    (Graph.Field "starships" [::]))
              (Node "Starship" [:: (pair (Graph.Field "id" [::]) (VInt 3000));
                                  (pair (Graph.Field "name" [::]) (VString "Falcon")); 
                                  (pair (Graph.Field "length" [::]) (VFloat 34 37))])
      ].
    
    
    Let r : @node value_eqType := Node "Query" [::].
    
    
    Let g := GraphQLGraph r edges.


    Lemma rtc : root_type_conforms wf_schema g.
    Proof.    by [].  Qed.

    
    Lemma ec : edges_conform wf_schema g.
    Proof.
      by [].
    Qed.

    Lemma fc : nodes_conform wf_schema g.
    Proof.
      by []. 
    Qed.
    

    Let wf_graph := ConformedGraph rtc ec fc.


    
    Let q :=
      [::
         "hero" [[ [:: (pair "episode" (VString "EMPIRE")) ] ]] {
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
                   (pair "name" (Leaf (Some (VString "Luke"))));
                   (pair "friends"
                         (Array
                            [::
                               {-
                                [::
                                   (pair "droidFriend" (Leaf (Some (VString "R2-D2"))));
                                   (pair "primaryFunction" (Leaf (Some (VString "Astromech"))))
                                ]
                                -};
                               {-
                                [::
                                   (pair "humanFriend" (Leaf (Some (VString "Han"))));
                                   (pair "starships"
                                         (Array
                                            [::
                                               {-
                                                [::
                                                   (pair "starship" (Leaf (Some (VString "Falcon"))));
                                                   (pair "length" (Leaf (Some (VFloat 34 37))))
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
     


                
  Example ev_query_eq_response :  wf_schema, wf_graph ⊢  ⟦ q ⟧ˢ in wf_graph.(root) with coerce = query_response.
  Proof.
      by [].
  Qed.

    

    Let q' := [::
                ("hero" [[ [:: (pair "episode" (VString "EMPIRE")) ] ]] {
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
  


     Goal (wf_schema, wf_graph ⊢  ⟦ q' ⟧ˢ in wf_graph.(root) with coerce =
            [::
               (pair "hero" {-
                             [::
                                (pair "name" (Leaf (Some (VString "Luke"))));
                                (pair "id" (Leaf (Some (VInt 1000))))
                             ]
                             -}
               )
          ]) .
         by [].
     Qed.
    
    
  End HP.
  

  Section WrongGraph.
    (** Some examples of graph's not conforming to the schema **)

    Let r : @node value_eqType := Node "Query" [::].
        
    (** Root node does not have same type as query type **)
    Let edges1 : seq (@node value_eqType * @fld value_eqType * @node value_eqType) := [::].
    
    Let r1 : @node value_eqType := Graph.Node "Human" [::].
    
    Let g := GraphQLGraph r1 edges1.

    Example rtNc : ~ root_type_conforms wf_schema g.
    Proof. by []. Qed.



    
    (** Arguments are incorrect **)

    Let edges2 : seq (@node value_eqType * @fld value_eqType * @node value_eqType) :=
      [:: (pair
             (pair
                (Node "Query" [::])

                (Graph.Field "search" [:: pair "wrong_Arg" (VString "L")]))          (* <--- Wrong name for argument *)

                (Node "Starship" [::
                                   (pair (Graph.Field  "id" [::]) (VInt 3000));
                                   (pair (Graph.Field "name" [::]) (VString "Falcon")); 
                                   (pair (Graph.Field "length" [::]) (VFloat 34 37))
                                 ]
                )
          )
      ].

    
    Let g2 := GraphQLGraph r edges2.
    
    Example eNc : ~ edges_conform wf_schema g2.
    Proof. by [].
    Qed.
    
    
    (** Types are incorrect **)
    
    Let edges3 : seq (@node value_eqType * @fld value_eqType * @node value_eqType) :=
      [:: pair
          (pair (Node "Human" [::
                                 (pair (Graph.Field "id" [::]) (VInt 1000));
                                 (pair (Graph.Field "name" [::]) (VString "Luke"))
                              ]
                )
                (Graph.Field "friends" [::])
          )
          (Node "Starship" [::
                             (pair (Graph.Field "id" [::]) (VInt 2001));
                             (pair (Graph.Field "name" [::]) (VString "R2-D2"));
                             (pair (Graph.Field "primaryFunction" [::]) (VString "Astromech"))
                           ]
          )
      ].
    
    Let r3 : @node string_eqType := Node "Query" [::].
    
    Let g3 := GraphQLGraph r edges3.
    
    Example eNc3 : ~ edges_conform wf_schema g3.
    Proof. by [].
    Qed.




    Let edges4 : seq (@node value_eqType * fld * node) :=
      [:: pair
          (pair (Node "Query" [::])
                (Graph.Field "search" [:: (pair "wrong_Arg" (VString "L"))])
          )
          (Node "Other" [::
                           (pair (Graph.Field "id" [::]) (VInt 3000)); (* <--- Type is not in union *)
                           (pair (Graph.Field "name" [::]) (VString "Falcon")); 
                           (pair (Graph.Field "length" [::]) (VFloat 34 37))
                        ]
          )
      ].

    Let r4 : @node value_eqType := Node "Query" [::].

    Let g4 := GraphQLGraph r edges4.
    
    Example eNc4 : ~ edges_conform wf_schema g4.
    Proof. by [].
    Qed.



    (** Field's are incorrect **)

     Let edges5 : seq (@node value_eqType * @fld value_eqType * @node value_eqType) :=
       [:: pair
           (pair (Node "Query" [::])
                 (Graph.Field "search" [:: (pair "wrong_Arg" (VString "L"))])
           )
           (Node "Starship" [::
                               (pair (Graph.Field "id" [::]) (VInt 3000));
                               (pair (Graph.Field "name" [:: (pair "wrong" (VString "arg"))]) (VString "Falcon")); (* <--- invalid argument in field*) 
                               (pair (Graph.Field "length" [::]) (VFloat 34 37))
                            ]
           )
       ].

    
    Let g5 := GraphQLGraph r edges5.

    
    Example fNc : ~ nodes_conform wf_schema g5.
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

  Let wf_schema : wfGraphQLSchema := WFGraphQLSchema schwf (is_valid_value schema).

  Section FieldValidation.
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Validation.Fields
     *)

    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selections-on-Objects-Interfaces-and-Unions-Types
     *)
    Let example102 : seq (@Query value_eqType) :=  [::
                                                      on "Dog" {
                                                        [::
                                                           "meowVolume" [[ [::] ]]
                                                        ]
                                                      }
                                                   ].
    
    Let example102' :  seq (@Query value_eqType) := [::
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


    Let example103 : seq (@Query value_eqType) := [::
                                                     (* on "Pet" { *)
                                                     (* [:: *)
                                                     "name" [[ [::] ]]
                                                     (* ] *)
                                                     (* } *)
                                                  ].

    
    Example e103 : queries_conform wf_schema "Pet" example103.
    Proof. by []. Qed.

    

    Let example104 : seq (@Query value_eqType) := [::
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
    

    Let example105 : seq (@Query value_eqType) := [::
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

    Let example106 : seq (@Query value_eqType) := [::
                                                     "name" [[ [::] ]];
                                                     "barkVolume" [[ [::] ]]
                                                  ].

    Example e106 : ~~ queries_conform wf_schema "CatOrDog" example106.
    Proof. by []. Qed.

    

    Section FieldSelectionMerging.

      Let example107_1 : seq (@Query value_eqType) := [::
                                                         "name" [[ [::] ]];
                                                         "name" [[ [::] ]]
                                                      ].
      Let example107_2 : seq (@Query value_eqType) := [::
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


      Let example108 : seq (@Query value_eqType) := [::
                                                       "name" : "nickname" [[ [::] ]];
                                                       "name" [[ [::] ]]
                                                    ].

      Example e108 : ~~ is_field_merging_possible wf_schema "Dog" example108.
      Proof.
          by [].
      Qed.

      Let example109 := [::
                          "doesKnowCommand" [[ [:: pair "dogCommand" (VString "SIT")] ]];
                          "doesKnowCommand" [[ [:: pair "dogCommand" (VString "SIT")] ]]
                       ].

      Example e109 : is_field_merging_possible wf_schema "Dog" example109.
      Proof.
          by [].
      Qed.
      
      (**
       Omitting examples with variables since they are not implemented. 
       *)
      Let example110_1 := [::
                            "doesKnowCommand" [[ [:: pair "dogCommand" (VString "SIT")] ]];
                            "doesKnowCommand" [[ [:: pair "dogCommand" (VString "HEEL")] ]]
                         ].
      
      Let example110_2 := [::
                            "doesKnowCommand" [[ [:: pair "dogCommand" (VString "SIT")] ]];
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


      Let example111_1 : seq (@Query value_eqType) := [::
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

      Let example111_2 : seq (@Query value_eqType) := [::
                                                         on "Dog" {
                                                           [::
                                                              "doesKnowCommand" [[ [:: pair "dogCommand" (VString "SIT")] ]]
                                                           ]
                                                         };
                                                         
                                                         on "Cat" {
                                                              [::
                                                                 "doesKnowCommand" [[ [:: pair "catCommand" (VString "JUMP")] ]]
                                                              ]
                                                            }
                                                      ].

      Example e111_2 : is_field_merging_possible wf_schema "Pet" example111_2.
      Proof.
          by [].
      Qed.
      

      Let example112 : seq (@Query value_eqType) := [::
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

      Let example113 : seq (@Query value_eqType) := [::
                                                       "barkVolume" [[ [::] ]]
                                                    ].
      
      Example e113 : queries_conform wf_schema "Dog" example113.
      Proof.
          by [].
      Qed.

      Let example114 : seq (@Query value_eqType) :=
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

      Let extended_wf_schema : @wfGraphQLSchema value_eqType   := WFGraphQLSchema extended_schwf (is_valid_value extended_schema).

      Let example116_1 : seq (@Query value_eqType) :=
        [::
           "human" [[ [::] ]]
        ].

      Example e116_1 : ~~queries_conform extended_wf_schema "ExtendedQuery" example116_1.
      Proof.
          by [].
      Qed.

      Let example116_2 : seq (@Query value_eqType) :=
        [::
           "pet" [[ [::] ]]
        ].

      Example e116_2 : ~~queries_conform extended_wf_schema "ExtendedQuery" example116_2.
      Proof.
          by [].
      Qed.

      Let example116_3 : seq (@Query value_eqType) :=
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

    Let example117_1 : seq (@Query value_eqType) :=
      [::
         "doesKnowCommand" [[ [:: pair "dogCommand" (VString "SIT")] ]]
      ].

    Example e117_1 : queries_conform wf_schema "Dog" example117_1.
    Proof.
        by [].
    Qed.

    (**
       Not including the directive @include since directives are not implemented.
     *)
    Let example117_2 : seq (@Query value_eqType) :=
      [::
         "isHousetrained" [[ [:: pair "atOtherHomes" (VBool true) ] ]]
      ].

    Example e117_2 : queries_conform wf_schema "Dog" example117_2.
    Proof.
      by [].
    Qed.


    Let example_118 : seq (@Query value_eqType) :=
      [::
         "doesKnowCommand" [[ [:: pair "command" (VString "CLEAN_UP_HOUSE") ] ]]
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

    Let extended_wf_schema : @wfGraphQLSchema value_eqType   := WFGraphQLSchema extended_schwf (is_valid_value extended_schema).

    Let example121_1 : seq (@Query value_eqType) :=
      [::
         "multipleReqs" [[ [:: (pair "x" (VInt 1)); (pair "y" (VInt 2))] ]]
      ].

    Example e121_1 : queries_conform extended_wf_schema "Arguments" example121_1.
    Proof.
        by [].
    Qed.

    Let example121_2 : seq (@Query value_eqType) :=
      [::
         "multipleReqs" [[ [:: (pair "y" (VInt 1)); (pair "x" (VInt 2))] ]]
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
    Let example128 : seq (@Query value_eqType) :=
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


    Let example129 : seq (@Query value_eqType) :=
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

    Let example130_1 : @Query value_eqType := on "Dog" {
                                                   [::
                                                      "name" [[ [::] ]]
                                                   ]
                                                 }.
    Example e130_1 : is_consistent wf_schema "Dog" example130_1 &&
                     is_consistent wf_schema "Pet" example130_1.
    Proof.
        by [].
    Qed.

    Let example130_2 : @Query value_eqType := on "Pet" {
                                                   [::
                                                      "name" [[ [::] ]]
                                                   ]
                                                 }.
    Example e130_2 : is_consistent wf_schema "Dog" example130_2 &&
                     is_consistent wf_schema "Pet" example130_2.
    Proof.
        by [].
    Qed.

     Let example130_3 : @Query value_eqType := on "CatOrDog" {
                                                    [::
                                                       on "Dog" {
                                                         [::
                                                            "name" [[ [::] ]]
                                                         ]
                                                       }
                                                    ]
                                                 }.
    Example e130_3 : is_consistent wf_schema "CatOrDog" example130_3.
    Proof.
        by [].
    Qed.

    Let example131_1 : (@Query value_eqType) := on "Int" {
                                                     [::
                                                        "something" [[ [::] ]]
                                                     ]
                                                   }.

    Example e131_1 : all (fun name => ~~is_consistent wf_schema name example131_1) wf_schema.(schema_names).
    Proof.
        by [].
    Qed.

    Let example131_2 : (@Query value_eqType) := on "Dog" {
                                                     [::
                                                        on "Boolean" {
                                                          [::
                                                             "somethingElse" [[ [::] ]]
                                                          ]
                                                        }
                                                     ]
                                                   }.

    Example e131_2 : all (fun name => ~~is_consistent wf_schema name example131_2) wf_schema.(schema_names).
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
    Let example137 : @Query value_eqType := on "Dog" {
                                                 [::
                                                    "barkVolume" [[ [::] ]]
                                                 ]
                                               }.
    Example e137' : is_fragment_spread_possible wf_schema "Dog" "Dog".
    Proof.
        by [].
    Qed.
    
    Example e137 : is_consistent wf_schema "Dog" example137.
    Proof.
        by [].
    Qed.

    Let example138 : @Query value_eqType := on "Cat" {
                                                 [::
                                                    "meowVolume" [[ [::] ]]
                                                 ]
                                               }.
     
    Example e138' : ~~ is_fragment_spread_possible wf_schema "Cat" "Dog".
    Proof.
        by [].
    Qed.

    Example e138 : ~~ is_consistent wf_schema "Dog" example138.
    Proof.
        by [].
    Qed.

    
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Abstract-Spreads-in-Object-Scope
     *)
    Let example139 : @Query value_eqType := on "Pet" {
                                                 [::
                                                    "name" [[ [::] ]]
                                                 ]
                                                }.

    
    Example e139' : is_fragment_spread_possible wf_schema "Pet" "Dog".
    Proof.
        by [].
    Qed.
    
    Example e139 : is_consistent wf_schema "Dog" example139.
    Proof.
        by [].
    Qed.

    Let example140 : @Query value_eqType := on "CatOrDog" {
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
    
    Example e140 : is_consistent wf_schema "Dog" example140.
    Proof.
        by [].
    Qed.


    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Object-Spreads-In-Abstract-Scope
     *)
    Let example141_1 : seq (@Query value_eqType) :=
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

    Let example141_2 : seq (@Query value_eqType) :=
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
    
    
    Let example142_1 : @Query value_eqType := on "Dog" {
                                                 [::
                                                    "barkVolume" [[ [::] ]]
                                                 ]
                                                 }.

    Example e142_1' : ~~ is_fragment_spread_possible wf_schema "Dog" "Sentient".
    Proof.
        by [].
    Qed.

    Example e142_1 : ~~ is_consistent wf_schema "Sentient" example142_1.
    Proof.
        by [].
    Qed.

    
    Let example142_2 : @Query value_eqType := on "Cat" {
                                                 [::
                                                    "meowVolume" [[ [::] ]]
                                                 ]
                                                 }.

    Example e142_2' : ~~ is_fragment_spread_possible wf_schema "Cat" "HumanOrAlien".
    Proof.
        by [].
    Qed.
    
    Example e142_2 : ~~ is_consistent wf_schema "HumanOrAlien" example142_2.
    Proof.
        by [].
    Qed.


    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Abstract-Spreads-in-Abstract-Scope
     *)
    Let example143 : seq (@Query value_eqType) :=
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

    Let example144 : @Query value_eqType := on "Sentient" {
                                                 [::
                                                    "name" [[ [::] ]]
                                                 ]
                                               }.

    Example e144' : ~~ is_fragment_spread_possible wf_schema "Sentient" "Pet".
    Proof.
        by [].
    Qed.

    Example e144 : ~~ is_consistent wf_schema "Pet" example144.
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