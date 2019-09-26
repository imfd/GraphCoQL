(* begin hide *)

From mathcomp Require Import all_ssreflect.

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

Require Import QuerySemantic.

(* end hide *)


Open Scope string_scope.


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

    Lemma cgraph : is_a_conforming_graph wf_schema g.
    Proof.
        by [].
    Qed.
    

    Let wf_graph := ConformedGraph cgraph.


    
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
  



End Example.

