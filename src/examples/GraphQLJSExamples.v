(* begin hide *)

From mathcomp Require Import all_ssreflect.

Require Import String.
Require Import QString.

From Equations Require Import Equations.
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
Require Import QueryTactics.

Require Import Response.

Require Import QuerySemantic.
Require Import QuerySemanticsLemmas.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GraphQLJS Example</h1>
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

  Unset Elimination Schemes.
  (** ---- *)
  (** *** Value 
     
     Type that wraps all possible values present in the system.
   *)
  Inductive Value : Type :=
  | VString : string -> Value
  | VList : seq Value -> Value.

  Set Elimination Schemes.

  (* begin hide *)
  
  (** ---- *)
  (**
     Defining the induction principle for Value.
   *)
  Definition Value_rect (P : Value -> Type)
             (Pl : seq Value -> Type)
             (IH_Str : forall s, P (VString s))
             (IH_List : forall l, Pl l -> P (VList l))
             (IH_Nil : Pl [::])
             (IH_Cons : forall v, P v -> forall vs, Pl vs -> Pl (v :: vs))
    :=
    fix loop value : P value :=
      let fix F (qs : seq Value) : Pl qs :=
          match qs with
          | [::] => IH_Nil
          | hd :: tl => IH_Cons hd (loop hd) tl (F tl)
          end
      in
      match value with
      | VString s => IH_Str s
      | VList l => IH_List l (F l)
      end.

  Definition Value_rec (P : Value -> Set) := @Value_rect P.

  Definition Value_ind (P : Value -> Prop)
           (Pl : seq Value -> Type)
             (IH_Str : forall s, P (VString s))
             (IH_List : forall l, Pl l -> P (VList l))
             (IH_Nil : Pl [::])
             (IH_Cons : forall v, P v -> forall vs, Pl vs -> Pl (v :: vs))
    :=
        fix loop value : P value :=
      let fix F (qs : seq Value) : Pl qs :=
          match qs with
          | [::] => IH_Nil
          | hd :: tl => IH_Cons hd (loop hd) tl (F tl)
          end
      in
      match value with
      | VString s => IH_Str s
      | VList l => IH_List l (F l)
      end.


  (** We need to prove that Value has a decidable equality procedure,
      we hide it to unclutter the docs
   *)
  Notation vtype := (string)%type.

  Fixpoint value_size (v : Value) : nat :=
    match v with
    | VList l => (sumn [seq value_size v | v <- l]).+1
    | _ => 1
    end.

  Lemma value_size_gt_1 v : 0 < v.(value_size).
      by case: v.
  Qed.

  Equations? value_eq (v1 v2 : Value) : bool by wf (v1.(value_size)) :=
    {
      value_eq (VString s1) (VString s2) := s1 == s2;
      value_eq (VList [::]) (VList [::]) := true;
      value_eq (VList (v1 :: vs1)) (VList (v2 :: vs2)) :=
        value_eq v1 v2 && value_eq (VList vs1) (VList vs2);
      value_eq _ _ := false
    }. 
   Proof.
     all: do ? [have H := (value_size_gt_1 v1)]; ssromega.
   Qed.
   
   Lemma value_eq_axiom : Equality.axiom value_eq.
   Proof.
     rewrite /Equality.axiom; intros.
     apply: (iffP idP) => [| ->]; last first.
     - funelim (value_eq y y) => //=; first by case: H => ->; apply/eqP.
       case: H1 => Heq1 Heq2; rewrite ?Heq1 ?Heq2 in H H0 *.
         by apply_andP; [apply: H| apply: H0].
     - funelim (value_eq x y) => //= [| /andP [/H -> Heq ] ]; first by move/eqP=> ->.
       congr VList; congr cons.
         by move: (H0 Heq); case.
   Qed.

  Canonical value_eqType := EqType Value (EqMixin value_eq_axiom).

  (* end hide *)


  (** ---- *)
  (** *** Coerce function

      #<strong>coerce</strong># : Value → ResponseNode
 
      This is the function used in the semantics to coerce 
      results into JSON values.

      Scalar value are  simply translated as leaf values, while 
      list values have to be properly formatted as array values.
   *)
  Fixpoint coerce (v : Value) : @ResponseNode (option Value) :=
    match v with
    | VList ls => Array [seq coerce x | x <- ls]
    | _ => Leaf (Some v)
    end.

  
  Coercion v_of_str (s : string) := VString s.


  (** ---- *)
  (** *** Is valid value?
      #<strong>is_valid_value</strong># : type → Value → Bool

      The following predicate checks whether a given value respects 
      the given type. This is used when checking that argument values 
      are used accordingly to the schema, and similarly for graphs.

      For instance, an integer value in this scenario is valid if the 
      type is the ID type. However, a string value is valid for the type 
      String or if it refers to an enum value.
   *)
  Variable (schema : graphQLSchema). 
  Fixpoint is_valid_value (ty : type) (v : Value) : bool :=
    match v with    
    | VString s => if ty is NamedType name then
                    (name == "String")
                    ||
                    if lookup_type schema name is Some (Enum _ { members }) then
                      s \in members
                    else
                      false
                  else
                    false
                                           
    | VList ls => if ty is ListType ty' then
                   all (is_valid_value ty') ls
                 else
                   false

    end.

End Values.


  (** ---- *)
  (**
     We prove here that the coercion is ok, simply for scope...
   *)
  Let wf_coerce : forall v, is_non_redundant (coerce v).
  Proof.
    move=> v.
    elim v using Value_ind  with
        (Pl := fun vs => all (fun v => is_non_redundant (coerce v)) vs) => //=.
    - intros; simp is_non_redundant.
      rewrite all_map; apply/allP => v' Hin /=.
        by move/allP: H => /(_ v' Hin).
    - intros; simp is_non_redundant; apply_andP.
  Qed.
   
  Let wf_coercion := WFCoercion value_eqType coerce wf_coerce.



(** * Example

 *)
Section Example.

 
  Coercion namedType_of_string (s : string) := NamedType s.

  (** ---- *)
  (** ** Schema
      
      As described in HP, the schema is the following:

      #<img src="../imgs/HPExample/schema.png" class="img-fluid" alt="Schema definition">#

   *)
  (**
     We first define the scalar types used in this system.
   *)
  Let StringType := Scalar "String".


  Let EpisodeType := Enum "Episode" { [:: "NEWHOPE" ; "EMPIRE" ; "JEDI" ] }.

  (* The secret backstory is actually implemented as a function that throws error, so
     we omit it for now *)
  Let CharacterType := Interface "Character" {
                                  [::
                                     Field "id" [::] "String" ;
                                     Field "name" [::] "String";
                                     Field "friends" [::] [ "Character" ];
                                     Field "appearsIn" [::] [ "Episode" ]
                                     (* Field "secretBackstory" [::] "String" *)
                                    ]
                                  }.

  Let HumanType := Object "Human" implements [:: "Character"] {
                           [::
                              Field "id" [::] "String" ;
                              Field "name" [::] "String";
                              Field "friends" [::] [ "Character" ];
                              Field "appearsIn" [::] [ "Episode" ];
                              (* Field "secretBackstory" [::] "String"; *)
                              Field "homePlanet" [::] "String"
                           ]
                         }.

  Let DroidType := Object "Droid" implements [:: "Character"] {
                           [::
                              Field "id" [::] "String" ;
                              Field "name" [::] "String";
                              Field "friends" [::] [ "Character" ];
                              Field "appearsIn" [::] [ "Episode" ];
                              (* Field "secretBackstory" [::] "String"; *)
                              Field "primaryFunction" [::] "String"
                           ]
                         }.


  Let QueryType := Object "Query" implements [::] {
                           [::
                              Field "hero" [:: FieldArgument "episode" "Episode"] "Character";
                              Field "human" [:: FieldArgument "id" "String"] "Human";
                              Field "droid" [:: FieldArgument "id" "String"] "Droid"
                           ]
                         }.


  (** ---- *)
  (**
     We define the schema as the root operation type and its type definitions.
   *)
  Let StarWarsSchema  := GraphQLSchema "Query"  [:: StringType; EpisodeType; CharacterType; HumanType; DroidType; QueryType].


  
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
  Let ValidStarWarsSchema : wfGraphQLSchema := WFGraphQLSchema wf_schema (is_valid_value StarWarsSchema).

  (** ---- *)
  (** ** Data 
        
      We then define the graph defined in
      #<a href='https://github.com/graphql/graphql-js/blob/master/src/__tests__/starWarsData.js'>Data</a>#
        
      #<img src="../imgs/HPExample/graph.png" class="img-fluid" alt="Graph">#
        
   *)
  
  Let Luke := Node "Human" [::
                             pair (Label "id" [::]) (VString "1000");
                             pair (Label "name" [::]) (VString "Luke Skywalker");
                             pair (Label "appearsIn" [::]) (VList [::
                                                                     (VString "NEWHOPE");
                                                                     (VString "EMPIRE");
                                                                     (VString "JEDI")
                                                                  ]
                                                           );
                             pair (Label "homePlanet" [::]) (VString "Tatooine")
                          ].
  
  Let Vader := Node "Human" [::
                              pair (Label "id" [::]) (VString "1001");
                              pair (Label "name" [::]) (VString "Darth Vader");
                              pair (Label "appearsIn" [::]) (VList [::
                                                                      (VString "NEWHOPE");
                                                                      (VString "EMPIRE");
                                                                      (VString "JEDI")
                                                                   ]
                                                            );
                             pair (Label "homePlanet" [::]) (VString "Tatooine")
                          ].

  Let Han := Node "Human" [::
                            pair (Label "id" [::]) (VString "1002");
                            pair (Label "name" [::]) (VString "Han Solo");
                            pair (Label "appearsIn" [::]) (VList [::
                                                                    (VString "NEWHOPE");
                                                                    (VString "EMPIRE");
                                                                    (VString "JEDI")
                                                                 ]
                                                          ) 
                         ].
  
  Let Leia := Node "Human" [::
                             pair (Label "id" [::]) (VString "1003");
                             pair (Label "name" [::]) (VString "Leia Organa");
                             pair (Label "appearsIn" [::]) (VList [::
                                                                     (VString "NEWHOPE");
                                                                     (VString "EMPIRE");
                                                                     (VString "JEDI")
                                                                  ]
                                                           );
                             pair (Label "homePlanet" [::]) (VString "Alderaan")
                          ].
  
  Let Tarkin := Node "Human" [::
                               pair (Label "id" [::]) (VString "1004");
                               pair (Label "name" [::]) (VString "Wilhuff Tarkin");
                               pair (Label "appearsIn" [::]) (VList [::
                                                                       (VString "NEWHOPE")
                                                                    ]
                                                             )
                            ].
  
  Let Threepio := Node "Droid" [::
                                 pair (Label "id" [::]) (VString "2000");
                                 pair (Label "name" [::]) (VString "C3-PO");
                                 pair (Label "appearsIn" [::]) (VList [::
                                                                         (VString "NEWHOPE");
                                                                         (VString "EMPIRE");
                                                                         (VString "JEDI")
                                                                      ]
                                                               );
                                 pair (Label "primaryFunction" [::]) (VString "Protocol")
                              ].

  
  Let Artoo := Node "Droid" [::
                              pair (Label "id" [::]) (VString "2001");
                              pair (Label "name" [::]) (VString "R2-D2");
                              pair (Label "appearsIn" [::]) (VList [::
                                                                      (VString "NEWHOPE");
                                                                      (VString "EMPIRE");
                                                                      (VString "JEDI")
                                                                   ]
                                                            );
                              pair (Label "primaryFunction" [::]) (VString "Astromech")
                           ].

  Eval compute in coerce ((VList [::
                                                                      (VString "NEWHOPE");
                                                                      (VString "EMPIRE");
                                                                      (VString "JEDI")
                                                                   ]
                                                            )).

  Let Root := @Node value_eqType "Query" [::].

  Let human (id : string) := @Label value_eqType "human" [:: pair "id" (VString id)].

  Let droid (id : string) := @Label value_eqType "droid" [:: pair "id" (VString id)].

  Let hero (episode : string) := (Label "hero" [:: pair "episode" (VString episode)]).
  
  Let friends := @Label value_eqType "friends" [::].

  Let appearsIn := @Label value_eqType "appearsIn" [::].
  
  Let edges : seq (@node value_eqType * label * node) :=
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

   (** ---- *)
  (**
       We define the graph as the root node and the edges in the graph.
   *)
  Let StarWarsGraph := GraphQLGraph Root edges.


  (** ---- *)
  (**
       We prove that the graph conforms to the previous well-formed schema, by simple computation.
   *)
 
  Let graph_conforms : is_a_conforming_graph ValidStarWarsSchema StarWarsGraph.
  Proof.
      by [].
  Qed.
    

  (** ---- *)
  (**
       We build the conformed graph, using the graph and the proof of its conformance.
   *)
  Let ValidStarWarsGraph := ConformedGraph graph_conforms.




  (** ---- *)
  (** ** Query 
        
        We then define the queries.

        #<img src="../imgs/HPExample/query.png" class="img-fluid" alt="Query">#

   *)

  Let val v := Leaf (Some (VString v)).
  
  (** *** Basic Queries

   *)
  (** **** It correctly identifies R2-D2 as the hero of the Star Wars Saga
   *)
  Let q1 := @Query value_eqType (Some "HeroNameQuery")
                  [::
                     "hero" [[ [::] ]] {
                       [::
                          "name" [[ [::] ]]
                       ]
                     }
                  ].

  Let q1_conforms : query_conforms ValidStarWarsSchema q1. by []. Qed.
  
  Let result1 :=   [::
                     pair "hero"
                     (Response.Object
                               [::
                                  pair "name" (val "R2-D2")
                               ]
                     )
                  ].

   Goal execute_query ValidStarWarsSchema ValidStarWarsGraph wf_coercion q1 = result1.
       by [].
   Qed.

   (** **** It allows us to query for the ID and friends of R2-D2

    *)
  

   Let q2 := @Query value_eqType (Some "HeroNameAndFriendsQuery")
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

  Let q2_conforms : query_conforms ValidStarWarsSchema q2. by []. Qed.

   Ltac exec :=
    repeat
      match goal with
      | [ H : lookup_field_in_type _ _ _ = _ |- context [ lookup_field_in_type _ _ _] ] => rewrite H /=
      | [ H : (field_seq_value (nprops _) _) = _ |- context [ field_seq_value (nprops _) _] ] => rewrite H /=

      | [|- context [ lookup_field_in_type _ _ _] ] => lookup
      | [|- context [ field_seq_value ?u.(nprops) ] ] =>
        let Hv := fresh "Hv" in
        let v := fresh "v" in
        let vs := fresh "vs" in
        case Hv : (field_seq_value u.(nprops) _) => [ v |] /=

      | [H : is_true (is_valid_response_value _ _ _) |- context [if is_valid_response_value _ _ _ then _ else _] ] =>
        rewrite H /=

      | [H : is_valid_response_value _ _ _ = _ |- context [if is_valid_response_value _ _ _ then _ else _] ] =>
        rewrite H /=

      | [|- context [if is_valid_response_value _ _ _ then _ else _] ] =>
        let Hvalid := fresh "Hvalid" in
        case: ifP => Hvalid //=
                      
      | [H : (return_type ?f) = _ |- context [ return_type ?f ] ] => rewrite H /=

      | [|- context[ execute_selection_set_unfold_clause_4_clause_1 _ _ _ _ _ (return_type ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(return_type) => [rty | rty] /=

      | [|- context[ execute_selection_set_unfold_clause_4_clause_1_clause_2 _ _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
                               
      | [|- context[ execute_selection_set_unfold_clause_5_clause_1 _ _ _ _ _ (return_type ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(return_type) => [rty | rty] /=

      | [|- context[ execute_selection_set_unfold_clause_5_clause_1_clause_2 _ _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
                               
      | [ H : does_fragment_type_apply _ _ _ = _ |- context [ does_fragment_type_apply _ _ _] ] => rewrite H /=

      | [|- context [execute_selection_set_unfold_clause_6 _ _ _ _ _ _ (does_fragment_type_apply _ _ _)] ] =>
        let Hfapplies := fresh "Hfapplies" in
        case Hfapplies : does_fragment_type_apply => //=
   
      | [ |- context [ _, _ ⊢ ⟦ _ ⟧ˢ in _ with _] ] => simp execute_selection_set
      end.
   
  Let result2 :=   [::
                     pair "hero"
                     (Response.Object
                     [::
                        pair "id" (val "2001");
                        pair "name" (val "R2-D2");
                        pair "friends"
                             (Array
                             [::
                                Response.Object
                                [::
                                   pair "name" (val "Luke Skywalker")
                                ];
                                Response.Object
                                  [::
                                     pair "name" (val "Han Solo")
                                  ];
                                Response.Object
                                  [::
                                     pair "name" (val "Leia Organa")
                                  ]
                             ])
                     ])
                  ].


  Goal execute_query ValidStarWarsSchema ValidStarWarsGraph wf_coercion q2 = result2.
      by [].
  Qed.


  (** **** Nested Queries

   *)
  (** It allows us to query for the friends of friends of R2-D2
     
   *)

   Let q3 := @Query value_eqType (Some "HeroNameAndFriendsQuery")
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

   Let q3_conforms : query_conforms ValidStarWarsSchema q3. by []. Qed.


   Let result3 := [::
                     pair "hero"
                     (Response.Object
                     [::
                        pair "name" (val "R2-D2");
                                
                        pair "friends"
                             (Array
                             [::
                                Response.Object
                                [::
                                   pair "name" (val "Luke Skywalker");
                                   pair "appearsIn" (Array [:: val "NEWHOPE";
                                                              val "EMPIRE";
                                                              val "JEDI"
                                                    ]);
                                   pair "friends"
                                   (Array
                                      [::
                                         Response.Object
                                         [::
                                            pair "name" (val "Han Solo")
                                         ];
                                         Response.Object
                                         [::
                                            pair "name" (val "Leia Organa")
                                         ];
                                         Response.Object
                                         [::
                                            pair "name" (val "C3-PO")
                                         ];
                                         Response.Object
                                         [::
                                            pair "name" (val "R2-D2")
                                         ]
                                      ]
                                   )
                                ];
                                Response.Object
                                  [::
                                     pair "name" (val "Han Solo");
                                     pair "appearsIn" (Array [:: val "NEWHOPE";
                                                                val "EMPIRE";
                                                                val "JEDI"
                                                      ]);
                                     pair "friends"
                                   (Array
                                      [::
                                         Response.Object
                                         [::
                                            pair "name" (val "Luke Skywalker")
                                         ];
                                         Response.Object
                                         [::
                                            pair "name" (val "Leia Organa")
                                         ];
                                         Response.Object
                                         [::
                                            pair "name" (val "R2-D2")
                                         ]
                                      ]
                                   )
                                  ];
                                Response.Object
                                  [::
                                     pair "name" (val "Leia Organa");
                                     pair "appearsIn" (Array [:: val "NEWHOPE";
                                                                val "EMPIRE";
                                                                val "JEDI"
                                                      ]);
                                     pair "friends"
                                   (Array
                                      [::
                                         Response.Object
                                         [::
                                            pair "name" (val "Luke Skywalker")
                                         ];
                                         
                                         Response.Object
                                         [::
                                            pair "name" (val "Han Solo")
                                         ];
                                         Response.Object
                                         [::
                                            pair "name" (val "C3-PO")
                                         ];
                                         Response.Object
                                         [::
                                            pair "name" (val "R2-D2")
                                         ]
                                      ]
                                   )
                                  ]
                             ])
                     ])
                 ].

   Goal execute_query ValidStarWarsSchema ValidStarWarsGraph wf_coercion q3 = result3.
       by [].
   Qed.

   
   (** *** Using IDs and query parameters to refetch objects

    *)
   (** It allows us to query for Luke Skywalker directly, using his ID

    *)   
   Let q4 := @Query value_eqType (Some "FetchLukeQuery")
                   [::
                      "human" [[ [:: pair "id" (VString "1000")] ]] {
                        [::
                           "name" [[ [::] ]]
                        ]
                      }
                   ].

   Let q4_conforms : query_conforms ValidStarWarsSchema q4. by []. Qed.

   Let result4 := [::
                    pair "human"
                    (Response.Object
                     [::
                        pair "name" (val "Luke Skywalker")
                     ]
                    )
                 ].

   Goal execute_query ValidStarWarsSchema ValidStarWarsGraph wf_coercion q4 = result4.
       by [].
   Qed.


   (** **** pass an invalid ID to get null back.

    *)
 
  Let q5 := @Query value_eqType (Some "humanQuery")
                   [::
                      "human" [[ [:: pair "id" (VString "not a valid id")] ]] {
                        [::
                           "name" [[ [::] ]]
                        ]
                      }
                   ].

   Let q5_conforms : query_conforms ValidStarWarsSchema q5. by []. Qed.

   Let result5 := [::
                    pair "human" (@Leaf (option value_eqType) None)
                 ].

   Goal execute_query ValidStarWarsSchema ValidStarWarsGraph wf_coercion q5 = result5.
       by [].
   Qed.



   (** *** Using aliases to change the key in the response

    *)
   (** **** Allows us to query for Luke, changing his key with an alias

    *)

   Let q6 := @Query value_eqType (Some "FetchLukeAliased")
                   [::
                      "luke":"human" [[ [:: pair "id" (VString "1000")] ]] {
                        [::
                           "name" [[ [::] ]]
                        ]
                      }
                   ].

   Let q6_conforms : query_conforms ValidStarWarsSchema q6. by []. Qed.

   Let result6 := [::
                    pair "luke"
                    (Response.Object
                     [::
                        pair "name" (val "Luke Skywalker")
                     ]
                    )
                 ].

   Goal execute_query ValidStarWarsSchema ValidStarWarsGraph wf_coercion q6 = result6.
       by [].
   Qed.


   (** **** Allows us to query for both Luke and Leia, using two root fields and an alias

    *)

   Let q7 := @Query value_eqType (Some "FetchLukeAndLeiaAliased")
                   [::
                      "luke":"human" [[ [:: pair "id" (VString "1000")] ]] {
                                       [::
                                          "name" [[ [::] ]]
                                       ]
                                     };
                      "leia":"human" [[ [:: pair "id" (VString "1003")] ]] {
                                       [::
                                          "name" [[ [::] ]]
                                       ]
                                     }
                   ].

   Let q7_conforms : query_conforms ValidStarWarsSchema q7. by []. Qed.

   Let result7 := [::
                    pair "luke"
                    (Response.Object
                     [::
                        pair "name" (val "Luke Skywalker")
                     ]
                    );
                    pair "leia"
                    (Response.Object
                     [::
                        pair "name" (val "Leia Organa")
                     ]
                    )
                 ].

   Goal execute_query ValidStarWarsSchema ValidStarWarsGraph wf_coercion q7 = result7.
       by [].
   Qed.



   (** *** Uses fragments to express more complex queries

    *)

   (** **** Allows us to query using duplicated content

    *)
   Let q8 := @Query value_eqType (Some "DuplicateFields")
                   [::
                      "luke":"human" [[ [:: pair "id" (VString "1000")] ]] {
                                       [::
                                          "name" [[ [::] ]];
                                          "homePlanet" [[ [::] ]]
                                       ]
                                     };
                      "leia":"human" [[ [:: pair "id" (VString "1003")] ]] {
                                       [::
                                          "name" [[ [::] ]];
                                          "homePlanet" [[ [::] ]]
                                       ]
                                     }
                   ].

   Let q8_conforms : query_conforms ValidStarWarsSchema q8. by []. Qed.

   Let result8 := [::
                    pair "luke"
                    (Response.Object
                     [::
                        pair "name" (val "Luke Skywalker");
                        pair  "homePlanet" (val "Tatooine")
                     ]
                    );
                    pair "leia"
                    (Response.Object
                     [::
                        pair "name" (val "Leia Organa");
                        pair "homePlanet" (val "Alderaan")
                     ]
                    )
                 ].

   Goal execute_query ValidStarWarsSchema ValidStarWarsGraph wf_coercion q8 = result8.
       by [].
   Qed.


   (** **** Allows us to use a fragment to avoid duplicating content
       
       Not doing it bc fragments are not implemented. Instead, checking that inline fragments 
       are still ok.
    *)

   Let q9 := @Query value_eqType (Some "DuplicateFields")
                   [::
                      "luke":"human" [[ [:: pair "id" (VString "1000")] ]] {
                                       [::
                                          on "Human" {
                                            [::
                                               "name" [[ [::] ]];
                                               "homePlanet" [[ [::] ]]
                                            ]
                                          }
                                       ]
                                     };
                      "leia":"human" [[ [:: pair "id" (VString "1003")] ]] {
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

   Let q9_conforms : query_conforms ValidStarWarsSchema q9. by []. Qed.

   Let result9 := [::
                    pair "luke"
                    (Response.Object
                     [::
                        pair "name" (val "Luke Skywalker");
                        pair  "homePlanet" (val "Tatooine")
                     ]
                    );
                    pair "leia"
                    (Response.Object
                     [::
                        pair "name" (val "Leia Organa");
                        pair "homePlanet" (val "Alderaan")
                     ]
                    )
                 ].

   Goal execute_query ValidStarWarsSchema ValidStarWarsGraph wf_coercion q9 = result9.
       by [].
   Qed.