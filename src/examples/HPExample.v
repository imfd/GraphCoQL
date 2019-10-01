(* begin hide *)

From mathcomp Require Import all_ssreflect.

Require Import String.
Require Import QString.

From Equations Require Import Equations.
Require Import GeneralTactics.

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

  Unset Elimination Schemes.
  (** ---- *)
  (** *** Value 
     
     Type that wraps all possible values present in the system.
   *)
  Inductive Value : Type :=
  | VInt : nat -> Value
  | VString : string -> Value
  | VFloat : nat -> nat -> Value
  | VList : seq Value -> Value.

  Set Elimination Schemes.

  (* begin hide *)
  
  (** ---- *)
  (**
     Defining the induction principle for Value.
   *)
  Definition Value_rect (P : Value -> Type)
             (Pl : seq Value -> Type)
             (IH_Int : forall n, P (VInt n))
             (IH_Str : forall s, P (VString s))
             (IH_Float : forall f1 f2, P (VFloat f1 f2))
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
      | VInt n => IH_Int n
      | VString s => IH_Str s
      | VFloat f1 f2 => IH_Float f1 f2
      | VList l => IH_List l (F l)
      end.

  Definition Value_rec (P : Value -> Set) := @Value_rect P.

  Definition Value_ind (P : Value -> Prop)
           (Pl : seq Value -> Type)
             (IH_Int : forall n, P (VInt n))
             (IH_Str : forall s, P (VString s))
             (IH_Float : forall f1 f2, P (VFloat f1 f2))
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
      | VInt n => IH_Int n
      | VString s => IH_Str s
      | VFloat f1 f2 => IH_Float f1 f2
      | VList l => IH_List l (F l)
      end.


  (** We need to prove that Value has a decidable equality procedure,
      we hide it to unclutter the docs
   *)
  Notation vtype := (nat + string + (nat * nat))%type.

  Fixpoint tree_of_value (v : Value) : GenTree.tree vtype  :=
    match v with
    | VInt n => GenTree.Node 0 [:: GenTree.Leaf (inl (inl n))]
    | VString s => GenTree.Node 1 [:: GenTree.Leaf (inl (inr s))]
    | VFloat f1 f2 => GenTree.Node 2 [:: GenTree.Leaf (inr (pair f1 f2))]
    | VList ls => GenTree.Node 3 [seq tree_of_value x | x <- ls]
    end.

  Fixpoint value_of_tree (t : GenTree.tree vtype) : option Value :=
    match t with
    | GenTree.Node 0 [:: GenTree.Leaf (inl (inl n))] => Some (VInt n)
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

  
  Coercion v_of_nat (n : nat) := VInt n.
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
    | VInt _ => if ty is NamedType name then
                 name == "ID"
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


  (** ---- *)
  (**
     We define the schema as the root operation type and its type definitions.
   *)
  Let schema  := GraphQLSchema "Query"  [:: IDType; StringType; FloatType;  StarshipType;  CharacterType; DroidType; HumanType; EpisodeType; SearchResultType; QueryType].


  
  (** ---- *)
  (**
     We prove that the schema is well-formed by simple computation.
   *)
  Lemma sdf : schema.(is_a_wf_schema).
  Proof. by []. Qed.
  


 
  (** ---- *)
  (**
     We build the well-formed schema with the schema, the proof of its well-formedness
     and the predicate that helps determine when a value respects the type.
   *)
  Let wf_schema : wfGraphQLSchema := WFGraphQLSchema sdf (is_valid_value schema).

  (** ---- *)
  (** ** Graph 
        
      We then define the graph displayed in HP.
        
      #<img src="../imgs/HPExample/graph.png" class="img-fluid" alt="Graph">#
        
   *)
    
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
    


  (**
       We define the root node.
   *)
  Let r : @node value_eqType := Node "Query" [::].
  

  (** ---- *)
  (**
       We define the graph as the root node and the edges in the graph.
   *)
  Let g := GraphQLGraph r edges.


  (** ---- *)
  (**
       We prove that the graph conforms to the previous well-formed schema, by simple computation.
   *)
  Lemma cgraph : is_a_conforming_graph wf_schema g.
  Proof.
      by [].
  Qed.
    

  (** ---- *)
  (**
       We build the conformed graph, using the graph and the proof of its conformance.
   *)
  Let wf_graph := ConformedGraph cgraph.


  (** ---- *)
  (** ** Query 
        
        We then define the query.

        #<img src="../imgs/HPExample/query.png" class="img-fluid" alt="Query">#

   *)
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


  (** ---- *)
  (**
       We prove it conforms to the schema by simple computation.     
   *)
  Lemma qbc : queries_conform  wf_schema wf_schema.(query_type) q.
  Proof.
      by [].
  Qed.
  


  (** ---- *)
  (** ** Response
        
        We define the response expected for the previous query.

        #<img src="../imgs/HPExample/response.png" class="img-fluid" alt="Response">#

   *)
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
  

  
  (** ---- *)
  (**
     Finally, we show that executing the previous query in the context of the well-formed schema, and over the conformed graph, starting from the root node, gives us the expected response.
   *)
  Example ev_query_eq_response :  wf_schema, wf_graph ⊢  ⟦ q ⟧ˢ in wf_graph.(root) with wf_coercion = query_response.
  Proof.
      by [].
  Qed.
  


End Example.

