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



Section WrongGraph.

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