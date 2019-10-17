(* begin hide *)

From mathcomp Require Import all_ssreflect.

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

Require Import Response.

Require Import QuerySemantic.

(* end hide *)


Open Scope string_scope.


Section Values.

  Inductive Scalar : Type :=
  | VInt : nat -> Scalar
  | VBool: bool -> Scalar            
  | VString : string -> Scalar
  | VFloat : nat -> nat -> Scalar.
 
  

  (** We need to prove that Value has a decidable equality procedure,
      we hide it to unclutter the docs
   *)
  (* begin hide *)
  Notation vtype := (nat + bool + string + (nat * nat))%type.

  Definition tuple_of_scalar (v : Scalar) :=
    match v with
    | VInt n => inl (inl (inl n))
    | VBool b => inl (inl (inr b))
    | VString s => inl (inr s)
    | VFloat n1 n2 => inr (n1, n2)
    end.

  Definition scalar_of_tuple (t : vtype) : Scalar :=
    match t with
    | inl (inl (inl n)) => VInt n
    | inl (inl (inr b)) => VBool b
    | inl (inr s) => VString s
    | inr (n1, n2) => VFloat n1 n2
    end.

  Lemma tuple_of_scalarK : cancel tuple_of_scalar scalar_of_tuple.
  Proof. by case; case.
  Qed.
   
  Canonical scalar_eqType := EqType Scalar (CanEqMixin tuple_of_scalarK).
  (* end hide *)
 
  Definition coerce : Scalar -> Scalar := id.

  
 
  Variable (schema : graphQLSchema). 
  Fixpoint is_valid_scalar_value (ty : type) (v : Scalar) : bool :=
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



Section WrongGraph.

  Coercion namedType_of_string (s : string) := NamedType s.


  
  Let IDType := scalar "ID".
  Let StringType := scalar "String".
  Let FloatType := scalar "Float".


  
  Let StarshipType := object "Starship" implements [::] {
                              [:: Schema.Field "id" [::] "ID";
                                  Schema.Field "name" [::] "String";
                                  Schema.Field "length" [::] "Float"
                              ]
                            }.

  Let CharacterType := interface "Character" {
                                  [::
                                     Schema.Field "id" [::] "ID" ;
                                     Schema.Field "name" [::] "String";
                                     Schema.Field "friends" [::] [ "Character" ]
                                    ]
                                  }.

  
  Let DroidType := object "Droid" implements [:: "Character"] {
                           [::
                              Schema.Field "id" [::] "ID" ;
                              Schema.Field "name" [::] "String";
                              Schema.Field "friends" [::] [ "Character" ];
                              Schema.Field "primaryFunction" [::] "String"
                           ]
                         }.
  
  
  Let HumanType := object "Human" implements [:: "Character"] {
                           [::
                              Schema.Field "id" [::] "ID" ;
                              Schema.Field "name" [::] "String";
                              Schema.Field "friends" [::] [ "Character" ];
                              Schema.Field "starships" [::] [ "Starship" ]
                           ]
                         }.

  Let EpisodeType := enum "Episode" { [:: "NEWHOPE" ; "EMPIRE" ; "JEDI" ] }.


  Let SearchResultType := union "SearchResult" { [:: "Human" ; "Droid" ; "Starship"] }.


  Let QueryType := object "Query" implements [::] {
                           [::
                              Schema.Field "hero" [:: FieldArgument "episode" "Episode"] "Character";
                              Schema.Field "search" [:: FieldArgument "text" "String"] [ "SearchResult" ]
                           ]
                         }.

  Let schema  := GraphQLSchema "Query"  [:: IDType; StringType; FloatType;  StarshipType;  CharacterType; DroidType; HumanType; EpisodeType; SearchResultType; QueryType].


  Lemma sdf : schema.(is_a_wf_schema).
  Proof. by []. Qed.
  


 

  Let wf_schema : wfGraphQLSchema := WFGraphQLSchema sdf.
  
  (** Some examples of graph's not conforming to the schema **)

  Let r : @node scalar_eqType := Node "Query" [::].
  
  (** Root node does not have same type as query type **)
  Let edges1 : seq (@node scalar_eqType * @label scalar_eqType * @node scalar_eqType) := [::].
  
  Let r1 : @node scalar_eqType := Graph.Node "Human" [::].
  
  Let g := GraphQLGraph r1 edges1.



  
  (** Arguments are incorrect **)

  Let edges2 : seq (@node scalar_eqType * @label scalar_eqType * @node scalar_eqType) :=
    [:: (pair
           (pair
              (Node "Query" [::])

              (Label "search" [:: pair "wrong_Arg" (SValue (VString "L"))]))          (* <--- Wrong name for argument *)

           (Node "Starship" [::
                               (pair (Label  "id" [::]) (SValue (VInt 3000)));
                               (pair (Label "name" [::]) (SValue (VString "Falcon"))); 
                               (pair (Label "length" [::]) (SValue (VFloat 34 37)))
                            ]
           )
        )
    ].

  
  Let g2 := GraphQLGraph r edges2.
  
  Example eNc : ~ edges_conform wf_schema is_valid_scalar_value g2.
  Proof. by [].
  Qed.
  
  
  (** Types are incorrect **)
  
  Let edges3 : seq (@node scalar_eqType * @label scalar_eqType * @node scalar_eqType) :=
    [:: pair
        (pair (Node "Human" [::
                               (pair (Label "id" [::]) (SValue (VInt 1000)));
                               (pair (Label "name" [::]) (SValue (VString "Luke")))
                            ]
              )
              (Label "friends" [::])
        )
        (Node "Starship" [::
                            (pair (Label "id" [::]) (SValue (VInt 2001)));
                            (pair (Label "name" [::]) (SValue (VString "R2-)D2")));
                            (pair (Label "primaryFunction" [::]) (SValue (VString "Astromech")))
                         ]
        )
    ].
  
  Let r3 : @node string_eqType := Node "Query" [::].
  
    Let g3 := GraphQLGraph r edges3.
    
    Example eNc3 : ~ edges_conform wf_schema is_valid_scalar_value g3.
    Proof. by [].
    Qed.




    Let edges4 : seq (@node scalar_eqType * label * node) :=
      [:: pair
          (pair (Node "Query" [::])
                (Label "search" [:: (pair "wrong_Arg" (SValue (VString "L")))])
          )
          (Node "Other" [::
                           (pair (Label "id" [::]) (SValue (VInt 3000))); (* <--- Type is not in union *)
                           (pair (Label "name" [::]) (SValue (VString "Falcon"))); 
                           (pair (Label "length" [::]) (SValue (VFloat 34 37)))
                        ]
          )
      ].

    Let r4 : @node scalar_eqType := Node "Query" [::].

    Let g4 := GraphQLGraph r edges4.
    
    Example eNc4 : ~ edges_conform wf_schema is_valid_scalar_value g4.
    Proof. by [].
    Qed.



    (** Label's are incorrect **)

    Let edges5 : seq (@node scalar_eqType * @label scalar_eqType * @node scalar_eqType) :=
      [:: pair
          (pair (Node "Query" [::])
                (Label "search" [:: (pair "wrong_Arg" (SValue (VString "L")))])
          )
          (Node "Starship" [::
                              (pair (Label "id" [::]) (SValue (VInt 3000)));
                              (pair (Label "name" [:: (pair "wrong" (SValue (VString "arg")))]) (SValue (VString "Falcon"))); (* <--- invalid argument in field*) 
                              (pair (Label "length" [::]) (SValue (VFloat 34 37)))
                           ]
          )
      ].

    
    Let g5 := GraphQLGraph r edges5.

    
    Example fNc : ~ nodes_conform wf_schema is_valid_scalar_value g5.(nodes).
    Proof. by [].
    Qed.
    
End WrongGraph.