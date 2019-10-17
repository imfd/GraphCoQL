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

Require Import Response.

Require Import QuerySemantics.

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


Section GraphQLSpecExamples.
  (**
     Examples from section Validation in the specification.

     https://graphql.github.io/graphql-spec/June2018/#sec-Validation

   *)

  
  Coercion namedType_of_string (s : string) := NamedType s.
  
  Let StringScalar := scalar "String".
  Let BooleanScalar := scalar "Boolean".
  Let IntScalar := scalar "Int".
  Let FloatScalar := scalar "Float".


  Let QueryType := object "Query" implements [::] {
                         [::
                            (Field "dog" [::] "Dog")
                         ]
                       }.
  
  Let DogCommandEnum := enum "DogCommand" { [:: "SIT"; "DOWN"; "HEEL"] }.

  Let DogType := object "Dog" implements [:: "Pet"] {
                         [::
                            (Field "name" [::] "String");
                            (Field "nickname" [::] "String");
                            (Field "barkVolume" [::] "Int");
                            (Field "doesKnowCommand" [:: (FieldArgument "dogCommand" "DogCommand")] "Boolean");
                            (Field "isHousetrained" [:: (FieldArgument "atOtherHomes" "Boolean")] "Boolean");
                            (Field "owner" [::] "Human")
                         ]
                       }.

  Let SentientInterface := interface "Sentient" {
                                      [::
                                         (Field "name" [::] "String")
                                      ]
                                    }.
  
  Let PetInterface := interface "Pet" {
                                 [::
                                    (Field "name" [::] "String")
                                 ]
                               }.



  Let AlienType := object "Alien" implements [:: "Sentient"] {
                           [::
                              (Field "name" [::] "String");
                              (Field "homePlanet" [::] "String")
                           ]
                         }.

  Let HumanType := object "Human" implements [:: "Sentient"] {
                           [::
                              (Field "name" [::] "String")
                           ]
                         }.

  Let CatCommandEnum := enum "CatCommand" {[:: "JUMP" ]}.

  Let CatType := object "Cat" implements [:: "Pet" ] {
                         [::
                            (Field "name" [::] "String");
                            (Field "nickname" [::] "String");
                            (Field "doesKnowCommand" [:: (FieldArgument "catCommand" "CatCommand")] "Boolean");
                            (Field "meowVolume" [::] "Int")
                         ]
                       }.

  Let CatOrDogUnion := union "CatOrDog" { [:: "Cat"; "Dog"] }.

  Let DogOrHumanUnion := union "DogOrHuman" { [:: "Dog"; "Human"] }.

  Let HumanOrAlienUnion := union "HumanOrAlien" { [:: "Human"; "Alien"] }.
  

  Let schema := GraphQLSchema "Query" [:: StringScalar; BooleanScalar; IntScalar; FloatScalar;
                                 QueryType;
                                 DogCommandEnum; DogType;
                                   SentientInterface; PetInterface;
                                     AlienType; HumanType;
                                       CatCommandEnum; CatType;
                                         CatOrDogUnion; DogOrHumanUnion; HumanOrAlienUnion].

  Let schwf : schema.(is_a_wf_schema).
  Proof. by []. Qed.

  Let wf_schema : wfGraphQLSchema := WFGraphQLSchema schwf.

  Section FieldValidation.
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Validation.Fields
     *)

    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selections-on-objects-Interfaces-and-Unions-Types
     *)
    Let example102 : seq (@Selection scalar_eqType) :=  [::
                                                      on "Dog" {
                                                        [::
                                                           "meowVolume" [[ [::] ]]
                                                        ]
                                                      }
                                                   ].
    
    Let example102' :  seq (@Selection scalar_eqType) := [::
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
    Example e102 : ~~ (selections_conform is_valid_scalar_value wf_schema "Dog" example102 || selections_conform is_valid_scalar_value wf_schema "Dog" example102').
    Proof. by []. Qed.


    Let example103 : seq (@Selection scalar_eqType) := [::
                                                     (* on "Pet" { *)
                                                     (* [:: *)
                                                     "name" [[ [::] ]]
                                                     (* ] *)
                                                     (* } *)
                                                  ].

    
    Example e103 : selections_conform is_valid_scalar_value wf_schema "Pet" example103.
    Proof. by []. Qed.

    

    Let example104 : seq (@Selection scalar_eqType) := [::
                                                     (* on "Pet" { *)
                                                     (* [:: *)
                                                     "nickname" [[ [::] ]]
                                                     (* ] *)
                                                     (* } *)
                                                  ].

    Example e104 : ~~ selections_conform is_valid_scalar_value wf_schema "Pet" example104.
    Proof. by []. Qed.

    Example e104' : all (fun implementor => selections_conform is_valid_scalar_value wf_schema implementor example104) (get_possible_types wf_schema "Pet").
    Proof.
        by [].
    Qed.
    

    Let example105 : seq (@Selection scalar_eqType) := [::
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

    Example e105 : selections_conform is_valid_scalar_value wf_schema "CatOrDog" example105.
    Proof. by []. Qed.

    Let example106 : seq (@Selection scalar_eqType) := [::
                                                     "name" [[ [::] ]];
                                                     "barkVolume" [[ [::] ]]
                                                  ].

    Example e106 : ~~ selections_conform is_valid_scalar_value wf_schema "CatOrDog" example106.
    Proof. by []. Qed.

    

    Section FieldSelectionMerging.
      (* Redefining only to ease reading -- Another option would be to use [selections_conform is_valid_scalar_value] but this seems simpler *)
      Definition are_renaming_consistent (s : wfGraphQLSchema)
                 (ts : Name) (σs : seq (@Selection scalar_eqType)) := are_renaming_consistent s [seq (pair ts σ) | σ <- σs]. 

      Let example107_1 : seq (@Selection scalar_eqType) := [::
                                                         "name" [[ [::] ]];
                                                         "name" [[ [::] ]]
                                                      ].
      Let example107_2 : seq (@Selection scalar_eqType) := [::
                                                         "otherName" : "name" [[ [::] ]];
                                                         "otherName" : "name" [[ [::] ]]
                                                      ].

      Example e107_1 : are_renaming_consistent wf_schema "Dog" example107_1.
      Proof.
          by [].
      Qed.

      Example e107_2 : are_renaming_consistent wf_schema "Dog" example107_2.
      Proof.
          by [].
      Qed.


      Let example108 : seq (@Selection scalar_eqType) := [::
                                                       "name" : "nickname" [[ [::] ]];
                                                       "name" [[ [::] ]]
                                                    ].

      Example e108 : ~~ are_renaming_consistent wf_schema "Dog" example108.
      Proof.
          by [].
      Qed.

      Let example109 := [::
                          "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT")) ] ]];
                          "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT"))] ]]
                       ].

      Example e109 : are_renaming_consistent wf_schema "Dog" example109.
      Proof.
          by [].
      Qed.
      
      (**
       Omitting examples with variables since they are not implemented. 
       *)
      Let example110_1 := [::
                            "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT"))] ]];
                            "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "HEEL"))] ]]
                         ].
      
      Let example110_2 := [::
                            "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT"))] ]];
                            "doesKnowCommand" [[ [::] ]]
                         ].

      Example e110_1 : ~~ are_renaming_consistent wf_schema "Dog" example110_1.
      Proof.
          by [].
      Qed.
      
      Example e110_2 : ~~ are_renaming_consistent wf_schema "Dog" example110_2.
      Proof.
          by [].
      Qed.


      Let example111_1 : seq (@Selection scalar_eqType) := [::
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

      Example e111_1 : are_renaming_consistent wf_schema "Pet" example111_1.
      Proof.
          by [].
      Qed.

      Let example111_2 : seq (@Selection scalar_eqType) := [::
                                                         on "Dog" {
                                                           [::
                                                              "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT"))] ]]
                                                           ]
                                                         };
                                                         
                                                         on "Cat" {
                                                              [::
                                                                 "doesKnowCommand" [[ [:: ("catCommand", SValue (VString "JUMP"))] ]]
                                                              ]
                                                            }
                                                      ].

      Example e111_2 : are_renaming_consistent wf_schema "Pet" example111_2.
      Proof.
          by [].
      Qed.
      

      Let example112 : seq (@Selection scalar_eqType) := [::
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

      Example e112 : ~~ are_type_compatible wf_schema [seq pair "Pet" q | q <- example112].
      Proof.
          by [].
      Qed.

      Example e112' : ~~ selections_conform is_valid_scalar_value wf_schema "Pet" example112.
      Proof.
          by [].
      Qed.
      
      
    End FieldSelectionMerging.


    Section LeafFieldSelections.
      (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Leaf-Field-Selections
       *)

      Let example113 : seq (@Selection scalar_eqType) := [::
                                                       "barkVolume" [[ [::] ]]
                                                    ].
      
      Example e113 : selections_conform is_valid_scalar_value wf_schema "Dog" example113.
      Proof.
          by [].
      Qed.

      Let example114 : seq (@Selection scalar_eqType) :=
        [::
           "barkVolume" [[ [::] ]] {
             [::
                "sinceWhen" [[ [::] ]]
             ]
           }
        ].

      Example e114 : ~~ selections_conform is_valid_scalar_value wf_schema "Dog" example114.
      Proof.
          by [].
      Qed.


      (**
       Example 115 uses schema extension, which is not implemented but we can manage around it.
       *)
      Let ExtendedSelectionType := object "ExtendedSelection" implements [::] {
                                       [::
                                          (Field "dog" [::] "Dog");
                                          (Field "human" [::] "Human");
                                          (Field "pet" [::] "Pet");
                                          (Field "catOrDog" [::] "CatOrDog")
                                       ]
                                     }.
      (* For some reason this gets stuck trying to compute wf... ? *)
      (* Let extended_schema := GraphQLSchema "ExtendedSelection" *)
      (*                                     (ExtendedSelectionType :: schema.(type_definitions)). *)

      Let extended_schema := GraphQLSchema "ExtendedSelection"
                                          [:: StringScalar; BooleanScalar; IntScalar; FloatScalar;
                                             ExtendedSelectionType;
                                             DogCommandEnum; DogType;
                                               SentientInterface; PetInterface;
                                                 AlienType; HumanType;
                                                   CatCommandEnum; CatType;
                                                     CatOrDogUnion; DogOrHumanUnion; HumanOrAlienUnion].

      Let extended_schwf : extended_schema.(is_a_wf_schema).
      Proof. by []. Qed.

      Let extended_wf_schema : wfGraphQLSchema := WFGraphQLSchema extended_schwf.

      Let example116_1 : seq (@Selection scalar_eqType) :=
        [::
           "human" [[ [::] ]]
        ].

      Example e116_1 : ~~selections_conform is_valid_scalar_value extended_wf_schema "ExtendedSelection" example116_1.
      Proof.
          by [].
      Qed.

      Let example116_2 : seq (@Selection scalar_eqType) :=
        [::
           "pet" [[ [::] ]]
        ].

      Example e116_2 : ~~selections_conform is_valid_scalar_value extended_wf_schema "ExtendedSelection" example116_2.
      Proof.
          by [].
      Qed.

      Let example116_3 : seq (@Selection scalar_eqType) :=
        [::
           "catOrDog" [[ [::] ]]
        ].

      Example e116_3 : ~~selections_conform is_valid_scalar_value extended_wf_schema "ExtendedSelection" example116_3.
      Proof.
          by [].
      Qed.
      
    End LeafFieldSelections.

  End FieldValidation.


  Section ValidArguments.
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Argument-Names
     *)

    Let example117_1 : seq (@Selection scalar_eqType) :=
      [::
         "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT"))] ]]
      ].

    Example e117_1 : selections_conform is_valid_scalar_value wf_schema "Dog" example117_1.
    Proof.
        by [].
    Qed.

    (**
       Not including the directive @include since directives are not implemented.
     *)
    Let example117_2 : seq (@Selection scalar_eqType) :=
      [::
         "isHousetrained" [[ [:: ("atOtherHomes", SValue (VBool true))] ]]
      ].

    Example e117_2 : selections_conform is_valid_scalar_value wf_schema "Dog" example117_2.
    Proof.
      by [].
    Qed.


    Let example_118 : seq (@Selection scalar_eqType) :=
      [::
         "doesKnowCommand" [[ [:: ("command", SValue (VString "CLEAN_UP_HOUSE")) ] ]]
      ].

    Example e118 : ~~selections_conform is_valid_scalar_value wf_schema "Dog" example_118.
    Proof.
        by [].
    Qed.

    (**
       Example 119 is not included since it checks the directive @include
       and directives are not implemented.
     *)


    Let ArgumentsType := object "Arguments" implements [::] {
                                 [::
                                    (Field "multipleReqs" [::
                                                                    FieldArgument "x" "Int";
                                                                    FieldArgument "y" "Int"
                                                                 ]
                                                  "Int");
                                    (Field "booleanArgField" [::
                                                                       FieldArgument "booleanArg" "Boolean"
                                                                    ]
                                                  "Boolean");
                                    (Field "floatArgField" [::
                                                                     FieldArgument "floatArg" "Float"
                                                                  ]
                                                  "Float");
                                    (Field "intArgField" [::
                                                                   FieldArgument "intArg" "Int"
                                                                ]
                                                  "Int");
                                    (* (Field "nonNullBooleanArgField" *)
                                    (*               [:: *)
                                    (*                  FieldArgument "nonNullBooleanArg" "Boolean" *)
                                    (*               ] *)
                                    (*               "Boolean"); *)

                                    (Field "booleanListArgField"
                                                  [::
                                                     FieldArgument "booleanListArg" [ "Boolean" ]
                                                  ]
                                                  [ "Boolean" ])

                                      (* (Field "optionalNonNullBooleanArgField" *)
                                      (*               [:: *)
                                      (*                  FieldArgument "optionalNonNullBooleanArgField" "Boolean" *)
                                      (*               ] *)
                                      (*               "Boolean") *)
                                      
                                                                              
                                 ]
                               }.

    Let ExtendedSelectionType := object "ExtendedSelection" implements [::] {
                                     [::
                                        (Field "dog" [::] "Dog");
                                        (Field "arguments" [::] "Arguments")

                                     ]
                                   }.

    Let extended_schema := GraphQLSchema "ExtendedSelection"
                                        [:: StringScalar; BooleanScalar; IntScalar; FloatScalar;
                                           ExtendedSelectionType;
                                           DogCommandEnum; DogType;
                                           SentientInterface; PetInterface;
                                           AlienType; HumanType;
                                           CatCommandEnum; CatType;
                                           CatOrDogUnion; DogOrHumanUnion; HumanOrAlienUnion;
                                           ArgumentsType
                                        ].

    Let extended_schwf : extended_schema.(is_a_wf_schema).
    Proof.
      (* For some reason just computing gets stuck - using by [] *)
      rewrite /is_a_wf_schema /= ?andbT //. 
    Qed.

    Let extended_wf_schema  := WFGraphQLSchema extended_schwf.

    Let example121_1 : seq (@Selection scalar_eqType) :=
      [::
         "multipleReqs" [[ [:: ("x", SValue (VInt 1)); ("y", SValue (VInt 2))] ]]
      ].

    Example e121_1 : selections_conform is_valid_scalar_value extended_wf_schema "Arguments" example121_1.
    Proof.
        by [].
    Qed.

    Let example121_2 : seq (@Selection scalar_eqType) :=
      [::
         "multipleReqs" [[ [:: ("y", SValue (VInt 1)); ("x", SValue (VInt 2))] ]]
      ].

    Example e121_2 : selections_conform is_valid_scalar_value extended_wf_schema "Arguments" example121_2.
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
    Let example128 : seq (@Selection scalar_eqType) :=
      [::
         on "Dog" {
           [::
              "name" [[ [::] ]]
           ]
         }
      ].

    Example e128 : selections_conform is_valid_scalar_value wf_schema "Dog" example128 &&
                   selections_conform is_valid_scalar_value wf_schema "Pet" example128.                
    Proof.
        by [].
    Qed.


    Let example129 : seq (@Selection scalar_eqType) :=
      [::
         on "NotInSchema" {
           [::
              "name" [[ [::] ]]
           ]
         }
      ].

    Example e129 : ~~selections_conform is_valid_scalar_value wf_schema "Dog" example129.
    Proof.
        by [].
    Qed.

    Example e129' : all (fun name => ~~selections_conform is_valid_scalar_value wf_schema name example129) wf_schema.(schema_names).
    Proof.
        by [].
    Qed.

    Let example130_1 : @Selection scalar_eqType := on "Dog" {
                                                   [::
                                                      "name" [[ [::] ]]
                                                   ]
                                                 }.
    Example e130_1 : is_consistent is_valid_scalar_value wf_schema "Dog" example130_1 &&
                     is_consistent is_valid_scalar_value wf_schema "Pet" example130_1.
    Proof.
        by [].
    Qed.

    Let example130_2 : @Selection scalar_eqType := on "Pet" {
                                                   [::
                                                      "name" [[ [::] ]]
                                                   ]
                                                 }.
    Example e130_2 : is_consistent is_valid_scalar_value wf_schema "Dog" example130_2 &&
                     is_consistent is_valid_scalar_value wf_schema "Pet" example130_2.
    Proof.
        by [].
    Qed.

     Let example130_3 : @Selection scalar_eqType := on "CatOrDog" {
                                                    [::
                                                       on "Dog" {
                                                         [::
                                                            "name" [[ [::] ]]
                                                         ]
                                                       }
                                                    ]
                                                 }.
    Example e130_3 : is_consistent is_valid_scalar_value wf_schema "CatOrDog" example130_3.
    Proof.
        by [].
    Qed.

    Let example131_1 : (@Selection scalar_eqType) := on "Int" {
                                                     [::
                                                        "something" [[ [::] ]]
                                                     ]
                                                   }.

    Example e131_1 : all (fun name => ~~is_consistent is_valid_scalar_value wf_schema name example131_1) wf_schema.(schema_names).
    Proof.
        by [].
    Qed.

    Let example131_2 : (@Selection scalar_eqType) := on "Dog" {
                                                     [::
                                                        on "Boolean" {
                                                          [::
                                                             "somethingElse" [[ [::] ]]
                                                          ]
                                                        }
                                                     ]
                                                   }.

    Example e131_2 : all (fun name => ~~is_consistent is_valid_scalar_value wf_schema name example131_2) wf_schema.(schema_names).
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
       https://graphql.github.io/graphql-spec/June2018/#sec-object-Spreads-In-object-Scope
     *)
    Let example137 : @Selection scalar_eqType := on "Dog" {
                                                 [::
                                                    "barkVolume" [[ [::] ]]
                                                 ]
                                               }.
    Example e137' : is_fragment_spread_possible wf_schema "Dog" "Dog".
    Proof.
        by [].
    Qed.
    
    Example e137 : is_consistent is_valid_scalar_value wf_schema "Dog" example137.
    Proof.
        by [].
    Qed.

    Let example138 : @Selection scalar_eqType := on "Cat" {
                                                 [::
                                                    "meowVolume" [[ [::] ]]
                                                 ]
                                               }.
     
    Example e138' : ~~ is_fragment_spread_possible wf_schema "Cat" "Dog".
    Proof.
        by [].
    Qed.

    Example e138 : ~~ is_consistent is_valid_scalar_value wf_schema "Dog" example138.
    Proof.
        by [].
    Qed.

    
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Abstract-Spreads-in-object-Scope
     *)
    Let example139 : @Selection scalar_eqType := on "Pet" {
                                                 [::
                                                    "name" [[ [::] ]]
                                                 ]
                                                }.

    
    Example e139' : is_fragment_spread_possible wf_schema "Pet" "Dog".
    Proof.
        by [].
    Qed.
    
    Example e139 : is_consistent is_valid_scalar_value wf_schema "Dog" example139.
    Proof.
        by [].
    Qed.

    Let example140 : @Selection scalar_eqType := on "CatOrDog" {
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
    
    Example e140 : is_consistent is_valid_scalar_value wf_schema "Dog" example140.
    Proof.
        by [].
    Qed.


    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-object-Spreads-In-Abstract-Scope
     *)
    Let example141_1 : seq (@Selection scalar_eqType) :=
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

    
    Example e141_1 : selections_conform is_valid_scalar_value wf_schema "Pet" example141_1.
    Proof.
        by [].
    Qed.

    Let example141_2 : seq (@Selection scalar_eqType) :=
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
    
    Example e141_2 : selections_conform is_valid_scalar_value wf_schema "CatOrDog" example141_2.
    Proof.
        by [].
    Qed.
    
    
    Let example142_1 : @Selection scalar_eqType := on "Dog" {
                                                 [::
                                                    "barkVolume" [[ [::] ]]
                                                 ]
                                                 }.

    Example e142_1' : ~~ is_fragment_spread_possible wf_schema "Dog" "Sentient".
    Proof.
        by [].
    Qed.

    Example e142_1 : ~~ is_consistent is_valid_scalar_value wf_schema "Sentient" example142_1.
    Proof.
        by [].
    Qed.

    
    Let example142_2 : @Selection scalar_eqType := on "Cat" {
                                                 [::
                                                    "meowVolume" [[ [::] ]]
                                                 ]
                                                 }.

    Example e142_2' : ~~ is_fragment_spread_possible wf_schema "Cat" "HumanOrAlien".
    Proof.
        by [].
    Qed.
    
    Example e142_2 : ~~ is_consistent is_valid_scalar_value wf_schema "HumanOrAlien" example142_2.
    Proof.
        by [].
    Qed.


    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Abstract-Spreads-in-Abstract-Scope
     *)
    Let example143 : seq (@Selection scalar_eqType) :=
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

    Example e143 : selections_conform is_valid_scalar_value wf_schema "Pet" example143.
    Proof.
        by [].
    Qed.

    Let example144 : @Selection scalar_eqType := on "Sentient" {
                                                 [::
                                                    "name" [[ [::] ]]
                                                 ]
                                               }.

    Example e144' : ~~ is_fragment_spread_possible wf_schema "Sentient" "Pet".
    Proof.
        by [].
    Qed.

    Example e144 : ~~ is_consistent is_valid_scalar_value wf_schema "Pet" example144.
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