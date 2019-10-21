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

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Spec's Validation Examples</h1>
        <p class="lead">
         This file contains the examples used in the Validation section of the spec (cf. <a href='https://graphql.github.io/graphql-spec/June2018/##sec-Validation'><span>&#167;</span>5</a>).
         </p>
         <p>
         The examples included are only of the currently supported features.
         </p>
  </div>
</div>#
 *)


Open Scope string_scope.
 

Section Values.

  Inductive Scalar : Type :=
  | VInt : nat -> Scalar
  | VBool: bool -> Scalar            
  | VString : string -> Scalar
  | VFloat : nat -> nat -> Scalar.
 
  

  (** We need to prove that Value has a decidable equality procedure,
      we hide it to unclutter the docs.
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

   (** **** Coerce function
      ----
 
      This is the function used in the semantics to coerce 
      results into "proper" values.
      
      Since we use the same type of data everywhere, we
      actually don't need to coerce, hence coerce is the id function.
      One could imagine that a technology implementing GraphQL
      might have different types to represent their values.
   *)
  Definition coerce : Scalar -> Scalar := id.

  
  (** **** Is valid scalar value?
      ---- 

      The following predicate checks whether a value respects its
      expected type. 
   *)
  Variable (schema : graphQLSchema).
  
  Fixpoint check_scalar (ty : type) (v : Scalar) : bool :=
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


(** *** Examples from section Validation in the specification     
    ----

    Some of the implemented examples do not exatly match the spec's examples
    because they are defined using fragments (in the spec). We try to accomodate 
    them using either inline fragments or by validating the selections using, as 
    type in scope, the same type condition used in the spec's fragments.

    We believe this still preserves the core validation idea behind the examples.
   *)
Section GraphQLSpecExamples.
 

  
  Coercion namedType_of_string (s : string) := NamedType s.

  (** **** Schema
      ----
      First, we define the schema. 

      #<div class="row">
        <div class="col-md-5">
          <img src="../imgs/SpecExamples/schema1.png" class="img-fluid" alt="Schema definition">
        </div>
        <div class="col-md-5">
          <img src="../imgs/SpecExamples/schema2.png" class="img-fluid" alt="Schema definition">
        </div>
      
      </div>#

   *)
  (**
     We start by defining the scalar types used in this system (implicit in the above schema).
   *)
  Let StringScalar := scalar "String".
  Let BooleanScalar := scalar "Boolean".
  Let IntScalar := scalar "Int".
  Let FloatScalar := scalar "Float".

  
  (** Then we proceed to define the types as described above, starting from the left side *)
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


  (** Next, the right side *)
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
  

   (**
     We then define the schema as the root operation type and its type definitions.
   *)
  Let schema := GraphQLSchema "Query" [:: StringScalar; BooleanScalar; IntScalar; FloatScalar;
                                 QueryType;
                                 DogCommandEnum; DogType;
                                   SentientInterface; PetInterface;
                                     AlienType; HumanType;
                                       CatCommandEnum; CatType;
                                         CatOrDogUnion; DogOrHumanUnion; HumanOrAlienUnion].

  (**
     Followed by a proof that the schema is well-formed, by simple computation.
   *)
  Let schwf : schema.(is_a_wf_schema).
  Proof. by []. Qed.


  (**
     Finally, we build the well-formed schema with the schema and the proof of its well-formedness.
   *)
  Let wf_schema : wfGraphQLSchema := WFGraphQLSchema schwf.



  (** **** Field Validation
      (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Validation.Fields'><span>&#167;</span>5.3</a>#)
      ---- 

      We begin with the examples proving showing valid and invalid field selections.
   *)
  Section FieldValidation.

    (**
       First, fields on object, interfaces and unions (cf. #<a href=' https://graphql.github.io/graphql-spec/June2018/##sec-Field-Selections-on-objects-Interfaces-and-Unions-Types'><span>&#167;</span>5.3.1</a>#)
     *)

    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-48706'>Counter example 102</a># 
        ---- *)
    Let example102 : @Selection scalar_eqType :=  "meowVolume" [[ [::] ]].
    
    Let example102' :  (@Selection scalar_eqType) :=  "barkVolume" : "kawVolume" [[ [::] ]].

    (** We compute it to show that both selections are invalid *)
    Example e102 : ~~ (is_consistent check_scalar wf_schema "Dog" example102 || is_consistent check_scalar wf_schema "Dog" example102').
    Proof. by []. Qed.


    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-d34e0'>Example 103</a># 
        ---- *)
    Let example103 : @Selection scalar_eqType := "name" [[ [::] ]].

    (** We show the selection is valid in the scope of the "Pet" type *)
    Example e103 : is_consistent check_scalar wf_schema "Pet" example103.
    Proof. by []. Qed.

    
    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-db33b'>Counter example 104</a># 
        ---- *)
    Let example104 : @Selection scalar_eqType := "nickname" [[ [::] ]].
    

    (** We show the selection is invalid in the scope of the "Pet" type *)
    Example e104 : ~~ is_consistent check_scalar wf_schema "Pet" example104.
    Proof. by []. Qed.

    (** And also for any subtype of the "Pet" type (This one is not in the spec). *)
    Example e104' : all (fun implementor => is_consistent check_scalar wf_schema implementor example104) (get_possible_types wf_schema "Pet").
    Proof.
        by [].
    Qed.
    

    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-245fa'>Example 105</a># 
        ---- *)
    Let example105 : seq (@Selection scalar_eqType) :=
      [::
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
      ].
    
    (** We show the selection is invalid in the scope of the "CatOrDog" type *)
    Example e105 : selections_conform check_scalar wf_schema "CatOrDog" example105.
    Proof. by []. Qed.


    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-252ad'>Counter example 106</a>#
        ----
     *)
    Let example106 : seq (@Selection scalar_eqType) := [::
                                                     "name" [[ [::] ]];
                                                     "barkVolume" [[ [::] ]]
                                                      ].
    
    (** We show the selection is invalid in the scope of the "Pet" type *)
    Example e106 : ~~ selections_conform check_scalar wf_schema "CatOrDog" example106.
    Proof. by []. Qed.

    

    (** We now move onto field merging validation (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Selection-Merging'><span>&#167;</span>5.3.2</a>#)
        ----
     *)
    Section FieldSelectionMerging.

      (** 
          Redefining only to ease reading -- Another option would be to use [selections_conform check_scalar] but this seems simpler.
          
          This checks that selections are [renaming_consistent] but first wrapping them in 
          their type in scope.
       *)
      Definition are_renaming_consistent (s : wfGraphQLSchema)
                 (ts : Name) (σs : seq (@Selection scalar_eqType)) := are_renaming_consistent s [seq (pair ts σ) | σ <- σs]. 


      (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-4e10c'>Example 107</a>#
        ----
     *)
      Let example107_1 : seq (@Selection scalar_eqType) := [::
                                                         "name" [[ [::] ]];
                                                         "name" [[ [::] ]]
                                                          ].
      
      Let example107_2 : seq (@Selection scalar_eqType) := [::
                                                             "otherName" : "name" [[ [::] ]];
                                                             "otherName" : "name" [[ [::] ]]
                                                          ].

      (** We show the selection is renaming-consistent in the scope of the "Dog" type *)
      Example e107_1 : are_renaming_consistent wf_schema "Dog" example107_1.
      Proof.
          by [].
      Qed.

      (** We show the selection is renaming-consistent in the scope of the "Dog" type *)
      Example e107_2 : are_renaming_consistent wf_schema "Dog" example107_2.
      Proof.
          by [].
      Qed.


      (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-a2230'>Counter example 108</a>#
        ----
     *)
      Let example108 : seq (@Selection scalar_eqType) := [::
                                                           "name" : "nickname" [[ [::] ]];
                                                           "name" [[ [::] ]]
                                                        ].
      
      (** We show the selection is not renaming-consistent in the scope of the "Dog" type *)
      Example e108 : ~~ are_renaming_consistent wf_schema "Dog" example108.
      Proof.
          by [].
      Qed.


      (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-b6369'>Example 109</a>#
        ----
     *)
      Let example109 := [::
                          "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT")) ] ]];
                          "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT"))] ]]
                       ].

      (** We show the selection is valid in the scope of the "Dog" type *)
      Example e109 : are_renaming_consistent wf_schema "Dog" example109.
      Proof.
          by [].
      Qed.

      
     
      (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-00fbf'>Counter example 110</a>#
        ----
     *)
      Let example110_1 := [::
                            "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT"))] ]];
                            "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "HEEL"))] ]]
                         ].
      
      Let example110_2 := [::
                            "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT"))] ]];
                            "doesKnowCommand" [[ [::] ]]
                         ].

      (** We show the selection is not renaming-consistent in the scope of the "Dog" type *)
      Example e110_1 : ~~ are_renaming_consistent wf_schema "Dog" example110_1.
      Proof.
          by [].
      Qed.
      
      (** We show the selection is not renaming-consistent in the scope of the "Dog" type *)
      Example e110_2 : ~~ are_renaming_consistent wf_schema "Dog" example110_2.
      Proof.
          by [].
      Qed.


      (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-a8406'>Example 111</a>#
        ----
     *)
      Let example111_1 : seq (@Selection scalar_eqType) :=
        [::
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
      
      (** We show the selection is renaming-consistent in the scope of the "Pet" type *)
      Example e111_1 : are_renaming_consistent wf_schema "Pet" example111_1.
      Proof.
          by [].
      Qed.


      
      Let example111_2 : seq (@Selection scalar_eqType) :=
        [::
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
      
      (** We show the selection is renaming-consistent in the scope of the "Pet" type *)
      Example e111_2 : are_renaming_consistent wf_schema "Pet" example111_2.
      Proof.
          by [].
      Qed.
      

      (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-54e3d'>Counter example 112</a>#
        ----
     *)
      Let example112 : seq (@Selection scalar_eqType) :=
        [::
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
      
      (** We show the selections are not type-compatible in the scope of the "Pet" type *)
      Example e112 : ~~ are_type_compatible wf_schema [seq pair "Pet" q | q <- example112].
      Proof.
          by [].
      Qed.
      
      (** We show the selections are not type-compatible in the scope of the "Pet" type *)
      Example e112' : ~~ selections_conform check_scalar wf_schema "Pet" example112.
      Proof.
          by [].
      Qed.
      
      
    End FieldSelectionMerging.


    (**
       In this section we define examples from the leaf field selections 
       (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Leaf-Field-Selections'><span>&#167;</span>5.3.3</a>#)
     *)
    Section LeafFieldSelections.


      (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-e23c5'>Example 113</a>#
        ----
     *)
      Let example113 : @Selection scalar_eqType := "barkVolume" [[ [::] ]].
      

      (** We show the selection is valid in the scope of the "Pet" type *)
      Example e113 : is_consistent check_scalar wf_schema "Dog" example113.
      Proof.
          by [].
      Qed.

      (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-13b69'>Counter example 114</a>#
        ----
     *)
      Let example114 : (@Selection scalar_eqType) :=
        "barkVolume" [[ [::] ]] {
                       [::
                          "sinceWhen" [[ [::] ]]
                       ]
                     }.
       

      (** We show the selection is invalid in the scope of the "Pet" type *)
      Example e114 : ~~ is_consistent check_scalar wf_schema "Dog" example114.
      Proof.
          by [].
      Qed.


      (**
         Example 115 is a schema extension, which is not currently implemented, and Example 116 uses it. However, we can manage around it, by redefining the Query type and schema.
       *)
      Let ExtendedQuery := object "ExtendedQuery" implements [::] {
                                       [::
                                          (Field "dog" [::] "Dog");
                                          (Field "human" [::] "Human");
                                          (Field "pet" [::] "Pet");
                                          (Field "catOrDog" [::] "CatOrDog")
                                       ]
                                 }.

      
     
      (** We "extend" the schema, and indicate that the Query type is now called 
          _ExtendedQuery_.
       *)
      Let extended_schema := GraphQLSchema "ExtendedQuery"
                                          [:: StringScalar; BooleanScalar; IntScalar; FloatScalar;
                                             ExtendedQuery;
                                             DogCommandEnum; DogType;
                                             SentientInterface; PetInterface;
                                             AlienType; HumanType;
                                             CatCommandEnum; CatType;
                                             CatOrDogUnion; DogOrHumanUnion; HumanOrAlienUnion].


      (** We prove it is still a valid schema *)
      Let extended_schwf : extended_schema.(is_a_wf_schema).
      Proof.  by [].
      Qed.


      
      (** And redefine the well-formed schema *)
      Let extended_wf_schema : wfGraphQLSchema := WFGraphQLSchema extended_schwf.


      (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-d68ee'>Counter example 116</a>#
        ----
     *)
      Let example116_1 : @Selection scalar_eqType := "human" [[ [::] ]].


      (** We show the selection is invalid in the scope of the root query type *)
      Example e116_1 : ~~is_consistent check_scalar extended_wf_schema "ExtendedQuery" example116_1.
      Proof.
          by [].
      Qed.

      Let example116_2 : @Selection scalar_eqType := "pet" [[ [::] ]].
      

      (** We show the selection is invalid in the scope of the root query type *)
      Example e116_2 : ~~is_consistent check_scalar extended_wf_schema "ExtendedQuery" example116_2.
      Proof.
          by [].
      Qed.

      Let example116_3 : @Selection scalar_eqType := "catOrDog" [[ [::] ]].

      
      (** We show the selection is invalid in the scope of the root query type *)
      Example e116_3 : ~~is_consistent check_scalar extended_wf_schema "ExtendedQuery" example116_3.
      Proof.
          by [].
      Qed.
      
    End LeafFieldSelections.


    (** This concludes the field validation section *)

  End FieldValidation.



  (** **** Arguments Validation
      (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/#sec-Validation.Arguments'><span>&#167;</span>5.4</a>#)
      ---- 

      In this section we include the examples validating arguments.
   *)
  Section ValidArguments.

    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-760cb'>Example 117</a>#
        ----
     *)
    Let example117_1 : @Selection scalar_eqType := "doesKnowCommand" [[ [:: ("dogCommand", SValue (VString "SIT"))] ]].


    (** We show the selection is valid in the scope of the "Dog" type *)
    Example e117_1 : is_consistent check_scalar wf_schema "Dog" example117_1.
    Proof.
        by [].
    Qed.

    (* Not including the directive @include since directives are not implemented.*)
    Let example117_2 : @Selection scalar_eqType := "isHousetrained" [[ [:: ("atOtherHomes", SValue (VBool true))] ]].
    

    (** We show the selection is valid in the scope of the "Dog" type *)
    Example e117_2 : is_consistent check_scalar wf_schema "Dog" example117_2.
    Proof.
      by [].
    Qed.

    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-d5639'>Counter example 118</a>#
        ----
     *)
    Let example_118 : @Selection scalar_eqType := "doesKnowCommand" [[ [:: ("command", SValue (VString "CLEAN_UP_HOUSE")) ] ]].

    
    (** We show the selection is invalid in the scope of the "Dog" type *)
    Example e118 : ~~is_consistent check_scalar wf_schema "Dog" example_118.
    Proof.
        by [].
    Qed.


    (** Example 120 corresponds to a type extension to the query type. 
        Since we don't implement type extension, we work around it *)
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

    (** We redefine the Query type *)
    Let ExtendedQueryType := object "ExtendedQuery" implements [::] {
                                     [::
                                        (Field "dog" [::] "Dog");
                                        (Field "arguments" [::] "Arguments")

                                     ]
                                   }.

    (** Redefine the schema *)
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

    (** And prove it correct *)
    Let extended_schwf : extended_schema.(is_a_wf_schema).
    Proof.
      (* For some reason just computing gets stuck - using by [] *)
      rewrite /is_a_wf_schema /= ?andbT //. 
      (* Actually, only using [rewrite /is_a_wf_schema //=.] concludes, but 
       then using [Qed.] gets stuck D: *)
    Qed.

    (** Finally, redefine the well-formed schema *)
    Let extended_wf_schema  := WFGraphQLSchema extended_schwf.


    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-18fab'>Example 121</a>#
        ----
     *)
    Let example121_1 : @Selection scalar_eqType := "multipleReqs" [[ [:: ("x", SValue (VInt 1)); ("y", SValue (VInt 2))] ]].

    (** We show the selection is valid in the scope of the "Arguments" type *)
    Example e121_1 : is_consistent check_scalar extended_wf_schema "Arguments" example121_1.
    Proof.
        by [].
    Qed.

    
    Let example121_2 : @Selection scalar_eqType := "multipleReqs" [[ [:: ("y", SValue (VInt 1)); ("x", SValue (VInt 2))] ]].

    
    (** We show the selection is valid in the scope of the "Arguments" type *)
    Example e121_2 : is_consistent check_scalar extended_wf_schema "Arguments" example121_2.
    Proof.
        by [].
    Qed.

    
    (**
       Examples 122 - 125 are meant for required arguments, which is not currently supported.
     *)
    
    (** This concludes validation over arguments *)
  End ValidArguments.




  
  (** **** Fragments Validation
      (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Validation.Fragments'><span>&#167;</span>5.5</a>#)
      ---- 

      In this section we include the examples validating fragments.
   *)
  Section Fragments.

    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-1b2da'>Example 128</a>#
        ----

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

    (** We show the selection is valid in the scope of the "Dog" and "Pet" types *)
    Example e128 : selections_conform check_scalar wf_schema "Dog" example128 &&
                   selections_conform check_scalar wf_schema "Pet" example128.                
    Proof.
        by [].
    Qed.


    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-463f6'>Counter example 129</a>#
        ----
     *)
    Let example129 : seq (@Selection scalar_eqType) :=
      [::
         on "NotInSchema" {
           [::
              "name" [[ [::] ]]
           ]
         }
      ].

    (** We show the selection is invalid in the scope of the "Dog" type *)
    Example e129 : ~~selections_conform check_scalar wf_schema "Dog" example129.
    Proof.
        by [].
    Qed.

    (** We show the selection is invalid in the scope of any type in the schema *)
    Example e129' : all (fun name => ~~selections_conform check_scalar wf_schema name example129) wf_schema.(type_names).
    Proof.
        by [].
    Qed.


    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-3c8d4'>Example 130</a>#
        ----
     *)
    Let example130_1 : @Selection scalar_eqType := on "Dog" {
                                                   [::
                                                      "name" [[ [::] ]]
                                                   ]
                                                     }.

    (** We show the selection is valid in the scope of the "Dog" and "Pet" types *)
    Example e130_1 : is_consistent check_scalar wf_schema "Dog" example130_1 &&
                     is_consistent check_scalar wf_schema "Pet" example130_1.
    Proof.
        by [].
    Qed.

    Let example130_2 : @Selection scalar_eqType := on "Pet" {
                                                   [::
                                                      "name" [[ [::] ]]
                                                   ]
                                                     }.

    (** We show the selection is valid in the scope of the "Dog" and "Pet" types *)
    Example e130_2 : is_consistent check_scalar wf_schema "Dog" example130_2 &&
                     is_consistent check_scalar wf_schema "Pet" example130_2.
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

    (** We show the selection is valid in the scope of the "Dog" and "Pet" types *)
    Example e130_3 : is_consistent check_scalar wf_schema "CatOrDog" example130_3.
    Proof.
        by [].
    Qed.


    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-4d5e5'>Counter example 131</a>#
        ----
     *)
    Let example131_1 : (@Selection scalar_eqType) := on "Int" {
                                                     [::
                                                        "something" [[ [::] ]]
                                                     ]
                                                   }.

    (** We show the selection is invalid in the scope of any type in the shema *)
    Example e131_1 : all (fun name => ~~is_consistent check_scalar wf_schema name example131_1) wf_schema.(type_names).
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

    (** We show the selection is invalid in the scope of any type in the shema *)
    Example e131_2 : all (fun name => ~~is_consistent check_scalar wf_schema name example131_2) wf_schema.(type_names).
    Proof.
        by [].
    Qed.


    (**
       Example 132-136 refer to fragment definitions. We don't implement 
       that so we omit those examples.
     *)



    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-0fc38'>Example 137</a>#
        ----
     *)
    Let example137 : @Selection scalar_eqType := on "Dog" {
                                                 [::
                                                    "barkVolume" [[ [::] ]]
                                                 ]
                                                   }.

    (** We show the fragment spreads in the scope of the "Dog" type *)
    Example e137' : is_fragment_spread_possible wf_schema "Dog" "Dog".
    Proof.
        by [].
    Qed.

    (** We show the selection is valid in the scope of the "Dog" type *)
    Example e137 : is_consistent check_scalar wf_schema "Dog" example137.
    Proof.
        by [].
    Qed.
    
    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-4d411'>Counter example 138</a>#
        ----
     *)
    Let example138 : @Selection scalar_eqType := on "Cat" {
                                                 [::
                                                    "meowVolume" [[ [::] ]]
                                                 ]
                                               }.

    (** We show the fragment does not spread in the scope of the "Dog" type *)
    Example e138' : ~~ is_fragment_spread_possible wf_schema "Cat" "Dog".
    Proof.
        by [].
    Qed.

    (** We show the selection is invalid in the scope of the "Dog" type *)
    Example e138 : ~~ is_consistent check_scalar wf_schema "Dog" example138.
    Proof.
        by [].
    Qed.

    
    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-2c8d0'>Example 139</a>#
        ----
     *)
    Let example139 : @Selection scalar_eqType := on "Pet" {
                                                 [::
                                                    "name" [[ [::] ]]
                                                 ]
                                                }.

    (** We show the fragment spreads in the scope of the "Dog" type *)
    Example e139' : is_fragment_spread_possible wf_schema "Pet" "Dog".
    Proof.
        by [].
    Qed.

    (** We show the selection is valid in the scope of the "Dog" type *)
    Example e139 : is_consistent check_scalar wf_schema "Dog" example139.
    Proof.
        by [].
    Qed.


    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-41843'>Example 140</a>#
        ----
     *)
    Let example140 : @Selection scalar_eqType := on "CatOrDog" {
                                                 [::
                                                    on "Cat" {
                                                      [::
                                                         "meowVolume" [[ [::] ]]
                                                      ]
                                                    }
                                                 ]
                                               }.

    (** We show the fragment spreads in the scope of the "Dog" type *)
    Example e140' : is_fragment_spread_possible wf_schema "CatOrDog" "Dog".
    Proof.
        by [].
    Qed.

    (** We show the selection is valid in the scope of the "Dog" type *)
    Example e140 : is_consistent check_scalar wf_schema "Dog" example140.
    Proof.
        by [].
    Qed.


    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-85110'>Example 141</a>#
        ----
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


    (** We show the fragment spreads in the scope of the "Pet" type *)
    Example e141_1' : is_fragment_spread_possible wf_schema "Dog" "Pet".
    Proof.
        by [].
    Qed.

    (** We show the selection is valid in the scope of the "Pet" type *)
    Example e141_1 : selections_conform check_scalar wf_schema "Pet" example141_1.
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

    (** We show the fragment spreads in the scope of the "CatOrDog" type *)
    Example e141_2' : is_fragment_spread_possible wf_schema "Cat" "CatOrDog".
    Proof.
        by [].
    Qed.

    (** We show the selection is valid in the scope of the "CatOrDog" type *)
    Example e141_2 : selections_conform check_scalar wf_schema "CatOrDog" example141_2.
    Proof.
        by [].
    Qed.
    

    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-a8dcc'>Counter example 142</a>#
        ----
     *)
    Let example142_1 : @Selection scalar_eqType := on "Dog" {
                                                 [::
                                                    "barkVolume" [[ [::] ]]
                                                 ]
                                                 }.

    (** We show the fragment does not spread in the scope of the "Sentient" type *)
    Example e142_1' : ~~ is_fragment_spread_possible wf_schema "Dog" "Sentient".
    Proof.
        by [].
    Qed.

    (** We show the selection is invalid in the scope of the "Sentient" type *)
    Example e142_1 : ~~ is_consistent check_scalar wf_schema "Sentient" example142_1.
    Proof.
        by [].
    Qed.

    
    Let example142_2 : @Selection scalar_eqType := on "Cat" {
                                                 [::
                                                    "meowVolume" [[ [::] ]]
                                                 ]
                                                 }.
    (** We show the fragment does not spread in the scope of the "HumanOrAlien" type *)
    Example e142_2' : ~~ is_fragment_spread_possible wf_schema "Cat" "HumanOrAlien".
    Proof.
        by [].
    Qed.
    
    (** We show the selection is invalid in the scope of the "HumanOrAlien" type *)
    Example e142_2 : ~~ is_consistent check_scalar wf_schema "HumanOrAlien" example142_2.
    Proof.
        by [].
    Qed.



    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-dc875'>Example 143</a>#
        ----
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

    (** We show the type "DogOrHuman" spreads in the scope of the "Pet" type *)
    Example e143' : is_fragment_spread_possible wf_schema "DogOrHuman" "Pet".
    Proof.
        by [].
    Qed.

    (** We show the selection is valid in the scope of the "Pet" type *)
    Example e143 : selections_conform check_scalar wf_schema "Pet" example143.
    Proof.
        by [].
    Qed.


    (** #<a href='https://graphql.github.io/graphql-spec/June2018/##example-c9c63'>Counter example 144</a>#
        ----
     *)
    Let example144 : @Selection scalar_eqType := on "Sentient" {
                                                 [::
                                                    "name" [[ [::] ]]
                                                 ]
                                               }.

    (** We show the type "Sentient" does not spread in the scope of the "Pet" type *)
    Example e144' : ~~ is_fragment_spread_possible wf_schema "Sentient" "Pet".
    Proof.
        by [].
    Qed.

    (** We show the selection is invalid in the scope of the "Pet" type *)
    Example e144 : ~~ is_consistent check_scalar wf_schema "Pet" example144.
    Proof.
        by [].
    Qed.
    
    
    (** This concludes the validation over fragments *)
  End Fragments.    

  
    
End GraphQLSpecExamples.