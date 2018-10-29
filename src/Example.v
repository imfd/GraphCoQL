From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Coq Require Import String Ascii List.
From CoqUtils Require Import string.


Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Graph.
(* Require Import Conformance. *)





(** This file depicts the example used in [Hartig & Pérez, 2017];
    the Schema, graph, etc. 
 **)

Section Example.

  Variable Vals : finType.
  
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

  Let CharacterType := interface "Character" {{ [::
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

  Let schema : @Schema.schema string_eqType  := {| query := "Query" ; typeDefinitions :=  [:: IDType; StringType; FloatType;  StarshipType;  CharacterType; DroidType; HumanType; EpisodeType; SearchResultType; QueryType] |}.


  Lemma sdf : schemaIsWF schema.
  Proof. by []. Qed.
  
  Definition wf_schema : @wfSchema string_eqType Vals   := WFSchema (fun n v => true) sdf.

 
 
  
  

End Example.