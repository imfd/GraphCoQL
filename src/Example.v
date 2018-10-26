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

  
  Local Open Scope string_scope.


  Delimit Scope schema_scope with schema.
  Open Scope schema_scope.

  Notation "'type' O 'implements' I {{ F }}" := (ObjectTypeDefinition O I F) (at level 0, no associativity) : schema_scope.

  Notation "'interface' I {{ F }}" := (InterfaceTypeDefinition I F) (at level 0, no associativity) : schema_scope.

  Notation "'enum' E { EV }" := (EnumTypeDefinition E EV) (at level 0, E at next level,  EV at level 0) : schema_scope.

  Notation "'union' U 'of' Uv" := (UnionTypeDefinition U Uv) (at level 0, no associativity) : schema_scope.

  Notation "'scalar' S" := (ScalarTypeDefinition S) (at level 60).
  
  Notation "f : t" := (Schema.Field f [::] t).


  Let IDType := scalar "ID".
  Let StringType := scalar "String".
  Let FloatType := scalar "Float".

  Let StarshipType := (ObjectTypeDefinition "Starship" [::]
                                           [:: ("id" : (NamedType "ID"));
                                              ("name" : (NamedType "String"));
                                              ("length" : (NamedType "Float"))
                     ]).

  Let CharacterType := interface "Character" {{ [::
                                                 ("id" : (NamedType "ID"));
                                                 ("name" : (NamedType "String"));
                                                 ("friends" : (ListType (NamedType "Character")))]
                                            }}.

  
  Let DroidType := type "Droid" implements [:: (NamedType "Character")] {{[::
                                                                            ("id" : (NamedType "ID"));
                                                                            ("name" : (NamedType "String"));
                                                                            ("friends" : (ListType (NamedType "Character")));
                                                                            ("primaryFunction" : (NamedType "String"))
                                                                               
                                                                       ]}}.
  
  
  Let HumanType := type "Human" implements [:: (NamedType "Character")] {{[::
                                                                            ("id" : (NamedType "ID"));
                                                                            ("name" : (NamedType "String"));
                                                                            ("friends" : (ListType (NamedType "Character")));
                                                                            ("starships" : (ListType (NamedType "Starship")))
                                                                               
                                                                       ]}}.

  Let EpisodeType := enum "Episode" { [:: "NEWHOPE" ; "EMPIRE" ; "JEDI" ] }.


  Let SearchResultType := union "SearchResult" of [:: (NamedType "Human") ; (NamedType "Droid") ; (NamedType "Starship")].


  Let QueryType := type "Query" implements [::] {{ [::
                                                     (Schema.Field "hero" [:: (FieldArgument "episode" (NamedType "Episode"))] (NamedType "Character"));
                                                     (Schema.Field "search" [:: (FieldArgument "text" (NamedType "String"))] (ListType (NamedType "SearchResult")))]
                                               }}.

  Let schema  := {| query := (NamedType "Query") ; typeDefinitions :=  [:: IDType; StringType; FloatType;  StarshipType;  CharacterType; DroidType; HumanType; EpisodeType; SearchResultType; QueryType] |}.


  
  Eval compute in  match schema with
                   | Schema query tdefs => match query with
                                          | (NamedType root) =>
                                            (root \in (typeDefsNames tdefs))
                                              && uniq (typeDefsNames tdefs)
                                              && all (isWFTypeDef schema) tdefs
                                                                             
                           | _ => false
                           end
                   end.
    
    - by [].
    - by [].
    - apply Forall_forall.
      move => tdef H. simpl in H;   destruct H.
    - rewrite <- H;  apply WF_Scalar. reflexivity.
    - destruct H. rewrite <- H; apply WF_Scalar. reflexivity.
    - destruct H. rewrite <- H; apply WF_Scalar; reflexivity.
    - destruct H. rewrite <- H. apply WF_ObjectWithInterfaces.
      by []. by []. by []. apply Forall_forall. move => fdef. auto. by [].
  
 
  
  

End Example.