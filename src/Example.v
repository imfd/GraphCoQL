From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.

From Coq Require Import String Ascii List.
From CoqUtils Require Import string.


Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Graph.
Require Import Conformance.





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

  Let schema : @Schema.schema string_ordType  := {| query := "Query" ; typeDefinitions :=  [:: IDType; StringType; FloatType;  StarshipType;  CharacterType; DroidType; HumanType; EpisodeType; SearchResultType; QueryType] |}.


  Lemma sdf : schemaIsWF schema.
  Proof. by []. Qed.
  



  Let wf_schema : @wfSchema string_ordType string_ordType   := WFSchema (fun n v => true) sdf.



  Let edges := fset [:: (0, Graph.Field "search" [fmap ("text", "L")], 4);
                      (0,  Graph.Field "search" [fmap ("text", "L")], 1);
                      (0,  Graph.Field "hero" [fmap ("episode", "EMPIRE")], 1);
                      (0,  Graph.Field "hero" [fmap ("episode", "NEWHOPE")], 2);
                      (1,  Graph.Field "friends" emptym, 2);
                      (2,  Graph.Field "friends" emptym, 1);
                      (1,  Graph.Field "friends" emptym, 3);
                      (3,  Graph.Field "friends" emptym, 1);
                      (3,  Graph.Field "starships" emptym, 4)
                   ].
  Let r := 0.

  Let tau :=  mkfmap [:: (0, "Query");
                       (1, "Human");
                       (2, "Droid");
                       (3, "Human");
                       (4, "Starship")].

  Let lambda : {fmap nat * (@fld string_ordType string_ordType string_ordType) -> string + seq.seq string} :=
    [fmap ((1, Graph.Field "id" emptym), (inl "1000"));
       ((1, Graph.Field "name" emptym), (inl "Luke"));
       ((2, Graph.Field "id" emptym), (inl "2001"));
       ((2, Graph.Field "name" emptym), (inl "R2-D2"));
       ((2, Graph.Field "primaryFunction" emptym), (inl "Astromech"));
       ((3, Graph.Field "id" emptym), (inl "1002"));
       ((3, Graph.Field "name" emptym), (inl "Han"));
       ((4, Graph.Field "id" emptym), (inl "3000"));
       ((4, Graph.Field "name" emptym), (inl "Falcon")); 
       ((4, Graph.Field "length" emptym), (inl "34.37"))].
  

  Let g := GraphQLGraph r edges tau lambda.


  Lemma rasf : rootTypeConforms wf_schema g.
  Proof.
      by move => t /=; case.
  Qed.


  Lemma ec : edgeConforms wf_schema edges tau.
  Proof.
    by [].
  Qed.

  Lemma fc : fieldConforms wf_schema tau lambda.
  Proof.
      by []. Qed.

  Lemma tc : tauConforms wf_schema tau.
  Proof. by []. Qed.
    

  Let wf_graph := ConformedGraph rasf ec fc tc. 

End Example.