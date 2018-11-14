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
Require Import GraphAux.
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

  Let CharacterType := interface "Character" {{[::
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

  Let schema  := {| query := "Query" ; typeDefinitions :=  [:: IDType; StringType; FloatType;  StarshipType;  CharacterType; DroidType; HumanType; EpisodeType; SearchResultType; QueryType] |}.


  Lemma sdf : schemaIsWF schema.
  Proof. by []. Qed.
  



  Let wf_schema : @wfSchema string_ordType string_ordType   := WFSchema (fun n v => true) sdf.



  Let edges : {fset node * fld * node} :=
    fset [:: (Graph.Node 0 "Query" emptym ,
              Graph.Field "search" [fmap ("text", "L")],
              Graph.Node 4 "Starship" [fmap (Graph.Field "id" emptym, (inl "3000"));
                                         (Graph.Field "name" emptym, (inl "Falcon")); 
                                         (Graph.Field "length" emptym, (inl "34.37"))]);
            (Graph.Node 0 "Query" emptym,
             Graph.Field "search" [fmap ("text", "L")],
             Graph.Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                     (Graph.Field "name" emptym, (inl "Luke"))]);
            (Graph.Node 0 "Query" emptym,
             Graph.Field "hero" [fmap ("episode", "EMPIRE")],
             Graph.Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                     (Graph.Field "name" emptym, (inl "Luke"))]);
            (Graph.Node 0 "Query" emptym,
             Graph.Field "hero" [fmap ("episode", "NEWHOPE")],
             Graph.Node 2 "Droid" [fmap  (Graph.Field "id" emptym, (inl "2001"));
                                     (Graph.Field "name" emptym, (inl "R2-D2"));
                                     (Graph.Field "primaryFunction" emptym, (inl "Astromech"))]);
            (Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                               (Graph.Field "name" emptym, (inl "Luke"))],
             Graph.Field "friends" emptym,
                       Graph.Node 2 "Droid" [fmap  (Graph.Field "id" emptym, (inl "2001"));
                                               (Graph.Field "name" emptym, (inl "R2-D2"));
                                               (Graph.Field "primaryFunction" emptym, (inl "Astromech"))]);
            (Node 2 "Droid" [fmap  (Graph.Field "id" emptym, (inl "2001"));
                               (Graph.Field "name" emptym, (inl "R2-D2"));
                               (Graph.Field "primaryFunction" emptym, (inl "Astromech"))],
             Graph.Field "friends" emptym,
             Graph.Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                     (Graph.Field "name" emptym, (inl "Luke"))]);
            (Graph.Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                     (Graph.Field "name" emptym, (inl "Luke"))],
             Graph.Field "friends" emptym,
             Graph.Node 3 "Human" [fmap (Graph.Field "id" emptym, (inl "1002"));
                                     (Graph.Field "name" emptym, (inl "Han"))]);
            (Graph.Node 3 "Human" [fmap (Graph.Field "id" emptym, (inl "1002"));
                                     (Graph.Field "name" emptym, (inl "Han"))],
             Graph.Field "friends" emptym,
             Graph.Node 1 "Human" [fmap (Graph.Field "id" emptym, (inl "1000"));
                                     (Graph.Field "name" emptym, (inl "Luke"))]);
            (Graph.Node 3 "Human" [fmap (Graph.Field "id" emptym, (inl "1002"));
                                     (Graph.Field "name" emptym, (inl "Han"))],
             Graph.Field "starships" emptym,
             Graph.Node 4 "Starship" [fmap (Graph.Field "id" emptym, (inl "3000"));
                                        (Graph.Field "name" emptym, (inl "Falcon")); 
                                        (Graph.Field "length" emptym, (inl "34.37"))])
            ].
  
  
  Let r : @node nat_ordType string_ordType string_ordType := Graph.Node 0 "Query" emptym.
  

  Let g := GraphQLGraph r edges.


  Lemma rtc : rootTypeConforms wf_schema g.
  Proof.    by [].  Qed.

 
  Lemma ec : edgesConform wf_schema edges.
  Proof.
    by rewrite /edgesConform /edges [fset]unlock.
  Qed.

  Lemma fc : fieldsConform wf_schema g.
  Proof.
    by rewrite /fieldsConform /graph_s_nodes /= /edges [fset]unlock /=. Qed.

  Lemma nhot : nodes_have_object_type wf_schema g.
  Proof.
    by rewrite /nodes_have_object_type /graph_s_nodes /= /edges [fset]unlock.
  Qed.
    

  Let wf_graph := ConformedGraph rtc ec fc nhot.

End Example.