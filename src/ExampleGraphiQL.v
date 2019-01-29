From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.

From Coq Require Import String Ascii.
From CoqUtils Require Import string.

From Equations Require Import Equations.



Require Import Graph.
Require Import GraphAux.
Require Import GraphConformance.
Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryConformance.
Require Import QuerySemantic.
Require Import NRGTNF.

Local Open Scope string_scope.
Open Scope schema_scope.


Notation "[ name ]" := (ListType (NT name)).
Notation "argname :- ty" := (FieldArgument argname ty) (at level 50) : schema_scope.
Notation "f : ty" := (Field f [::] ty) : schema_scope.
Notation "fname '(' args ')' ':' ty" := (Field fname args ty) (at level 50) : schema_scope.
Notation "'scalar' S" := (ScalarTypeDefinition S) (at level 0) : schema_scope.
Notation "'object' O '{{' flds '}}'" := (ObjectTypeDefinition O [::] flds) : schema_scope.
Notation "'object' O 'implements' I '{{' flds '}}'" := (ObjectTypeDefinition O I flds) (at level 0) : schema_scope.
Notation "'interface' I '{{' flds '}}'" := (InterfaceTypeDefinition I flds) : schema_scope.
Notation "'union' U '{' mbs '}'" := (UnionTypeDefinition U mbs) : schema_scope.
Notation "'enum' E '{' evs '}'" := (EnumTypeDefinition E evs) : schema_scope.

Coercion namedType_of_string (s : string) := NT s.


Let ID := scalar "ID".

Let Root := object "Root" {{
                             [::
                                ("allPeople" : "PeopleConnection")
                             ]
                         }}.
Let PeopleConnection := object "PeopleConnection" {{
                                                     [::
                                                        ("people" : ["Person"])
                                                     ]
                                                 }}.

Let Node := interface "Node" {{
                                [::
                                   ("id" : "ID")
                                ]
                            }}.

Let Person := object "Person" implements [:: "Node"] {{
                                                        [::
                                                           ("id" : "ID")
                                                        ]
                                                    }}.

Let Vehicle := object "Vehicle" implements [:: "Node"] {{
                                                        [::
                                                           ("id" : "ID")
                                                        ]
                                                      }}.

Let Sch := Schema "Root" [:: ID; Root; PeopleConnection; Node; Person; Vehicle].


Lemma wfq : is_schema_wf Sch. done. Qed.

Let wf_schema : @wfSchema string_ordType string_ordType := WFSchema (fun n v => true) wfq.


Notation " id : ty '*-' f '->' n" := (Graph.Node id ty emptym, Graph.Field f emptym, n) (at level 0, f at next level, n at next level).

 Let edges : {fset (@node nat_ordType string_ordType string_ordType)  * (@fld string_ordType string_ordType) * (@node nat_ordType string_ordType string_ordType)} :=
   fset [::
           (Graph.Node 0 "Root" emptym,
            Graph.Field "allPeople" emptym,
            Graph.Node 1 "PeopleConnection" emptym);
           
           (Graph.Node 1 "PeopleConnection" emptym,
            Graph.Field "people" emptym,
            Graph.Node 2 "Person" [fmap  (Graph.Field "id" emptym, (inl "2001"))]);

           (Graph.Node 1 "PeopleConnection" emptym,
            Graph.Field "people" emptym,
            Graph.Node 3 "Person" [fmap  (Graph.Field "id" emptym, (inl "2002"))])
        ].
 

    
 Let r : @node nat_ordType string_ordType string_ordType := Graph.Node 0 "Root" emptym.
    
    
 Let g := GraphQLGraph r edges.


 Lemma rtc : root_type_conforms wf_schema g. done. Qed.
    
 Lemma ec : edges_conform wf_schema edges.
 Proof.
     by rewrite /edges_conform /edges [fset]unlock.
 Qed.
 
 Lemma fc : fields_conform wf_schema g.
 Proof.
     by rewrite /fields_conform /nodes /= /edges [fset]unlock /=. Qed.
 
 Lemma nhot : nodes_have_object_type wf_schema g.
 Proof.
     by rewrite /nodes_have_object_type /nodes /= /edges [fset]unlock.
 Qed.
 

 Let wf_graph := ConformedGraph rtc ec fc nhot.


 Let q : list (@Query string_ordType string_ordType) :=
         [::
            (NestedField "allPeople" emptym
               [::
                  (NestedField "people" emptym
                     [::
                        (InlineFragment "Node" 
                           [::
                              (InlineFragment "Vehicle"
                                 [::              
                                    (SingleField "id" emptym)
                                 ]
                              )
                           ]
                        )
                     ]
                  )
               ]
            )
         ].

 Lemma queries_wf : queries_conform wf_schema Sch.(query_type) q. done. Qed.

 
 Lemma app_nil_r A (l : seq A) : (l ++ [::] = l)%list.
   elim: l => // x l' IH.
   by rewrite -{2}IH -cat_cons.
 Qed.
 
 Goal eval_queries wf_schema wf_graph r q =
 [::
    (NestedResult "allPeople"
       [::
          (NestedListResult "people"
             [::
                [::];            
                [::]
             ]
          )
       ]
    )
 ].
 Proof.
   simpl.
   rewrite /eval_queries.
   simpl.
   rewrite /get_target_nodes_with_field /=.
   rewrite /edges [fset]unlock /=.
   program_simpl.
   Qed.