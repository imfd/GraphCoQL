From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import List.
Import ListNotations.

Require Import Schema.
Require Import SchemaWellFormedness.
Require Import SchemaAux.
Require Import Graph.

Section Conformance.


  Variables (N Vals Name : finType).

  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type graph : @graphQLGraph N Name Name Name Vals. 
  
  Definition rootTypeConforms schema graph  := (t graph (r graph)) = root(schema).

  Definition fieldTypeConforms schema (fieldType targetType : Name) : bool :=
    (fieldType == targetType) ||
    (declaresImplementation schema targetType fieldType) ||
    (targetType \in (union schema fieldType)).

  (*
  Record edge_conforms (E : edges N Name Name Vals) (t : tau) schema := EdgeConforms {
                                                                           fInFields : forall u f v, E u f v -> In (label f) (fields schema (t u));
                                                                           
                           }.*)
  

  Definition argumentsConform schema (src : Name) (f : fld) :=
    forall arg value ty,
      (f arg) = Some value ->
      lookupArgument schema src arg f = Some (FieldArgument arg ty) ->
      (hasType schema) ty value.
    
    
  Definition edgeConforms schema (E : edges N Name Name Vals) (t : tau)   :=
    forall (u v : N) (f : fld) (fieldType : type),
      E u f v ->              
      lookupFieldType schema (t u) (label f) = Some fieldType ->    (* This covers the field \in fields (t(u)) *)
      (fieldTypeConforms schema (unwrapTypeName fieldType) (t v)) /\
      (~~isListType fieldType ->
       forall w, E u f w -> w == v) /\
      argumentsConform schema (t u) f.

  (*Definition rootConforms schema (t : tau) := t(r) == (root schema).*)

  Definition fieldConforms schema (t : tau) (l : lambda) :=
    forall (u : N) (f : fld) (ty : type) (value : Vals) (lvalue : list Vals),
      lookupFieldType schema (t u) f = Some ty ->
      (l (u,f) = Some (inl value)) \/ (l (u, f) = Some (inr lvalue)) ->
      (hasType schema) ty value \/ Forall (hasType schema ty) lvalue ->
      argumentsConform schema (t u) f.
  
  Record conformedGraph schema := ConformedGraph {
                                                graph;
                                                wf_root : rootTypeConforms schema graph;
                                                wf_edges : edgeConforms schema (E graph) (t graph);
                                                wf_fields : fieldConforms schema (t graph) (lam graph)
                                   }.
  
  

End Conformance.