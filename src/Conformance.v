From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Schema.
Require Import SchemaAux.
Require Import Graph.

Section Conformance.


  Variables (N Vals Name : finType).

  Variable vals_to_name : Vals -> Name.

  Definition vals_to_scalar (doc : Schema) :=
    forall (v : Vals),
      isScalarType doc (NamedType (vals_to_name v)) || isEnumType doc (NamedType (vals_to_name v)).


 (* Definition root_type_conforms (r : root) (doc : Schema) := tau (r) = root(doc). *)

  Definition fieldTypeConforms (doc : Schema) (fieldType targetType : Name) : bool :=
    (fieldType == targetType) ||
    (declaresImplementation doc targetType fieldType) ||
    (targetType \in (union doc fieldType))  .

    
  Definition edgeConforms (g : graph N Name Name Vals) (t : tau) (doc : Schema) :=
    forall (u v : N) (f : fld) (fieldType : type),
      g u f v ->
      lookupFieldType (label f) (t u) doc = Some fieldType ->
      (fieldTypeConforms doc fieldType (t v)) /\
      (~~isListType fieldType ->
      forall w, g u f w -> w == v)
  .
  
  Record conformed_graph (doc : Schema) := ConformedGraph {
                                                edges : graph N Name Name Vals;
                                                t : tau;
                                                wf_values : vals_to_scalar doc;
                                                wf_edges : edgeConforms edges t doc
                                              }.
  
  

End Conformance.