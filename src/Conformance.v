From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Syntax.
Require Import Graph.

Section Conformance.


  Variables (N Vals Name : finType).

  Variable vals_to_name : Vals -> Name.

  Definition vals_to_scalar (doc : Document) :=
    forall (v : Vals),
      ScalarType doc (NamedType (vals_to_name v)) || EnumType doc (NamedType (vals_to_name v)).


 (* Definition root_type_conforms (r : root) (doc : Document) := tau (r) = root(doc). *)

  Definition field_has_target_type (fname sname tname : Name) (doc : Document) : bool :=
    match lookupField fname sname doc with
    | Some fieldDef => (unwrapTypeName (fieldType fieldDef)) == tname
    | None => false
    end.
  
  Definition edge_conforms (g : graph N Name Name Vals) (t : tau) (doc : Document) :=
    forall (u v : N) (f : fld) (ftype : Name),
      g u f v ->
      lookupFieldType (label f) (t u) doc = Some ftype ->
      (ftype == (t v)) \/
      (declaresImplementation doc (t v) ftype) \/
      ((t v) \in (union doc ftype))                               
  .
  
  Record conformed_graph (doc : Document) := ConformedGraph {
                                                edges : graph N Name Name Vals;
                                                t : tau;
                                                wf_values : vals_to_scalar doc;
                                                wf_edges : edge_conforms edges t doc
                                              }.
  
  

End Conformance.