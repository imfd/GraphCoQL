From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.


Require Import Schema.
Require Import SchemaWellFormedness.
Require Import SchemaAux.
Require Import Graph.
Require Import GraphAux.

Require Import GraphConformance.

Require Import SeqExtra.


Section Theory.

  Variables (N Name Vals: ordType).

  Variable (s : @wfSchema Name Vals) (g : conformedGraph s).

  
  Lemma argument_conformsP ty fname arg :
    reflect (exists2 fld_arg, lookup_argument_in_type_and_field s ty fname arg.1 = Some fld_arg & s.(hasType) fld_arg.(argtype) arg.2)
            (argument_conforms s ty fname arg).
  Proof.
    apply: (iffP idP); rewrite /argument_conforms; case: arg => argname value.
    - case Hlook : lookup_argument_in_type_and_field => [arg|] // Hty.
        by exists arg.
    - by case=> fld_arg Hlook Hty; rewrite Hlook.
  Qed.

  
  Lemma nodes_have_object_typeP graph :
    reflect (forall node, node \in graph.(nodes) -> is_object_type s node.(type))
            (nodes_have_object_type s graph).
  Proof. by apply: (iffP allP). Qed.


  
  Lemma aux_root_query_type graph :
    root_type_conforms s graph -> graph.(root).(type) = s.(query_type).
  Proof. by rewrite /root_type_conforms; move/eqP. Qed.
  
  Lemma root_query_type :
    g.(root).(type) = s.(query_type).
  Proof.
    case: g => g' H *.
      by move: (aux_root_query_type H).
  Qed.

  Lemma node_in_graph_has_object_type :
    forall u, u \in g.(nodes) -> is_object_type s u.(type).
  Proof.
    apply/nodes_have_object_typeP.
    by case: g.
  Qed.

  

  Lemma neighbours_are_subtype_of_field u fld fdef  :
    lookup_field_in_type s u.(type) fld.(label) = Some fdef ->
    forall v, v \in neighbours_with_field g u fld ->
               v.(type) \in get_possible_types s fdef.(return_type).
  Proof.
    move=> Hlook.
    case: g => g' Hroot Hedges.
    
    have Hedge : forall e, e \in g'.(E) -> edge_conforms s g' e.
      by apply/allP; move: Hedges; rewrite /edges_conform; case/andP.

    move=> Hflds Hobjs v.
    rewrite /neighbours_with_field -in_undup => /mapP [v'].
    rewrite mem_filter => /andP [/andP [/eqP Hsrc /eqP Hfld] Hin] Htrgt.    
    move: (Hedge v' Hin).
    rewrite /edge_conforms /=.
    case: v' Hsrc Hfld Hin Htrgt => //=.
    case=> //= src fld' v' -> -> Hin ->.
      by rewrite Hlook /=; case/and3P.
  Qed.

  
End Theory.