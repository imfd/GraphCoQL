Require Import List.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord fset.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryConformance.

Require Import NRGTNF.

Section ValidFragments.

  Variables N Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.


  (* Check if it's possible to have an interface fragment in another one :
     - It is valid to spread an abstract on an abstract as long there is one object type
       that is a subtype of both -> Check if we eliminate this possibility *)
  Inductive Correct schema : (NamedType * NamedType) -> Query -> Prop :=
  | CF : forall f α root current,
      query_conforms schema current (SingleField f α) ->
      Correct schema (root, current) (SingleField f α)

  | CLF : forall l f α root current,
      query_conforms schema current (LabeledField l f α) ->
      Correct schema (root, current) (LabeledField l f α)
               
  | CNF : forall f α ϕ root current ty',
      query_conforms schema current (NestedField f α ϕ) ->
      lookup_field_type schema current f = Some ty' ->
      Forall (Correct schema (tname ty', tname ty')) ϕ ->
      Correct schema (root, current) (NestedField f α ϕ) 
               
  | CNLF : forall l f α ϕ root current ty',
      query_conforms schema current (NestedLabeledField l f α ϕ) ->
      lookup_field_type schema current f = Some ty' ->
      Forall (Correct schema (tname ty', tname ty')) ϕ ->
      Correct schema (root, current) (NestedLabeledField l f α ϕ) 

  (* If the query conforms to a type in scope, which is the same as the
     root type, then anything is correct as the inline's guard 
     (the conformance check rules out anything weird)
   *)
  | CIF_Any : forall root t ϕ,
      t <> root ->
      query_conforms schema root (InlineFragment t ϕ) ->
      Forall (Correct schema (root, t)) ϕ ->
      Correct schema (root, root) (InlineFragment t ϕ)

  | CIF_Root : forall root current ϕ,
      query_conforms schema current (InlineFragment root ϕ) ->
      Forall (Correct schema (root, root)) ϕ ->
      Correct schema (root, current) (InlineFragment root ϕ)

  | CIF_Spread : forall root current t φ,
      t <> root ->
      t <> current ->
      query_conforms schema current (InlineFragment t φ) ->
      is_fragment_spread_possible schema root t -> 
      Forall (Correct schema (root, t)) φ ->
      Correct schema (root, current) (InlineFragment t φ)
    
  (*
    Spec allows fragment to spread in asbtract scopes if there is at least one 
    object type in both types. This means it is possible to spread again into 
    this common type.
   *)
  | CIF_Subtype : forall root current t φ,
      query_conforms schema current (InlineFragment t φ) ->
      Forall (Correct schema (root, t)) φ ->
      (* An inline fragment cannot "drift" to another type not related to the root one *)
      is_subtype schema (NT t) (NT root) ->
      is_subtype schema (NT t) (NT current) ->
      Correct schema (root, current) (InlineFragment t φ)

        
  (* The inline's guard is the same as the previous one in scope *)            
  | CIF_Current : forall root current ϕ,
      current <> root ->
      query_conforms schema current (InlineFragment current ϕ) ->
      Forall (Correct schema (root, current)) ϕ ->
      Correct schema (root, current) (InlineFragment current ϕ).



  Fixpoint has_valid_fragments schema (root current : @NamedType Name) query : bool :=
    query_conforms schema current query &&
    match query with
    | NestedField f _ φ => match lookup_field_type schema current f with
                          | Some return_type => all (has_valid_fragments schema return_type return_type) φ
                          | _ => false
                          end
    | NestedLabeledField _ f _ φ => match lookup_field_type schema current f with
                                   | Some return_type => all (has_valid_fragments schema return_type return_type) φ
                                   | _ => false
                                   end
    | InlineFragment t φ => if current == root then
                             if t != root then
                               (* CIF_Any *)
                               all (has_valid_fragments schema root t) φ
                             else
                               (* CIF_Root with current = root *)
                               all (has_valid_fragments schema root root) φ
                           else
                             if t == root then
                               (* CIF_Root with current ≠ root *)
                               all (has_valid_fragments schema root root) φ
                             else
                             if t == current then
                               (* CIF_Current *)
                               all (has_valid_fragments schema root current) φ
                             else
                             if is_subtype schema (NT t) (NT root) && is_subtype schema (NT t) (NT current) then
                               (* CIF Subtype *)
                               all (has_valid_fragments schema root t) φ
                             else
                             if is_fragment_spread_possible schema root t then
                               (* CIF_Spread *)
                               all (has_valid_fragments schema root t) φ
                             else
                               false
    | _ => true
    
    end.


  Lemma valid_fragmentsP schema root current query :
    reflect (Correct schema (root, current) query)
            (has_valid_fragments schema root current query).
  Proof.
    apply: (iffP idP).
    - move: schema root current.
      elim query using Query_ind with
          (Pl := fun (qs : seq Query) =>
                  forall schema root current,
                  (all (has_valid_fragments schema root current) qs) ->
                  (Forall (Correct schema (root, current)) qs)) => //.
      * move=> f α schema root current; rewrite /has_valid_fragments => /andP [H _].
          by constructor.
      * move=> l f α schema root current; rewrite /has_valid_fragments => /andP [H _].
          by constructor.
      * move=> f α φ IH schema root current.
        rewrite /has_valid_fragments => /andP [H].
        case Hlook: lookup_field_type =>[rty|] //.
        rewrite -/(has_valid_fragments _ _ _).
        move/(IH schema rty rty) => Hall.
          by apply: CNF; [| apply: Hlook |].
      * move=> l f α φ IH schema root current.
        rewrite /has_valid_fragments => /andP [H].
        case Hlook: lookup_field_type =>[rty|] //.
        rewrite -/(has_valid_fragments _ _ _).
        move/(IH schema rty rty) => Hall.
          by apply: CNLF; [| apply: Hlook |].
      * move=> t φ IH schema root current.
        rewrite /has_valid_fragments => /andP [Hqc].
        case: ifP => //.
        move=> /eqP Heq.
        case: ifP => // Hneq.
        move/(IH schema root t) => Hall.
        rewrite Heq in Hqc *.
        by apply: CIF_Any => //; apply/eqP.
        move/eqP: Hneq => Heqt.
        move/(IH schema root root)=> Hall.
        rewrite Heqt in Hqc *.
        by apply: CIF_Root => //.
        move/eqP=> Hneq.
        case: ifP => // /eqP Heqt.
        move/(IH schema root root)=> Hall.
        rewrite Heqt in Hqc *.
        by apply: CIF_Root => //.
        case: ifP => // /eqP Heq.
        move/(IH schema root current) => Hall.
        rewrite Heq in Hqc *.
        by apply: CIF_Current; rewrite Heq in Heqt.
        case: ifP => // /andP.
        case=> [Hsubroot Hsubcurr].
        move/(IH schema root t)=> Hall.
        by apply: CIF_Subtype.
        move=> _.
        case: ifP => // Hspread.
        move/(IH schema root t)=> Hall.
          by apply: CIF_Spread.
      * move=> hd IH tl IH' schema root current.
        rewrite /all => /andP [Hval Htlval].
        apply/Forall_cons.
            by apply: (IH schema root current Hval).
            by apply: (IH' schema root current Htlval).
    - move: schema root current.
      elim query using Query_ind with
          (Pl := fun qs =>
                  forall schema root current,
                  Forall (Correct schema (root, current)) qs ->
                  all (has_valid_fragments schema root current) qs) => //.
      * by intros; inversion H; rewrite /has_valid_fragments; apply/andP.
      * by intros; inversion H; rewrite /has_valid_fragments; apply/andP.
      * move=> f α φ IH schema root current Hc; inversion Hc.
        rewrite /has_valid_fragments; apply/andP; split => //.
        by rewrite H5; apply: (IH schema ty' ty' H6).
      * move=> l f α φ IH schema root current Hc; inversion Hc.
        rewrite /has_valid_fragments; apply/andP; split => //.
          by rewrite H6; apply: (IH schema ty' ty' H7).
      * move=> t φ IH schema root current Hc; inversion Hc.
        + rewrite /has_valid_fragments; apply/andP; split => //.
          case: ifP => // _.
          case: ifP => // /eqP Hneq.
            by apply: (IH schema current t H5).
            by rewrite Hneq in H5; apply: (IH schema current current  H5).
          case: ifP => // /eqP Heq.
            by rewrite Heq in H5; apply: (IH schema current current H5). 
          case: eqP => // _.

  Admitted.

  Lemma has_valid_fragments_inline_subqueries schema root current t φ :
    has_valid_fragments schema root current (InlineFragment t φ) ->
    all (has_valid_fragments schema root t) φ.
  Proof.
    rewrite /has_valid_fragments => /andP [Hqc].
    case: eqP => // Heq.
    case: eqP => // Hneq /=.
      by rewrite Hneq.
      case: eqP => //= Hteq.
      by rewrite Hteq.
    case: eqP => // Hteq'. by rewrite Hteq'.
    case: ifP => // _.
    case: ifP => //.
  Qed.

 
    
  Lemma correct_object_E schema root current t ϕ :
    is_object_type schema t ->
    Correct schema (root, current) (InlineFragment t ϕ) ->
    (is_subtype schema (NT t) (NT current)).
      (*
    (t = root /\ is_subtype schema (NT t) (NT current)) |
    (t = current /\ is_subtype schema (NT t) (NT root))]. *)
  Proof.
    move=> Hobj Hok.
    inversion Hok => //.
    - move: H4; rewrite /query_conforms.
      move/and4P=> [_ Hspread _ _].
      move: (object_spreads_E Hobj Hspread) => [-> | Himpl | Hmb]; rewrite /is_subtype; apply/or3P.
        by constructor 1; apply/eqP.
        by constructor 2; rewrite declares_in_implementation.
        by constructor 3.
    - move: H2; rewrite /query_conforms.
      move/and4P=> [_ Hspread _ _].
      move: (object_spreads_E Hobj Hspread) => [-> | Himpl | Hmb]; rewrite /is_subtype;
      apply/or3P.                                        
        by constructor 1; apply/eqP.
        by constructor 2; rewrite declares_in_implementation.
        by constructor 3.
  Abort.

  Lemma correct_conforms schema root current q :
    Correct schema (root, current) q ->
    query_conforms schema current q.
  Proof. by move=> H; inversion H. Qed.

  Lemma queries_correct_conform schema root current queries :
    Forall (Correct schema (root, current)) queries ->
    all (query_conforms schema current) queries.
  Proof.
    elim: queries => // hd tl IH.
    move=> H; inversion H => //=.
    apply/andP; split.
    apply: (correct_conforms H2).
    by apply: IH.
  Qed.

   Lemma single_field_correct schema ty ty' n α :
    query_conforms schema ty' (SingleField n α) ->
    Correct schema (ty, ty') (SingleField n α).
  Proof. by move=> Hqc; apply: CF. Qed.

 


  Lemma nf_correct_lookup_some schema root current n α ϕ :
    Correct schema (root, current) (NestedField n α ϕ) ->
    exists fld, lookup_field_type schema current n = Some fld. 
  Proof.
    move=> H; inversion H.
      by exists ty'.
  Qed.

  Lemma nlf_correct_lookup_some schema root current l n α ϕ :
    Correct schema (root, current) (NestedLabeledField l n α ϕ) ->
    exists fld, lookup_field_type schema current n = Some fld. 
  Proof.
    move=> H; inversion H.
      by exists ty'.
  Qed.

  Lemma nf_queries_conform'' schema ty n α ϕ fld :
    lookup_field_in_type schema ty n = Some fld ->
    query_conforms schema ty (NestedField n α ϕ) ->
    queries_conform schema fld.(return_type) ϕ.
  Proof.
    move=> Hlook; rewrite /query_conforms.
    rewrite Hlook.
    rewrite -/(query_conforms schema fld.(return_type)).
    move/and4P=> [Hnty HNnil Hargs Hall].
    rewrite /queries_conform.
    by apply/andP. 
  Qed.

  Lemma nlf_queries_conform'' schema ty l n α ϕ fld :
    lookup_field_in_type schema ty n = Some fld ->
    query_conforms schema ty (NestedLabeledField l n α ϕ) ->
    queries_conform schema fld.(return_type) ϕ.
  Proof.
    move=> Hlook; rewrite /query_conforms.
    rewrite Hlook -/(query_conforms schema fld.(return_type)).
    move/and4P=> [Hnty HNnil Hargs Hall].
    rewrite /queries_conform.
    by apply/andP. 
  Qed.

  
  
  (**
     If query is free of issues and its type in the schema is "ty",
     then its subqueries are also free of issues for the given type.
   **)
  Lemma nested_field_subqueries_correct schema root current n α ϕ ty :
    Correct schema (root, current) (NestedField n α ϕ) ->
    lookup_field_type schema current n = Some ty ->
    Forall (Correct schema (tname ty, tname ty)) ϕ.
  Proof.  by move=> H Hlook; inversion H; rewrite Hlook in H6; case: H6 => ->. Qed.

  Lemma nlf_queries_correct schema root current l n α ϕ fld :
    lookup_field_type schema current n = Some fld ->
    Correct schema (root, current) (NestedLabeledField l n α ϕ) ->
    Forall (Correct schema (tname fld, tname fld)) ϕ.
  Proof.  by move=> Hlook H; inversion H; rewrite Hlook in H7; case: H7 => ->. Qed.

  
  Lemma inline_subqueries_correct schema root current t ϕ :
    Correct schema (root, current) (InlineFragment t ϕ) ->
    Forall (Correct schema (root, t)) ϕ.
  Proof.
      by move=> H; inversion H. Qed.


  
  Lemma queries_correct_impl schema ty ti queries :
    ty \in implementation schema ti ->
    Forall (Correct schema (ty, ti)) queries ->
    Forall (Correct schema (ty, ty)) queries.
  Admitted.

  Lemma queries_correct_mb schema ty tu queries :
    ty \in union_members schema tu ->
    Forall (Correct schema (ty, tu)) queries ->
    Forall (Correct schema (ty, ty)) queries.
  Admitted.     

  Lemma ble schema ty ti queries :
    ty \in implementation schema ti ->
    query_conforms schema ty (InlineFragment ti queries) ->
    Correct schema (ty, ty) (InlineFragment ti queries) ->
    queries_conform schema ty queries.
  Admitted.

  Lemma bleble schema ty ti queries :
    ty \in implementation schema ti ->
    queries_conform schema ti queries ->
    Forall (Correct schema (ty, ti)) queries ->
    queries_conform schema ty queries.
  Admitted.

  Lemma bleble' schema ty tu queries :
    ty \in union_members schema tu ->
    queries_conform schema tu queries ->
    Forall (Correct schema (ty, tu)) queries ->
    queries_conform schema ty queries.
  Admitted.

  

  Lemma foo schema ty ti queries :
    is_object_type schema ty ->
    is_interface_type schema ti ->
    is_fragment_spread_possible schema ty ti ->
    queries != [::] ->
    Forall (Correct schema (ty, ti)) queries ->
    query_conforms schema ty (InlineFragment ti queries).
  Proof.
    move=> Hobj Hint Hspread Hne Hqsok.
    rewrite /query_conforms.
    apply/and4P; split=> //.
      by apply/or3P; constructor 2.
    by move: (queries_correct_conform Hqsok).
  Qed.

  Lemma foo' schema ty tu queries :
    is_object_type schema ty ->
    is_union_type schema tu ->
    is_fragment_spread_possible schema ty tu ->
    queries != [::] ->
    Forall (Correct schema (ty, tu)) queries ->
    query_conforms schema ty (InlineFragment tu queries).
  Proof.
    move=> Hobj Hunion Hspread Hne Hqsok.
    rewrite /query_conforms.
    apply/and4P; split=> //.
      by apply/or3P; constructor 3.
    by move: (queries_correct_conform Hqsok).
  Qed.


  Lemma normalized_queries_are_valid schema type_in_scope φ :
    is_in_normal_form schema φ ->
    query_conforms schema type_in_scope φ ->
    Correct schema (type_in_scope, type_in_scope) φ.
  Abort.

End ValidFragments.