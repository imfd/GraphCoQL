Require Import List Relations.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

From extructures Require Import ord fset fmap.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryAux.
Require Import QueryConformance.

Require Import Graph.
Require Import GraphAux.
Require Import GraphConformance.

Require Import NRGTNF.

Require Import ValidFragments.

Require Import Ssromega.

Section QueryRewrite.

  Variables N Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.

  Notation is_field := (@QueryAux.is_field Name Vals).
  Notation is_inline_fragment := (@QueryAux.is_inline_fragment Name Vals).


 
  Equations map_In {A B : Type} (l : list A) (f : forall (x : A), In x l -> B) : list B :=
      map_In nil _ := nil;
      map_In (cons hd tl) f := cons (f hd _) (map_In (fun x H => f x _)).
  
  Lemma map_In_spec {A B : Type} (f : A -> B) (l : list A) :
    map_In (fun (x : A) (_ : In x l) => f x) = List.map f l.
  Proof.
    remember (fun (x : A) (_ : In x l) => f x) as g.
    funelim (map_In g); rewrite ?H; trivial.
    Admitted.


  Ltac foo := intros; program_simpl; rewrite -/(queries_size _); try ssromega.

  Hint Extern 100 => foo:Below.
  
  Equations normalize schema (type_in_scope : @NamedType Name) (queries : seq (@Query Name Vals))  : seq (@Query Name Vals) :=
    normalize schema type_in_scope queries by rec (queries_size queries) lt :=
      normalize _ _ [::] := [::];
      normalize schema type_in_scope (cons (SingleField f α) queries) :=
          let normalized := normalize schema type_in_scope queries in
          if is_object_type schema type_in_scope then
            (SingleField f α) :: normalized
          else
            let possible_types := get_possible_types schema type_in_scope in
            [seq (InlineFragment ty [:: (SingleField f α)]) | ty <- possible_types] ++ normalized;

      normalize schema type_in_scope (cons (LabeledField l f α) queries) :=
          let normalized := normalize schema type_in_scope queries in
          if is_object_type schema type_in_scope then
            (LabeledField l f α) :: normalized
          else
            let possible_types := get_possible_types schema type_in_scope in
            [seq (InlineFragment ty [:: (LabeledField l f α)]) | ty <- possible_types] ++ normalized;
                                                                                    
      normalize schema type_in_scope (cons (NestedField f α φ) queries) :=
          let normalized := normalize schema type_in_scope queries in
          if is_object_type schema type_in_scope then
            match lookup_field_type schema type_in_scope f with
            | Some return_type => (NestedField f α (normalize schema return_type φ)) :: normalized
            | _ => [::]
            end
          else
            let possible_types := get_possible_types schema type_in_scope in
            let normalized_head := normalize schema type_in_scope φ in
            [seq (InlineFragment ty [:: NestedField f α normalized_head]) | ty <- possible_types] ++ normalized;
         
              
     normalize schema type_in_scope (cons (NestedLabeledField l f α φ) queries) :=
          let normalized := normalize schema type_in_scope queries in
          if is_object_type schema type_in_scope then
            match lookup_field_type schema type_in_scope f with
            | Some return_type => (NestedLabeledField l f α (normalize schema return_type φ)) :: normalized
            | _ => [::]
            end
          else
            let possible_types := get_possible_types schema type_in_scope in
            let normalized_head := normalize schema type_in_scope φ in
            [seq (InlineFragment ty [:: NestedLabeledField l f α normalized_head]) | ty <- possible_types] ++ normalized;
              
     normalize schema type_in_scope (cons (InlineFragment t φ) queries) := 
          let normalized := normalize schema type_in_scope queries in
          if is_object_type schema type_in_scope then
            (normalize schema type_in_scope φ) ++ normalized
          else
          if is_object_type schema t && is_subtype schema (NT t) (NT type_in_scope) then
            (InlineFragment t (normalize schema t φ)) :: normalized
          else
            (* abstract type in scope & guard has abstract type *)
            let possible_types := get_possible_types schema t in
            let scope_possible_types := get_possible_types schema type_in_scope in
            let intersection := (scope_possible_types :&: possible_types)%fset in
            [seq (InlineFragment ty (normalize schema ty φ)) | ty <- intersection] ++ normalized
  .
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.


  

 
  Ltac query_conforms := rewrite /query_conforms -/(query_conforms _ _); try move/and4P; try apply/and4P.

  Lemma normalize_in_object_scope_are_fields schema graph u type_in_scope queries :
    all (query_conforms schema type_in_scope) queries ->
    all (has_valid_fragments schema graph u type_in_scope) queries ->
    is_object_type schema type_in_scope ->
    (forall q u ty, q \in queries ->
                     query_conforms schema ty q ->
                     has_valid_fragments schema graph u ty ->
                     is_field 
    all is_field (normalize schema type_in_scope queries).
  Proof.
    elim: queries => // hd.
    elim hd using Query_ind with
        (Pl := fun qs =>
                all (query_conforms schema type_in_scope) qs ->
                all (has_valid_fragments schema graph u type_in_scope) qs ->
                is_object_type schema type_in_scope ->
                all is_field (normalize schema type_in_scope qs)) => //;
    [move=> f α tl IH; rewrite normalize_equation_2 | 
     move=> l f α tl IH; rewrite normalize_equation_3 |
     move=> f α φ IH tl IH'; rewrite normalize_equation_4 |
     move=> l f α φ IH tl IH'; rewrite normalize_equation_5 |
     move=> t φ IH tl IH'; rewrite normalize_equation_6].

    all: do ?[by rewrite /all -/(all _ _) => /andP [_ Hqsc] /andP [Hval Hvals] Hobj; rewrite Hobj;
             rewrite /all; apply/andP; split => //; apply: (IH Hqsc Hvals Hobj)].
    - rewrite /all -/(all _ _) => /andP [/nf_conforms_lookup_some [fld Hlook] Hqsc].
      do 2 rewrite  -/(all _ _).
      move=> /andP [Hval Hvals] Hobj; rewrite Hobj.
      move/lookup_field_in_type_has_type :  Hlook => Hlook.
      case lookup_field_type => //= rty.
      by apply: (IH' Hqsc Hvals Hobj).
    - rewrite /all -/(all _ _) => /andP [/nf_conforms_lookup_some [fld Hlook] Hqsc].
      do 2 rewrite  -/(all _ _).
      move=> /andP [Hval Hvals] Hobj; rewrite Hobj.
      move/lookup_field_in_type_has_type :  Hlook => Hlook.
      case lookup_field_type => //= rty.
      by apply: (IH' Hqsc Hvals Hobj).
    - rewrite /all -/(all _ _) => /andP [Hqc Hqsc].
      do 2 rewrite  -/(all _ _).
      move=> /andP [Hval Hvals] Hobj; rewrite Hobj.
      rewrite all_cat; apply/andP; split; last first.
      apply: (IH' Hqsc Hvals Hobj).
      apply: IH => //; last first.
      move: Hval;
        rewrite /has_valid_fragments is_object_ifunionF => //.
      by rewrite is_object_ifinterfaceF => // /andP [_ H].
  Abort.
      
    
  Lemma normalize_to_normal_form schema graph u type_in_scope queries :
    all (query_conforms schema type_in_scope) queries ->
    all (has_valid_fragments schema graph u type_in_scope) queries ->
    are_in_normal_form schema (normalize schema type_in_scope queries).
  Proof.
    funelim (normalize schema type_in_scope queries) => //;  rewrite {1}/all -/(all _ _)=> /andP [Hqc Hqsc].
    rewrite /all -/(all _ _) => /andP [Hval Htlval].
    - rewrite /are_in_normal_form.
      apply/andP; split.
      apply/orP.
      case Hobj: is_object_type; [left | right].
      
      

  
  Equations normalize schema (type_in_scope : @NamedType Name) (queries : seq (@Query Name Vals)) : seq (@Query Name Vals) :=
    normalize schema type_in_scope queries by rec (queries_size queries) lt :=
      normalize schema type_in_scope [::] => [::];

      normalize schema type_in_scope (cons (SingleField f α) ϕ) :=
        let ϕ' := normalize schema type_in_scope ϕ in
      
        if is_object_type schema type_in_scope then
          let lifted := lift__queries ϕ' in
          (SingleField f α) :: (γ__φ (SingleField f α) lifted)

        else
        if is_interface_type schema type_in_scope then
          let filtered := γ__φ (SingleField f α) ϕ' in
          map_In (fun query (H : In query filtered) => 
                     match query with
                     | InlineFragment t φ => InlineFragment t (normalize schema t ((SingleField f α) :: φ))
                     | _ => query
                     end)
        else
          (* This should not be possible in a wf query *)
          [::];

      normalize schema type_in_scope (cons (LabeledField l f α) ϕ) :=
        let ϕ' := normalize schema type_in_scope ϕ in
      
        if is_object_type schema type_in_scope then
          let lifted := lift__queries ϕ' in
          (LabeledField l f α) :: (γ__φ (LabeledField l f α) lifted)

        else
        if is_interface_type schema type_in_scope then
          let filtered := γ__φ (LabeledField l f α) ϕ' in
          (map_In (fun query (H : In query filtered) =>
                     if query is InlineFragment t φ then
                       InlineFragment t (normalize schema t ((LabeledField l f α) :: φ))
                     else
                       query))
        else
          (* This should not be possible in a wf query *)
          [::];


      normalize schema type_in_scope (cons (NestedField f α φ) ϕ) :=
        let ϕ' := normalize schema type_in_scope ϕ in

        if is_object_type schema type_in_scope then
          let lifted := lift__queries ϕ' in
          let collected := β__queries (NestedField f α φ) lifted in
          match lookup_field_type schema type_in_scope f with
          | Some return_type => (NestedField f α (normalize schema return_type collected)) :: γ__φ (NestedField f α φ) lifted
          | _ => [::] (* Should never happen *)
          end

        else
        if is_interface_type schema type_in_scope then
          let filtered := γ__φ (NestedField f α φ) ϕ' in
          map_In (fun query (H : In query filtered) => 
                    if query is InlineFragment t β then
                      InlineFragment t (normalize schema t ((NestedField f α φ) :: β))
                    else
                      query)

        else
          (* This should not be possible in a wf query *)
          [::];

      normalize schema type_in_scope (cons (NestedLabeledField l f α φ) ϕ) :=
        let ϕ' := normalize schema type_in_scope ϕ in

        if is_object_type schema type_in_scope then
          let lifted := lift__queries ϕ' in
          let collected := β__queries (NestedLabeledField l f α φ) lifted in
          match lookup_field_type schema type_in_scope f with
          | Some return_type => (NestedLabeledField l f α (normalize schema return_type collected)) :: γ__φ (NestedLabeledField l f α φ) lifted
          | _ => [::] (* Should never happen *)
          end

        else
        if is_interface_type schema type_in_scope then
          let filtered := γ__φ (NestedLabeledField l f α φ) ϕ' in
          map_In (fun query (H : In query filtered) =>
                    if query is InlineFragment t β then
                      InlineFragment t (normalize schema t ((NestedLabeledField l f α φ) :: β))
                    else
                      query)

        else
          (* This should not be possible in a wf query *)
          [::];

          
      normalize schema type_in_scope (cons (InlineFragment t φ) ϕ) :=
        let ϕ' := normalize schema type_in_scope ϕ in

        if is_object_type schema type_in_scope then
          normalize schema type_in_scope (φ ++ ϕ')
        else
        if is_interface_type schema type_in_scope then
          if t == type_in_scope then
            normalize schema type_in_scope (φ ++ ϕ')
          else (* Object type in valid fragments *)
            let collected := β__queries (InlineFragment t φ) ϕ' in
            (InlineFragment t (normalize schema t collected)) :: (γ__φ (InlineFragment t φ) ϕ')        
      else (* union *)
        let collected := β__queries (InlineFragment t φ) ϕ' 
        in
        (InlineFragment t (normalize schema t collected)) :: (γ__φ (InlineFragment t φ) ϕ')
  .

  Next Obligation.
  



      
End QueryRewrite.

