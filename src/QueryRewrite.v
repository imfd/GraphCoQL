Require Import List Relations.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

From extructures Require Import ord fmap.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryAux.
Require Import QueryConformance.

Require Import NRGTNF.

Require Import ValidFragments.

Require Import Ssromega.

Section QueryRewrite.

  Variables N Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.

  Notation is_field := (@QueryAux.is_field Name Vals).
  Notation is_inline_fragment := (@QueryAux.is_inline_fragment Name Vals).
  
  Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.


  Equations map_In {A B : Type} (l : list A) (f : forall (x : A), In x l -> B) : list B :=
      map_In nil _ := nil;
      map_In (cons hd tl) f := cons (f hd _) (map_In (fun x H => f x _)).
  
  Lemma map_In_spec {A B : Type} (f : A -> B) (l : list A) :
    map_In (fun (x : A) (_ : In x l) => f x) = List.map f l.
  Proof.
    remember (fun (x : A) (_ : In x l) => f x) as g.
    funelim (map_In g); rewrite ?H; trivial.
    Admitted.


  Equations β__subqueryextract (filter query: @Query Name Vals) : seq (@Query Name Vals) :=
    {
      β__subqueryextract (NestedField f α β) (NestedField f' α' χ) <= (f == f') && (α == α') => {
          | true => χ;
          | false => [::]
      };

      β__subqueryextract (NestedLabeledField l f α β) (NestedLabeledField l' f' α' χ) <= [&& (l == l'), (f == f') & (α == α')] => {
      | true => χ;
      | false => [::]
      };

      β__subqueryextract (InlineFragment t β) (InlineFragment t' χ) <= t == t' => {
      | true => χ;
      | false => [::]
      };
      
      β__subqueryextract _ _ := [::]
    }.
   

  Equations lift (query : @Query Name Vals) : seq (@Query Name Vals) :=
    {
      lift (InlineFragment _ φ) := φ;
      lift _ := [::]
    }.

  Equations lift__queries (queries : seq (@Query Name Vals)) : seq (@Query Name Vals) :=
    {
      lift__queries [::] := [::];
      lift__queries (cons hd tl) := (lift hd) ++ (lift__queries tl)
    }.
  
  
  Equations β__queries (flt : @Query Name Vals) (queries : seq (@Query Name Vals)) : seq (@Query Name Vals) :=
    {
      β__queries _ [::] := [::];
      β__queries flt (cons hd tl) := (β__subqueryextract flt hd) ++ (β__queries flt tl)
    }.

  
  Definition γ__φ (flt : Query) (queries : seq Query) : seq (@Query Name Vals) :=
    [seq query <- queries | ~~ partial_query_eq flt query].

  Obligation Tactic := intros; program_simpl; try ssromega.
  Equations normalize schema (type_in_scope : @NamedType Name) (queries : seq (@Query Name Vals))  : seq (@Query Name Vals) :=
    normalize schema type_in_scope queries by rec (queries_size queries) lt :=
      normalize _ _ [::] := [::];
      normalize schema type_in_scope (cons (InlineFragment t φ) queries) := 
          let normalized := normalize schema type_in_scope queries in
          if t == type_in_scope then
            normalize schema type_in_scope (φ ++ queries)
          else
          if is_subtype schema (NT t) (NT type_in_scope) then
            (InlineFragment t (normalize schema t φ)) :: normalized
          else
            if is_fragment_spread_possible schema type_in_scope t then 
              normalize schema type_in_scope (φ ++ queries)
            else
              (* Should not happen ? *)
              [::];

            
      normalize schema type_in_scope (cons query queries) :=
          let normalized := normalize schema type_in_scope queries in
          if is_object_type schema type_in_scope then
              (* In a valid query, if there are fragments, they must be
                 on supertype or the same type. Then, every field in those
                 subqueries exist in the current type, therefore they should
                 be lifted on normalization. *)
              query :: normalized
          else
          if is_interface_type schema type_in_scope then
            if all is_inline_fragment normalized then
              map_In (fun q (H : In q normalized) =>
                        if q is InlineFragment t φ then
                          InlineFragment t (query :: φ)
                        else
                          q)
            else
              query :: normalized
          else
            [::]
  .
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.
  Next Obligation.
  Qed.
  Next Obligation.
      by rewrite queries_size_app -/(queries_size _); ssromega.
  Qed.
  Next Obligation.
      by rewrite -/(queries_size _); ssromega.
  Qed.
  Next Obligation.
          by rewrite queries_size_app -/(queries_size _); ssromega.
  Qed.


  Lemma normalize_in_object_scope_are_fields schema root current queries :
    all (has_valid_fragments schema root current) queries ->
    is_object_type schema current ->
    all is_field (normalize schema current queries).
  Proof.
    funelim (normalize schema current queries) => //.
    all: do ?[by rewrite {1}/all -/(all _ _) => /andP [Hval Hvals] Hobj; rewrite Hobj;
              rewrite /all; apply/andP; split => //; apply: (H root)]. 

    rewrite {1}/all -/(all _ _) => /andP [Hval Hvals] Hobj.
    case: eqP => // Heq.
    apply: (H0 root).
    rewrite all_cat; apply/andP; split => //.
    rewrite Heq in Hval.
    by apply: (has_valid_fragments_inline_subqueries Hval) => //.
    exact: Hobj.
    case: ifP => //.
    move/(is_subtype_obj_eq Hobj) => Hteq. by rewrite Hteq in Heq.
    move=> _.
    case: ifP=> // Hspread.
    apply: (H0 root) => //.
    rewrite all_cat; apply/andP; split => //.
    
    rewrite has_valid_fragmentsP in Hval.

    
  Lemma normalize_to_normal_form schema root current queries :
    all (has_valid_fragments schema root current) queries ->
    are_in_normal_form schema (normalize schema current queries).
  Proof.
    elim: queries root current => // hd tl IH root current.
    rewrite /all => /andP [Hval Htlval].
    case: hd Hval.
    - move=> f α.
      rewrite normalize_equation_2.
    rewrite /are_in_normal_form.
    apply/andP; split.
    apply/orP. left.
    simpl.
    move: (H root Htlval).
    rewrite /are_in_normal_form.

  
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

