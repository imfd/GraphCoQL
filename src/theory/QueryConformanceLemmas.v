From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

From extructures Require Import ord fset fmap.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaAuxLemmas.
Require Import SchemaWellFormedness.
Require Import SchemaWFLemmas.

Require Import Query.
Require Import QueryAux.
Require Import QueryConformance.

Require Import SeqExtra.


Require Import Ssromega.


Section Theory.
  Transparent qname qresponse_name.


  Ltac apply_and3P := apply/and3P; split=> //.

  Ltac wfquery := case: schema=> sch Hhasty Hwf.
  Ltac query_conforms := simp query_conforms; try move/and5P; try apply/and5P.


  Variables (Name Vals : ordType).
  
  Section FragmentSpread.

    Variable (s : @wfSchema Name Vals).
    
    (* TODO: rename **)
    Lemma object_spreads_E parent_type ty :
      is_object_type s ty ->
      is_fragment_spread_possible s parent_type ty ->
      [\/ ty = parent_type,
       ty \in implementation s parent_type |
       ty \in union_members s parent_type].
    Proof.
      case: s=> sch Hty Hwf Hobj Hspread.
      apply/in_possible_typesPwf=> //.
      move: Hspread.
      rewrite /is_fragment_spread_possible.
      simp get_possible_types.
      move/is_object_type_wfP: Hobj => [intfs [flds Hlook] ].
      rewrite Hlook /=.
        by case lookup_type => [t|] //=; case: t => //=; intros; apply: seq1I_N_nil.
        
    Qed.



    
    Lemma object_spreads_in_object_scope type_in_scope t ϕ :
      is_object_type s type_in_scope ->
      is_object_type s t ->
      ϕ != [::] ->
      queries_conform s t ϕ -> 
      query_conforms s type_in_scope (InlineFragment t ϕ) <->
      t = type_in_scope.
    Proof.
    Admitted.
    

    
    Lemma interface_spreads_in_object_scope type_in_scope t ϕ :
      is_object_type s type_in_scope ->
      is_interface_type s t ->
      query_conforms s type_in_scope (InlineFragment t ϕ) ->
      type_in_scope \in implementation s t.
    Proof.
      move/is_object_type_wfP=> [intfs [flds Hlook] ].
      move/is_interface_type_wfP=> [iflds Hlook'].
      simp query_conforms=> /and3P [Hspread _ _].
      move: Hspread; rewrite /is_fragment_spread_possible; simp get_possible_types; rewrite Hlook Hlook' /=.
        by rewrite -seq1IC; apply: seq1I_N_nil.
    Qed.

    Lemma union_spreads_in_object_scope type_in_scope t ϕ :
      is_object_type s type_in_scope ->
      is_union_type s t ->
      query_conforms s type_in_scope (InlineFragment t ϕ) ->
      type_in_scope \in union_members s t.
    Proof.
      funelim (is_object_type s type_in_scope) => // _.
      funelim (is_union_type s t) => // _.
      simp query_conforms.
      move/and3P=> [Hspread _ _].
      move: Hspread; rewrite /is_fragment_spread_possible; simp get_possible_types; rewrite Heq Heq0 /=.
      rewrite /SchemaAux.union_members Heq.
        by rewrite -seq1IC; apply: seq1I_N_nil.
    Qed.

    
    Lemma abstract_spreads_in_object_scope type_in_scope t ϕ :
      is_object_type s type_in_scope ->
      ϕ != [::] ->
      queries_conform s t ϕ ->
      (is_interface_type s t \/ is_union_type s t) ->
      reflect (type_in_scope \in implementation s t \/ type_in_scope \in union_members s t)
              (query_conforms s type_in_scope (InlineFragment t ϕ)).
    Proof.
      move=> Hobj Hne Hqsc Htype.
      apply: (iffP idP).
      - case: Htype => [Hint | Hunion].
          by move/(interface_spreads_in_object_scope Hobj Hint); left.
            by move/(union_spreads_in_object_scope Hobj Hunion); right.
      - move: Hqsc; rewrite /queries_conform => /andP [Hall Hmerge].
        move=> H.      
        simp query_conforms; apply/and3P; split=> //.
        * move/is_object_type_wfP: Hobj => [intfs [flds Holook] ].
          case: H => [Himpl | Hmb]; 
                      rewrite /is_fragment_spread_possible; simp get_possible_types.
          move: (has_implementation_is_interface Himpl) => /is_interface_type_wfP [iflds Hilook].
            by rewrite Holook Hilook /= -seq1IC seq1I Himpl.
            
            move: (in_union Hmb) => /is_union_type_wfP [mbs Hulook].
            rewrite Holook Hulook /= -seq1IC seq1I.
            rewrite /union_members Hulook in Hmb.
              by rewrite Hmb.
    Qed.

    Lemma object_spreads_in_interface_scope type_in_scope t ϕ :
      is_object_type s t ->
      is_interface_type s type_in_scope ->
      ϕ != [::] ->
      queries_conform s t ϕ ->
      reflect (t \in implementation s type_in_scope)
              (query_conforms s type_in_scope (InlineFragment t ϕ)).
    Proof.
      move=> Hobj Hintf Hne Hqsc.
      apply: (iffP idP).
      - simp query_conforms => /and3P [Hspread _ _].
        move: (object_spreads_E Hobj Hspread) => [Heq | // | /in_union Hun].
        * move: (is_object_type_interfaceN Hobj); rewrite Heq.
            by rewrite /negb Hintf.
        * by move: (is_interface_type_unionN Hintf); rewrite /negb Hun.
      - move=> Himpl; simp query_conforms.
        apply/and3P; split=> //=.
        * rewrite /is_fragment_spread_possible.
          move/get_possible_types_interfaceE: Hintf => ->.
          move/get_possible_types_objectE: Hobj => ->.
            by rewrite seq1I Himpl.

              by move: Hqsc; rewrite /queries_conform => /andP [H1 H2].
    Qed.

    
  End FragmentSpread.

  Section QueryConformance.

    Variable (s : @wfSchema Name Vals).
    
    Lemma queries_conform_inv ty φ :
      all (query_conforms s ty) φ ->
      have_compatible_response_shapes s ty φ ->
      is_field_merging_possible s ty φ ->
      queries_conform s ty φ.
    Proof.
        by intros; rewrite /queries_conform; apply/and3P; split.
    Qed.
    
    

    Lemma found_fields_with_response_name_share_field_name_in_obj ty rname φ :
      is_object_type s ty ->
      is_field_merging_possible s ty φ ->
      forall fname,
        all (has_field_name fname) (find_queries_with_label s rname ty φ).
    Proof.
      elim: φ => //=; case=> [f α | l f α | f α β | l f α β | t β] φ IH Hscope; simp is_field_merging_possible.

      - rewrite Hscope /=; simp are_equivalent => /andP [Hequiv Hmerge] fname.
    Admitted.



    
    Lemma nf_conformsP type_in_scope f α φ :
      reflect (exists2 fld, lookup_field_in_type s type_in_scope f = Some fld &
                            [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
                             arguments_conform s fld.(fargs) α,
                             φ != [::] &
                             all (query_conforms s fld.(return_type)) φ])
              (query_conforms s type_in_scope (NestedField f α φ)).
    Proof.
      apply: (iffP idP).
      - simp query_conforms.
        case Hlook : lookup_field_in_type => [fld |] //= H.
          by exists fld.
               - move=> [fld Hlook H].
                   by simp query_conforms; rewrite Hlook. 
    Qed.

    Lemma nlf_conformsP type_in_scope l f α φ :
      reflect (exists2 fld, lookup_field_in_type s type_in_scope f = Some fld &
                            [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
                             arguments_conform s fld.(fargs) α,
                             φ != [::] &
                             all (query_conforms s fld.(return_type)) φ])
              (query_conforms s type_in_scope (NestedLabeledField l f α φ)).
    Proof.
      apply: (iffP idP).
      - simp query_conforms.
        case Hlook : lookup_field_in_type => [fld |] // H.
          by exists fld.
               - move=> [fld Hlook H].
                   by simp query_conforms; rewrite Hlook. 
    Qed.

    
    Lemma scope_is_obj_or_abstract_for_field ty q :
      is_field q ->
      query_conforms s ty q ->
      is_object_type s ty \/ is_interface_type s ty.
    Proof.
      case: q => //= [f α | l f α | f α φ | l f α φ] _; simp query_conforms;
                  case Hlook: lookup_field_in_type => [fld|] // _;
                                                       have H: lookup_field_in_type s ty f by rewrite /isSome Hlook.

      all: by apply: (lookup_field_in_type_is_obj_or_intf H).
    Qed.
    
    Lemma nested_field_is_obj_or_abstract ty n α ϕ :
      query_conforms s ty (NestedField n α ϕ) ->
      is_object_type s ty \/ is_interface_type s ty.
    Proof.
      simp query_conforms.
      case Hlook: lookup_field_in_type => [fld|] // _.
      have H: lookup_field_in_type s ty n by rewrite /isSome Hlook.
        by apply: (lookup_field_in_type_is_obj_or_intf H).
    Qed.

    Lemma scope_is_obj_or_abstract_for_nlf ty l f α φ :
      query_conforms s ty (NestedLabeledField l f α φ) ->
      is_object_type s ty \/ is_interface_type s ty.
    Proof.
      simp query_conforms.
      case Hlook: lookup_field_in_type => [fld|] // _.
      have H: lookup_field_in_type s ty f by rewrite /isSome Hlook.
        by apply: (lookup_field_in_type_is_obj_or_intf H).
    Qed.

    
    
    Lemma type_in_scope_N_scalar_enum :
      forall type_in_scope ϕ,
        query_conforms s type_in_scope ϕ ->
        [\/ is_object_type s type_in_scope,
         is_interface_type s type_in_scope |
         is_union_type s type_in_scope].
    Proof.
      move=> ty.
      case=> [f α |  l f α |  f α ϕ |  l f α ϕ |  t ϕ]; simp query_conforms.
      all: do ?[case Hlook: lookup_field_in_type => [fld|] //= _;
                                                   have H: lookup_field_in_type ty f by rewrite /isSome Hlook].
      all: do ?[by move: (lookup_field_in_type_is_obj_or_intf H) => [Hobj | Hint]; [constructor 1 | constructor 2] ].
      
    (*
    case Hlook: lookup_type => [tdef|] //.
    by case: tdef Hlook => //=; do ?[rewrite fset0I //=];
                         [constructor 1; simp is_object_type
                         | constructor 2; simp is_interface_type
                         | constructor 3; simp is_union_type]; rewrite Hlook.
    
    by rewrite fset0I /=.
  Qed.*)
    Admitted.

    Lemma type_in_scope_N_scalar type_in_scope φ :
      query_conforms s type_in_scope φ ->
      is_scalar_type s type_in_scope = false.
    Admitted.

    Lemma type_in_scope_N_enum type_in_scope φ :
      query_conforms s type_in_scope φ ->
      is_enum_type s type_in_scope = false.
    Admitted.

    
    Lemma type_in_scope_N_obj_is_abstract type_in_scope φ :
      query_conforms s type_in_scope φ ->
      is_object_type s type_in_scope = false ->
      is_abstract_type s type_in_scope.
    Proof.
        by move/type_in_scope_N_scalar_enum => [-> | Hintf | Hunion ] _ //; rewrite /is_abstract_type; apply/orP; [left | right].
    Qed.
    
    Lemma queries_conform_obj_int_union type_in_scope ϕ :
      ϕ != [::] ->
      queries_conform s type_in_scope ϕ ->
      [\/ is_object_type s type_in_scope,
       is_interface_type s type_in_scope |
       is_union_type s type_in_scope].
    Proof.
      rewrite /queries_conform.
      case: ϕ => //= hd tl _.
      move/andP => [/andP [Hqc Hqsc] _].
      apply (type_in_scope_N_scalar_enum Hqc).
    Qed.

    Lemma nlf_conforms_lookup_some ty l n α ϕ :
      query_conforms s ty (NestedLabeledField l n α ϕ) ->
      exists fld, lookup_field_in_type s ty n = Some fld.
    Proof. simp query_conforms.
      case Hlook : lookup_field_in_type => [fld'|] //.
        by exists fld'.
    Qed.

    Lemma queries_conform_int_impl ty ti qs :
      ty \in implementation s ti ->
             all (@is_field Name Vals) qs ->
             queries_conform s ti qs ->       
             queries_conform s ty qs.
    Proof.
      move=> Himpl Hflds.
      rewrite /queries_conform.
      move/andP=> [/allP Hqsc Hmerge].
      apply/andP; split=> //.
      apply/allP.
      move=> x Hin.
      move: (Hqsc x Hin) => {Hin}.
      case: x => //; [move=> f α | move=> l f α | move=> f α ϕ | move=> l f α ϕ | move=> t ϕ];
                  simp query_conforms; do ? rewrite (field_in_interface_in_object f Himpl);
                    do ? case lookup_field_in_type => //.
      - Admitted. (* Invalid case - all fields *)


    

    Lemma sf_conforms_in_interface_in_obj ti tyo f α :
      tyo \in implementation s ti ->
              query_conforms s ti (SingleField f α) ->
              query_conforms s tyo (SingleField f α).
    Proof.
      move=> Hin.
      simp query_conforms.
      case Hlook : lookup_field_in_type => [fld |] //= /andP [Hty Hα].
      move: (in_implementation_is_object Hin) => Hobj.
      move: (field_in_interface_in_object_same_return_type Hin Hlook) => [fld' Hlook' Hrty].
      rewrite Hlook' /= -Hrty.
      apply/andP; split => //.
      move: Hα; rewrite /arguments_conform.
      move/allP=> Hα.
      apply/allP=> arg Hain.
      move: (Hα arg Hain) => {Hα Hain}.
      case: arg => n v.
      have: lookup_field_in_type s ti f = Some fld -> fld \in fields s ti.
      move: (has_implementation_is_interface Hin) => /is_interface_type_E.
      case=> [i [flds Hilook] ].
      
      rewrite /fields /lookup_field_in_type Hilook.
    Admitted.

    
  End QueryConformance.

  
End Theory.