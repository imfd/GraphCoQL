From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

From extructures Require Import ord fset fmap.

Require Import Schema.
Require Import SchemaAux.
Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.
Require Import SeqExtra.


Require Import Ssromega.

Section QueryConformance.

  Variables Name Vals : ordType.
  
  Implicit Type schema : @wfSchema Name Vals.  
  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  Implicit Type type : @type Name.

  Notation is_inline_fragment := (@is_inline_fragment Name Vals).

  Section All.
    Equations? all_In {A : eqType} (s : seq A) (f : forall x, x \in s -> bool) : bool :=
        {
          all_In [::] _ := true;
          all_In (hd :: tl) f := (f hd _) && (all_In tl (fun x H => f x _))
        }.
    by apply: mem_head.
    by apply: mem_tail.
    Defined.


    
    Fixpoint map_all {A : eqType} (p : A -> A -> bool) (s : seq A) : bool :=
      match s with
      | [::] => true
      | (hd :: tl) => all (p hd) tl && map_all p tl
      end.

  End All.
  
  Lemma fset1I_eq {A : ordType} (a b : A) :
    (fset1 a :&: fset1 b)%fset != fset0 -> a = b.
  Proof.
    rewrite fset1I.
    case: ifP => //.
    by move/fset1P => //.
  Qed.

  Lemma fset1I_N_fset0 {A : ordType} (a : A) :
    (fset1 a :&: fset1 a)%fset != fset0.
  Proof.
    rewrite fset1I.
    case: ifP => //.
      by rewrite in_fset1 eqxx.
  Qed.
  
  (** Checks whether a query's argument (arg name + value associated) conforms to an argument
      of a field defined in the schema.
      
      It basically consists on checking whether the field has an argument with the same name
      as the query's argument, and whether the type of the value associated matches the
      type of the field's argument (as defined in the schema).

      ∃ argument ∈ field, name(argument) = name(α) ∧ value(α) has_type type(argument)
   **)
  Definition argument_conforms schema (args : seq FieldArgumentDefinition) (arg : Name * Vals) : bool :=
    let: (argname, value) := arg in
    has (fun argdef => let: FieldArgument name ty := argdef in
                    (name == argname) && schema.(hasType) ty value) args.
  

  (** Checks whether a set of arguments (described as a partial mapping between names and values)
      conform to a set of fields. 

      See also [arguments_conforms].
   **)
  Definition arguments_conform schema (args : seq.seq FieldArgumentDefinition) (α : {fmap Name -> Vals}) : bool :=
    all (argument_conforms schema args) α.
     

  
  (** Checks whether a type can be used as an inline fragment's guard 
      in a given context with another type in scope (parent type).

      It basically amounts to intersecting the possible types of each
      and check that the intersection is not empty.


      See also [SchemaAux - get_possible_types].

     https://facebook.github.io/graphql/June2018/#sec-Fragment-spread-is-possible
     https://facebook.github.io/graphql/June2018/#GetPossibleTypes()
   **)
  Definition is_fragment_spread_possible schema parent_type ty : bool :=
    let ty_possible_types := get_possible_types schema ty in
    let parent_possible_types := get_possible_types schema parent_type in
    let applicable_types := (ty_possible_types :&: parent_possible_types)%SEQ in
    applicable_types != [::].

  
  (* TODO: rename **)
  Lemma object_spreads_E schema parent_type ty :
    is_object_type schema ty ->
    is_fragment_spread_possible schema parent_type ty ->
    [\/ ty = parent_type,
     ty \in implementation schema parent_type |
     ty \in union_members schema parent_type].
  Proof.
    case: schema=> sch Hty Hwf Hobj Hspread.
    apply/in_possible_typesPwf=> //.
    move: Hspread.
    rewrite /is_fragment_spread_possible.
    simp get_possible_types.
    move/is_object_type_wfP: Hobj => [intfs [flds Hlook]].
    rewrite Hlook /=.
    by case lookup_type => [t|] //=; case: t => //=; intros; apply: seq1I_N_nil.
    
  Qed.


  (*Lemma eq_spreads schema ty :
    [\/ is_object_type schema ty, is_interface_type schema ty | is_union_type schema ty] ->
    is_fragment_spread_possible schema ty ty.
  Proof.
    case.
    - move/is_object_type_E=> [obj [intf [flds Hlook]]].
      rewrite /is_fragment_spread_possible /get_possible_types Hlook.
        by apply: fset1I_N_fset0.
    - move/is_interface_type_E => [intf [flds Hlook]].
      rewrite /is_fragment_spread_possible /get_possible_types Hlook.
   *)

 Lemma map_snd_pair_comp {T A : Type} (s : seq T) (t : A) :  [seq (snd \o (pair t)) i | i <- s] = s.
 Proof.
     by elim: s => // hd tl' IH /=; rewrite IH.
 Qed.
 
 Equations have_same_type schema : @type Name -> @type Name -> bool :=
   {
     have_same_type schema (NT rty) (NT rty')
       with (is_scalar_type schema rty || is_enum_type schema rty) :=
       {
       | true := rty == rty';
       | _ := is_composite_type schema rty'
       };
     have_same_type schema (ListType rty) (ListType rty') := have_same_type schema rty rty';
     have_same_type _ _ _ := false
   }.

 Definition aux_queries_size (queries : seq (Name * @Query Name Vals)) :=
   queries_size [seq q.2 | q <- queries].


 Definition unline query : seq Query :=
   if query is InlineFragment t φ then φ else [:: query].


 
 Equations have_same_response_shape schema
           (q1 : @Query Name Vals) (pty1 : Name)
           (q2 : @Query Name Vals) (pty2 : Name) : bool by wf (query_size q1 + query_size q2) :=
   {
     have_same_response_shape schema (InlineFragment t φ) pty1 q2 pty2 :=
       all_In φ (fun q Hin => have_same_response_shape schema q t q2 pty2);
     
     have_same_response_shape schema q1 pty1 (InlineFragment t φ) pty2 :=
       all_In φ (fun q Hin => have_same_response_shape schema q1 pty1 q t);
     
     have_same_response_shape schema q1 pty1 q2 pty2
       with (qresponse_name q1 _) == (qresponse_name q2 _) :=
       {
       | true :=
         match lookup_field_type schema pty1 (qname q1 _), lookup_field_type schema pty2 (qname q2 _) with
         | Some rty1, Some rty2 =>
           have_same_type schema rty1 rty2 &&
           all_In q1.(qsubquery) (fun q Hin1 => all_In  q2.(qsubquery) (fun q' Hin2 => have_same_response_shape schema q rty1 q' rty2)) 
                                    
         | _, _ => false
         end;

       | _ := true
       }
   }.
 Solve Obligations with intros; simp query_size; move: (in_queries_lt Hin) => Hlt; ssromega.
 Next Obligation.
   intros; simp query_size; move: (in_queries_lt Hin1) (in_queries_lt Hin2) => Hlt1 Hlt2; ssromega.
 Qed.
 Next Obligation.
   intros; simp query_size; move: (in_queries_lt Hin1) (in_queries_lt Hin2) => Hlt1 Hlt2; ssromega.
 Qed.
 Next Obligation.
   intros; simp query_size; move: (in_queries_lt Hin1) (in_queries_lt Hin2) => Hlt1 Hlt2; ssromega.
 Qed.
 Next Obligation.
   intros; simp query_size; move: (in_queries_lt Hin1) (in_queries_lt Hin2) => Hlt1 Hlt2; ssromega.
 Qed.
    
 

 Equations is_field_merging_possible schema
           (q1 : @Query Name Vals) (pty1 : Name)
           (q2 : @Query Name Vals) (pty2 : Name) : bool by wf (query_size q1 + query_size q2) :=
   {
     is_field_merging_possible schema (InlineFragment t φ) _ q2 pty2 :=
       all_In φ (fun q Hin => is_field_merging_possible schema q t q2 pty2);
     
     is_field_merging_possible schema q1 pty1 (InlineFragment t φ) _ :=
       all_In φ (fun q Hin => is_field_merging_possible schema q1 pty1 q t);

     is_field_merging_possible schema q1 pty1 q2 pty2
       with lookup_field_type schema pty1 (qname q1 _), lookup_field_type schema pty2 (qname q2 _) :=
       {
       | Some rty1 | Some rty2 :=
         (have_same_response_shape schema q1 pty1 q2 pty2 &&
         (((pty1 == pty2) || ~~(is_object_type schema pty1 && is_object_type schema pty2)) ==>
          [&& (qname q1 _) == (qname q2 _),
           (qargs q1 _) == (qargs q2 _) &
           all_In q1.(qsubquery) (fun q Hin1 =>
                                    all_In q2.(qsubquery) (fun q' Hin2 =>
                                                             is_field_merging_possible schema q rty1 q' rty2))]));
        | _ | _ := false 
        }
      

   }.
 Solve Obligations with intros; simp query_size; move: (in_queries_lt Hin) => Hlt; ssromega.
 Next Obligation.
   intros; simp query_size; move: (in_queries_lt Hin1) (in_queries_lt Hin2) => Hlt1 Hlt2; ssromega.
 Qed.
 Next Obligation.
   intros; simp query_size; move: (in_queries_lt Hin1) (in_queries_lt Hin2) => Hlt1 Hlt2; ssromega.
 Qed.
 Next Obligation.
   intros; simp query_size; move: (in_queries_lt Hin1) (in_queries_lt Hin2) => Hlt1 Hlt2; ssromega.
 Qed.
  Next Obligation.
   intros; simp query_size; move: (in_queries_lt Hin1) (in_queries_lt Hin2) => Hlt1 Hlt2; ssromega.
 Qed.


  
  (** Checks whether a query conforms to a given schema.
      
      Every query (or selection of fields) is set in a given context
      of a particular type, therefore, the conformance is checked
      based on the schema and the current type in context.

   **)

 
  
  Equations query_conforms schema (ty : Name) query : bool :=
    {
      query_conforms schema ty (SingleField fname α)
        with lookup_field_in_type schema ty fname :=
        {
        | Some fld => (is_scalar_type schema fld.(return_type) ||
                      is_enum_type schema fld.(return_type)) &&
                      arguments_conform schema fld.(fargs) α;
        | _ => false
        };

      query_conforms schema ty (LabeledField _ fname α)
        with lookup_field_in_type schema ty fname :=
        {
        | Some fld => (is_scalar_type schema fld.(return_type) ||
                      is_enum_type schema fld.(return_type)) &&
                      arguments_conform schema fld.(fargs) α;
        | _ => false
        };

      query_conforms schema ty (NestedField fname α φ)
        with lookup_field_in_type schema ty fname :=
        {
        | Some fld => [&& (is_object_type schema fld.(return_type) || is_abstract_type schema fld.(return_type)),
                      arguments_conform schema fld.(fargs) α,
                      φ != [::] &
                      queries_conform schema fld.(return_type) φ];
        | _ => false
        };

      query_conforms schema ty (NestedLabeledField _ fname α φ)
        with lookup_field_in_type schema ty fname :=
        {
        | Some fld => [&& (is_object_type schema fld.(return_type) || is_abstract_type schema fld.(return_type)),
                      arguments_conform schema fld.(fargs) α,
                      φ != [::] &
                      queries_conform schema fld.(return_type) φ];
        | _ => false
        };

      query_conforms schema ty (InlineFragment t φ) :=
        [&& [|| is_object_type schema t, is_interface_type schema t | is_union_type schema t], (* This might be a bit redundant *)
         is_fragment_spread_possible schema ty t,
         φ != [::] &
         queries_conform schema t φ]
    }
  where
  queries_conform schema (ty : Name) queries : bool :=
    {
      queries_conform schema ty queries :=  all (query_conforms schema ty) queries &&
                                           map_all (fun q1 q2 => is_field_merging_possible schema q1 ty q2 ty) queries
    }.

  

(*
  Lemma queries_conform_inv schema ty queries :
    queries != [::] ->
    all (query_conforms schema ty) queries ->
    queries_conform schema ty queries.
  Proof. by move=> *; rewrite /queries_conform; apply/andP. Qed.
*)
  
  Lemma nf_conformsP schema type_in_scope f α φ :
    reflect (exists2 fld, lookup_field_in_type schema type_in_scope f = Some fld &
                          [&& (is_object_type schema fld.(return_type) || is_abstract_type schema fld.(return_type)),
                           arguments_conform schema fld.(fargs) α,
                           φ != [::] &
                           queries_conform schema fld.(return_type) φ])
            (query_conforms schema type_in_scope (NestedField f α φ)).
  Proof.
    apply: (iffP idP).
    - simp query_conforms.
      case Hlook : lookup_field_in_type => [fld |] //= H.
      by exists fld.
    - move=> [fld Hlook H].
      by simp query_conforms; rewrite Hlook. 
  Qed.

  Lemma nlf_conformsP schema type_in_scope l f α φ :
    reflect (exists2 fld, lookup_field_in_type schema type_in_scope f = Some fld &
                          [&& (is_object_type schema fld.(return_type) || is_abstract_type schema fld.(return_type)),
                           arguments_conform schema fld.(fargs) α,
                           φ != [::] &
                           queries_conform schema fld.(return_type) φ])
            (query_conforms schema type_in_scope (NestedLabeledField l f α φ)).
  Proof.
    apply: (iffP idP).
    - simp query_conforms.
      case Hlook : lookup_field_in_type => [fld |] // H.
      by exists fld.
    - move=> [fld Hlook H].
      by simp query_conforms; rewrite Hlook. 
  Qed.
             
  Lemma ty_not_scalar_or_enum schema ty tdef:
    lookup_type schema ty = Some tdef ->
    ~~(is_scalar_type schema ty || is_enum_type schema ty) ->
    [\/ is_object_type schema ty, is_interface_type schema ty | is_union_type schema ty].
  Proof. 
    rewrite /negb.
    case: ifP => //.
    rewrite /is_scalar_type /is_enum_type.
    case Hlook: lookup_type => [sm|] //.
    case: sm Hlook => //.
    by move=> o intfs flds Hlook _ _ _; constructor; rewrite is_object_type_equation_1 Hlook.
    by move=> i flds Hlook _ _; constructor; rewrite is_interface_type_equation_1 Hlook.
    by move=> u mbs Hlook _ _; constructor; rewrite is_union_type_equation_1 Hlook.
  Qed.



  Ltac wfquery := case: schema=> sch Hhasty Hwf.
 
  Lemma object_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    is_object_type schema t ->
    ϕ != [::] ->
    queries_conform schema t ϕ -> 
    query_conforms schema type_in_scope (InlineFragment t ϕ) <->
    t = type_in_scope.
  Proof.
    wfquery.
    move=> Hobj'.
    pose H' := Hobj'.
    move/is_object_type_E: H' => [obj [intfs [flds H]]] Hobj Hne Hqsc.
    split.
    - simp query_conforms.
      move/and4P=> [/or3P _ Hspread _ _].
      move: (object_spreads_E _ _ _ Hobj Hspread)=> [||] //.
      * move/has_implementation_is_interface=> Hcontr.
        move: (is_object_type_interfaceN Hobj') => //.
          by rewrite Hcontr.
      * move/in_union => Hcontr.
        move: (is_object_type_unionN Hobj').
          by rewrite Hcontr.
    - move=> Heq; rewrite Heq /=.
      move: Hqsc; rewrite /queries_conform.
      move/andP=> [Hall Hmerge].
      apply/and5P; split=> //.
        by apply/or3P; constructor 1.
        rewrite /is_fragment_spread_possible; simp get_possible_types => /=.
        by rewrite H /= /seqI /=; case: ifP => //=; rewrite inE => /eqP.
      by rewrite Heq in Hall.
      by rewrite -Heq.
  Qed.

  Lemma interface_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    is_interface_type schema t ->
    query_conforms schema type_in_scope (InlineFragment t ϕ) ->
    type_in_scope \in implementation schema t.
  Proof.
    move/is_object_type_wfP=> [intfs [flds Hlook]].
    move/is_interface_type_wfP=> [iflds Hlook'].
    simp query_conforms=> /and5P [_ Hspread _ _ _].
    move: Hspread; rewrite /is_fragment_spread_possible; simp get_possible_types; rewrite Hlook Hlook' /=.
    by rewrite -seq1IC; apply: seq1I_N_nil.
  Qed.

  Lemma union_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    is_union_type schema t ->
    query_conforms schema type_in_scope (InlineFragment t ϕ) ->
    type_in_scope \in union_members schema t.
  Proof.
    funelim (is_object_type schema type_in_scope) => // _.
    funelim (is_union_type schema t) => // _.
    simp query_conforms.
    move/and4P=> [_ Hspread _ _].
    move: Hspread; rewrite /is_fragment_spread_possible; simp get_possible_types; rewrite Heq Heq0 /=.
    rewrite /union_members Heq.
    by rewrite -seq1IC; apply: seq1I_N_nil.
  Qed.

  Lemma abstract_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    ϕ != [::] ->
    queries_conform schema t ϕ ->
    (is_interface_type schema t \/ is_union_type schema t) ->
    reflect (type_in_scope \in implementation schema t \/ type_in_scope \in union_members schema t)
            (query_conforms schema type_in_scope (InlineFragment t ϕ)).
  Proof.
    move=> Hobj Hne Hqsc Htype.
    apply: (iffP idP).
    - case: Htype => [Hint | Hunion].
        by move/(interface_spreads_in_object_scope _ _ _ _ Hobj Hint); left.
      by move/(union_spreads_in_object_scope _ _ _ _ Hobj Hunion); right.
    - move: Hqsc; rewrite /queries_conform => /andP [Hall Hmerge].
      move=> H.      
      simp query_conforms; apply/and5P; split=> //.
      * by apply/or3P; case: Htype; [constructor 2 | constructor 3].
      * move/is_object_type_wfP: Hobj => [intfs [flds Holook]].
        case: H => [Himpl | Hmb]; 
        rewrite /is_fragment_spread_possible; simp get_possible_types.
        move: (has_implementation_is_interface Himpl) => /is_interface_type_wfP [iflds Hilook].
          by rewrite Holook Hilook /= -seq1IC seq1I Himpl.
          
        move: (in_union Hmb) => /is_union_type_wfP [mbs Hulook].
        rewrite Holook Hulook /= -seq1IC seq1I.
        rewrite /union_members Hulook in Hmb.
        by rewrite Hmb.
  Qed.

  Ltac query_conforms := simp query_conforms; try move/and5P; try apply/and5P.




  
  
  Lemma object_spreads_in_interface_scope schema type_in_scope t ϕ :
    is_object_type schema t ->
    is_interface_type schema type_in_scope ->
    ϕ != [::] ->
    queries_conform schema t ϕ ->
    reflect (t \in implementation schema type_in_scope)
            (query_conforms schema type_in_scope (InlineFragment t ϕ)).
  Proof.
    move=> Hobj Hintf Hne Hqsc.
    apply: (iffP idP).
    - query_conforms.
      move=> [_ Hspread _ _].
      move: (object_spreads_E _ _ _ Hobj Hspread) => [Heq | // | /in_union Hun].
      * move: (is_object_type_interfaceN Hobj); rewrite Heq.
        by rewrite /negb Hintf.
      * by move: (is_interface_type_unionN Hintf); rewrite /negb Hun.
    - move=> Himpl.
      query_conforms; split.
      * by apply/or3P; constructor 1.
      * rewrite /is_fragment_spread_possible.
        move/get_possible_types_interfaceE: Hintf => ->.
        move/get_possible_types_objectE: Hobj => ->.
          by rewrite seq1I Himpl.

      all: do ?[by move: Hqsc; rewrite /queries_conform => /andP [H1 H2]].
  Qed.


  Lemma scope_is_obj_or_abstract_for_field schema ty q :
    is_field q ->
    query_conforms schema ty q ->
    is_object_type schema ty \/ is_interface_type schema ty.
  Proof.
    case: q => //= [f α | l f α | f α φ | l f α φ] _; simp query_conforms;
    case Hlook: lookup_field_in_type => [fld|] // _;
    have H: lookup_field_in_type schema ty f by rewrite /isSome Hlook.

    all: by apply: (lookup_field_in_type_is_obj_or_intf H).
  Qed.
  
  Lemma nested_field_is_obj_or_abstract schema ty n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) ->
    is_object_type schema ty \/ is_interface_type schema ty.
  Proof.
    simp query_conforms.
    case Hlook: lookup_field_in_type => [fld|] // _.
    have H: lookup_field_in_type schema ty n by rewrite /isSome Hlook.
      by apply: (lookup_field_in_type_is_obj_or_intf H).
  Qed.

  Lemma scope_is_obj_or_abstract_for_nlf schema ty l f α φ :
    query_conforms schema ty (NestedLabeledField l f α φ) ->
    is_object_type schema ty \/ is_interface_type schema ty.
  Proof.
    simp query_conforms.
    case Hlook: lookup_field_in_type => [fld|] // _.
    have H: lookup_field_in_type schema ty f by rewrite /isSome Hlook.
      by apply: (lookup_field_in_type_is_obj_or_intf H).
  Qed.
  



    
 
  

            
    
  Lemma type_in_scope_N_scalar_enum :
    forall schema type_in_scope ϕ,
    query_conforms schema type_in_scope ϕ ->
    [\/ is_object_type schema type_in_scope,
     is_interface_type schema type_in_scope |
     is_union_type schema type_in_scope].
  Proof.
    move=> schema ty.
    case=> [f α |  l f α |  f α ϕ |  l f α ϕ |  t ϕ]; simp query_conforms.
    all: do ?[case Hlook: lookup_field_in_type => [fld|] //= _;
              have H: lookup_field_in_type schema ty f by rewrite /isSome Hlook].
    all: do ?[by move: (lookup_field_in_type_is_obj_or_intf H) => [Hobj | Hint]; [constructor 1 | constructor 2]].
    
    move/and4P=> [/or3P Hty Hspread Hne _] => //.
    move: Hspread.
    rewrite /is_fragment_spread_possible.
    (*
    case Hlook: lookup_type => [tdef|] //.
    by case: tdef Hlook => //=; do ?[rewrite fset0I //=];
                         [constructor 1; simp is_object_type
                         | constructor 2; simp is_interface_type
                         | constructor 3; simp is_union_type]; rewrite Hlook.
    
    by rewrite fset0I /=.
  Qed.*)
  Admitted.

  Lemma type_in_scope_N_scalar schema type_in_scope φ :
    query_conforms schema type_in_scope φ ->
    is_scalar_type schema type_in_scope = false.
  Admitted.

  Lemma type_in_scope_N_enum schema type_in_scope φ :
    query_conforms schema type_in_scope φ ->
    is_enum_type schema type_in_scope = false.
  Admitted.

  Lemma type_in_scope_N_obj_is_abstract schema type_in_scope φ :
    query_conforms schema type_in_scope φ ->
    is_object_type schema type_in_scope = false ->
    is_abstract_type schema type_in_scope.
  Proof.
    by move/type_in_scope_N_scalar_enum => [-> | Hintf | Hunion ] _ //; rewrite /is_abstract_type; apply/orP; [left | right].
  Qed.
  
  Lemma queries_conform_obj_int_union schema type_in_scope ϕ :
    ϕ != [::] ->
    queries_conform schema type_in_scope ϕ ->
    [\/ is_object_type schema type_in_scope,
     is_interface_type schema type_in_scope |
     is_union_type schema type_in_scope].
  Proof.
    rewrite /queries_conform.
    case: ϕ => //= hd tl _.
    move/andP => [/andP [Hqc Hqsc] _].
    apply (type_in_scope_N_scalar_enum _ _ _ Hqc).
  Qed.

 

 
  
   Lemma nlf_conforms_lookup_some schema ty l n α ϕ :
    query_conforms schema ty (NestedLabeledField l n α ϕ) ->
    exists fld, lookup_field_in_type schema ty n = Some fld.
  Proof. simp query_conforms.
    case Hlook : lookup_field_in_type => [fld'|] //.
    by exists fld'.
  Qed.

  Lemma queries_conform_int_impl schema ty ti qs :
    ty \in implementation schema ti ->
    all (@is_field Name Vals) qs ->
    queries_conform schema ti qs ->       
    queries_conform schema ty qs.
  Proof.
    move=> Himpl Hflds.
    rewrite /queries_conform.
    move/andP=> [/allP Hqsc Hmerge].
    apply/andP; split=> //.
    apply/allP.
    move=> x Hin.
    move: (Hqsc x Hin) => {Hin}.
    case: x => //; [move=> f α | move=> l f α | move=> f α ϕ | move=> l f α ϕ | move=> t ϕ];
    simp query_conforms; do ? rewrite (field_in_interface_in_object schema f Himpl);
     do ? case lookup_field_in_type => //.
    - Admitted. (* Invalid case - all fields *)

  (* Not valid 
  Lemma inline_conforms_to_same_type schema t ϕ :
    [\/ is_object_type schema t, is_interface_type schema t | is_union_type schema t] ->
    queries_conform schema t ϕ ->
    query_conforms schema t (InlineFragment t ϕ).
  Proof.
    move=> Hty Hqsc /=; apply/and3P; split=> //.
    by apply/or3P.
    case: Hty => [Hobj | Hintf | Hunion]; rewrite /is_fragment_spread_possible;
    [rewrite (get_possible_types_objectE Hobj) | rewrite (get_possible_types_interfaceE Hintf)|  ]. apply: fset1I_N_fset0.
      by apply: eq_spreads.
  Qed. *)

  

  Lemma inline_preserves_conformance schema type_in_scope ϕ :
    query_conforms schema type_in_scope ϕ ->
    query_conforms schema type_in_scope (InlineFragment type_in_scope [:: ϕ]).
  Proof.
    simp query_conforms => Hqc.
    apply/and5P; split=> //.
    apply/or3P. apply: (type_in_scope_N_scalar_enum _ _ _ Hqc).
    rewrite /is_fragment_spread_possible; simp get_possible_types.
    
    move: (type_in_scope_N_scalar_enum _ _ _ Hqc) => [Hobj | Hint | Hunion].
    funelim (is_object_type schema type_in_scope) => //.
    Admitted.
 

  


  Lemma nested_conforms_list schema ty n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) -> ϕ != [::].
  Proof.
    simp query_conforms.
    case lookup_field_in_type => // f.
      by move/and4P=> [_ _ Hne _].
  Qed.

   Lemma inline_subqueries_conform schema ty t ϕ :
    query_conforms schema ty (InlineFragment t ϕ) ->
    queries_conform schema t ϕ.
  Proof.
    simp query_conforms.
    move/and5P=> [_ _ Hne H Hmerge].
    by apply/andP. 
  Qed.

  Lemma sf_conforms_in_interface_in_obj schema ti tyo f α :
    tyo \in implementation schema ti ->
            query_conforms schema ti (SingleField f α) ->
            query_conforms schema tyo (SingleField f α).
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
    have: lookup_field_in_type schema ti f = Some fld -> fld \in fields schema ti.
    move: (has_implementation_is_interface Hin) => /is_interface_type_E.
    case=> [i [flds Hilook]].
    
    rewrite /fields /lookup_field_in_type Hilook.
  Admitted.
    

  
  
 
End QueryConformance.


Arguments aux_queries_size [Name Vals].
Arguments have_same_response_shape [Name Vals].
Arguments is_field_merging_possible [Name Vals].
Arguments is_fragment_spread_possible [Name Vals].
Arguments query_conforms [Name Vals].
Arguments queries_conform [Name Vals].