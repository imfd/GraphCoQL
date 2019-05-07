Require Import List.

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord fmap fset.
From Equations Require Import Equations.


Require Import SchemaWellFormedness.
Require Import GraphConformance.
Require Import QueryConformance.
Require Import SchemaAux.
Require Import GraphAux.
Require Import QueryAux.

Require Import Schema.
Require Import Query.
Require Import Graph.


Require Import Ssromega.

Require Import SeqExtra.

Section QuerySemantic.

  Variables N Name Vals : ordType.
  
  
  Ltac case_response r := case: r => [l | l v | l vs | l ρ | l ρs].
    
  Section Aux.    
    Variables (T1 T2 : eqType).
    
    Equations? indexed_map_In (s : seq T1) (f : forall (i : nat) (x : T1), x \in s -> T2) (index : nat) : seq T2 :=
      { 
        indexed_map_In [::] _ _ := [::];
        indexed_map_In (hd :: tl) f i := (f i hd _) :: (indexed_map_In tl (fun i x H => f i x _) i.+1)
      }.
      by apply: mem_head.
        by apply: mem_tail.
    Qed.
      
    (**
       indexed_map : (s : seq T1) -> (nat -> x : T1 -> x ∈ s -> T2) -> seq T2
       Applies the function to every element in the given list.
       It is a regular map function but it allows to use the information
       about the index of the element where the function is being applied.
       The function also requires a proof that the element where it's being
       applied belongs to the list. This is mainly to be able to prove some
       obligations afterwards.
     **)
    Definition indexed_map (s : list T1) (f : forall (i : nat) (x : T1), x \in s -> T2)  : list T2 :=
        indexed_map_In s f 0
    .
    

    Lemma indexed_map_In_n (s : list T1) (f : T1 -> T2) :
      forall n1 n2,
        indexed_map_In s (fun _ x _ => f x) n1 = indexed_map_In s (fun _ x _ => f x) n2.
    Proof.
      elim: s => //= hd tl IH n1 n2; simp indexed_map_In.
      congr cons.
      apply: IH.
    Qed.
    
    Lemma indexed_map_eq_map (s : list T1) (f : T1 -> T2) :
      indexed_map s (fun _ x _ => f x) = [seq f x | x <- s].
    Proof.
      elim: s => //= hd tl IH.
      rewrite /indexed_map; simp indexed_map_In.
      congr cons.
      rewrite -IH /=.
      rewrite /indexed_map.
      apply: indexed_map_In_n.
    Qed.

       
    Variables (T : Type) (dflt : T).


    (**
       get_nth : T -> seq T -> nat -> T
       Gets the nth' element from a list or a default value if the index
       is out of bounds.
      
       Same as seq.nth from mathcomp but using Equations. 
       
     **)
    Equations get_nth (s : seq.seq T) (i : nat) : T :=
      get_nth nil _ := dflt;
      get_nth (cons hd tl) 0 := hd; 
      get_nth (cons hd tl) (S n) := get_nth tl n.


    
  
    Lemma In_e_sumn {A : Type} (elt : A) (f : A -> nat) (l : list A) :
      In elt l -> f elt <= sumn [seq (f x) | x <- l].
    Proof.
      elim: l => [// | hd l' IH].
      move=> [-> | Hnin] /=.
        by ssromega.
      by move: (IH Hnin) => *; ssromega.
    Qed.

    Lemma In_r_size (r : seq.seq (@ResponseObject Name Vals)) rs : In r rs -> responses_size r <= sumn [seq (responses_size r') | r' <- rs].
    Proof. by apply: In_e_sumn. Qed.

    
   (* Lemma In_r_size' (r : (@Result Name Vals)) rs0 : In r rs0 -> result_size r <= results_size rs0.
    Proof. elim: rs0 => [//| x rs' IH].
      move=> [-> | Hin].
      by simpl; ssromega.
      by move/IH: Hin => * /=; ssromega.
    Qed. *)
    
    Lemma le_lt_trans n m p : n < m -> m <= p -> n < p.
    Proof. by intros; ssromega. Qed.

    Lemma sum_lt a b c d : a < c -> b <= d -> (a + b < c + d)%coq_nat.
    Proof. intros. ssromega. Qed.

    Lemma sum_lt' a b c d : a <= c -> b <= d -> a + b <= c + d.
    Proof. by move=> *; ssromega. Qed.
    
    Lemma two_times_Sn n : 2 * n.+1 = 2 * n + 2.
    Proof.  by []. Qed.

    Lemma leq_addr m n p : m <= n -> m <= n + p.
    Proof. elim: m => [//| m IH].
      apply: ltn_addr.
    Qed.
    
  End Aux.

  Arguments indexed_map_In [T1 T2].
  Arguments indexed_map [T1 T2].
  Arguments indexed_map  [T1 T2].
  Arguments get_nth [T].
  
  Section Filters.


    Section Indexed_Beta.

      (**
         indexed_β_filter : seq ResponseObject -> ResponseObject -> nat -> seq ResponseObject 
         Traverses the list and extracts the i-th element from a response, whenever it 
         corresponds to a NestedListResult and it matches the filter response.
         This differs slightly from the definition given in Jorge and Olaf [WWW'18],
         where responses not matching would return an ϵ result (empty string). Here,
         an empty list is returned, which gets deleted when the flattening occurs.
       **)

      Equations indexed_β_filter (filter :  Name) (responses : seq (@ResponseObject Name Vals))  (index : nat) : seq (@ResponseObject Name Vals) :=
        {
          indexed_β_filter _ [::] _ := [::];
          indexed_β_filter filter ((NestedListResult l rs) :: tl) index
            with l == filter :=
              {
              | true := (get_nth [::] rs index) ++ (indexed_β_filter filter tl index);
              | false := (indexed_β_filter filter tl index)
              };
          indexed_β_filter filter (_ :: tl) index := (indexed_β_filter filter tl index)
        }.
    
    

      (** Auxiliary lemmas **)
      
    

      Lemma get_nth_lt (l : seq (seq (@ResponseObject Name Vals))) i :
        responses_size (get_nth [::] l i) <= responses_size' l.
      Proof.
        by funelim (get_nth [::] l i) => //=; rewrite -/(responses_size t); ssromega.
      Qed.
      
      Lemma indexed_β_size_reduced (flt : Name) (lst : seq ResponseObject) (i : nat) :
        
        responses_size (indexed_β_filter flt lst i) <= responses_size lst.
      Proof.
        apply_funelim (indexed_β_filter flt lst i) => //=.
        all: do ?[by intros; simp response_size; ssromega].

        move=> filter l.
        intros; rewrite responses_size_app; simp response_size.
          by move: (get_nth_lt l2 index) => Hlt; ssromega.
      Qed.
      
      

      
      Lemma indexed_β_nil flt rs i :
        all (fun r => r.(rname) != flt) rs ->
        indexed_β_filter flt rs i = [::].
      Proof.
        funelim (indexed_β_filter flt rs i) => //= /andP [Hneq Hall].
        all: do ? by apply: H.
        by rewrite Heq in Hneq.
      Qed.

    
      Lemma indexed_β_cat flt i s1 s2 :
        indexed_β_filter flt (s1 ++ s2) i =
        indexed_β_filter flt s1 i ++ indexed_β_filter flt s2 i.
      Proof.
        elim: s1 => //= hd tl IH.
        case: hd => //= l ρs; simp indexed_β_filter.
        case: eqP => /= _; last by apply: IH.
        by rewrite -catA IH.
      Qed.
      
    End Indexed_Beta.

    Section Beta.
     

      Equations βᶿ : Name -> seq (@ResponseObject Name Vals) -> seq (@ResponseObject Name Vals) -> seq (@ResponseObject Name Vals)
      :=
        {
          βᶿ _ ρ [::] := ρ;
          βᶿ l ρ (NestedResult l' σ :: rs)
            with l == l' :=
            {
                  | true := βᶿ l (ρ ++ σ) rs;
                  | _ := βᶿ l ρ rs
            };
          βᶿ l ρ (r :: rs) := βᶿ l ρ rs
        }.


      Lemma βᶿ_foldl l ρ rs :
        βᶿ l ρ rs = foldl (fun acc r => match r with
                                     | NestedResult l' σ =>
                                       if l == l' then
                                         acc ++ σ
                                       else
                                         acc
                                     | _ => acc
                                     end) ρ rs.
      Proof.
        funelim (βᶿ l ρ rs) => //=;
        by rewrite Heq; apply: H.
      Qed.

      Lemma βᶿ_all_neq l ρ rs :
        all (fun r => r.(rname) != l) rs ->
        βᶿ l ρ rs = ρ.
      Proof.
        funelim (βᶿ l ρ rs) => //= /andP [Hneq Hall]; do ? by apply: H.
        by move/negbTE in Hneq; rewrite eq_sym Hneq in Heq.
      Qed.

      Lemma βᶿ_preserves_non_redundancy l ρ rs :
        are_non_redundant__ρ ρ ->
        are_non_redundant__ρ (βᶿ l ρ rs).
      Proof.
        funelim (βᶿ l ρ rs) => //=.
      Abort.
        
      
      Equations β__Laux :  seq (seq (@ResponseObject Name Vals)) ->  seq (seq (@ResponseObject Name Vals)) ->  seq (seq (@ResponseObject Name Vals)) :=
        {
          β__Laux [::] _ := [::];
          β__Laux ρs [::] := ρs;
          β__Laux (ρ1 :: ρs) (σ1 :: σs) := (ρ1 ++ σ1) :: (β__Laux ρs σs)
        }.

      Lemma β__Laux_responses_size_leq ρs σs :
        responses_size' (β__Laux ρs σs) <= responses_size' ρs + responses_size' σs.
      Proof.
        apply_funelim (β__Laux ρs σs) => //; do ?[by intros; ssromega].
        intros; rewrite !responses_size'_equation_2.
        by rewrite responses_size_app; ssromega.
      Qed.
        
      Equations β__L : Name ->  seq (seq (@ResponseObject Name Vals)) -> seq (@ResponseObject Name Vals) -> seq (seq (@ResponseObject Name Vals)) :=
        {
          β__L _ ρs [::] := ρs;
          β__L l ρs (NestedListResult l' σs :: rs)
            with l == l' :=
            {
            | true := β__L l (β__Laux ρs σs) rs;
            | _ := β__L l ρs rs
            };
          β__L l ρs (r :: rs) := β__L l ρs rs
        }.      

      Lemma β__L_responses_size_leq ρ l ρs rs :
        ρ \in β__L l ρs rs ->
              responses_size ρ <= responses_size' ρs + responses_size rs.
      Proof.
        funelim (β__L l ρs rs) => //= Hin; simp response_size.
        - by move: (in_responses'_leq Hin) => Hleq; ssromega.
        - all: do ?[by move: (H ρ Hin) => Hleq; ssromega].
        - move: (H ρ Hin) => Hleq.
          by move: (β__Laux_responses_size_leq l l3) => Hleq2; ssromega.
      Qed.

      Lemma β__L_all_neq l ρs rs :
        all (fun r => r.(rname) != l) rs ->
        β__L l ρs rs = ρs.
      Proof.
        funelim (β__L l ρs rs) => //= /andP [Hneq Hall]; do ? by apply: H.
        by move/negbTE in Hneq; rewrite eq_sym Hneq in Heq.
      Qed.
      
      Lemma β__Laux_fold ρs σs :
        β__Laux ρs σs = (foldr (fun r acc => match acc, r with
                                        | ([::], acc), _ => ([::], r :: acc)
                                        | (σ1 :: σs, acc), r => (σs, (r ++ σ1) :: acc)
                                        end) (σs, [::]) ρs).2.
      Proof.
        move: {2}(size _) (leqnn (size ρs)) => n.
        elim: n ρs σs => //= [| n IH] ρs σs.
          by rewrite leqn0 => /eqP-/size0nil ->.
        - case: ρs => //= ρ1 ρs Hlt.
      Abort.
      
        
      Lemma βᶿ_responses_size_leq l ρ rs :
        responses_size (βᶿ l ρ rs) <= responses_size ρ + responses_size rs.
      Proof.
        funelim (βᶿ l ρ rs) => //=; simp response_size; do ? ssromega.
        move: H; rewrite responses_size_app => H; ssromega.
      Qed.

      Obligation Tactic := intros; simp response_size; do ? ssromega.
      Equations? β__ρ  (rs : seq (@ResponseObject Name Vals)) : seq (@ResponseObject Name Vals) by wf (responses_size rs) :=
        {
          β__ρ [::] := [::];
          β__ρ (NestedResult l ρ :: rs) := (NestedResult l (β__ρ (βᶿ l ρ rs))) :: β__ρ rs;
          β__ρ (NestedListResult l ρs :: rs) := (NestedListResult l (map_in (β__L l ρs rs) (fun ρ Hin => β__ρ ρ))) :: β__ρ rs;
          β__ρ (r :: rs) := r :: β__ρ rs
        }.
        by move: (βᶿ_responses_size_leq l ρ rs) => Hleq; ssromega.
        by move: (β__L_responses_size_leq ρ l ρs rs Hin) => Hleq; ssromega.
      Qed.
        

      
      

       (**
         β_filter : ResponseObject -> seq ResponseObject -> seq ResponseObject
         Traverses the list of response objects and extracts the nested result from an object,
         whenever it matches the filter response given as argument.
         
         This differs slightly from the definition given in Jorge and Olaf [WWW'18],
         where responses not matching would return an ϵ result (empty string). Here, 
         an empty list is returned (using β) but it gets deleted when it concatenates
         to the remaining list.
        **)
      
     
    End Beta.

    Section Gamma.

  
      (**
         γ_filter : ResponseObject -> seq ResponseObject -> seq ResponseObject 
         Filters out response objects that are partially equal to the filter
         response object given as argument.
         This differs slightly from the definition given in Jorge and Olaf [WWW'18],
         where matching responses would return an ϵ result (empty string) but here 
         these are deleted.
       **)

      Equations γ__ρ : @ResponseObject Name Vals -> @ResponseObject Name Vals :=
        {
          γ__ρ (NestedResult l ρ) := NestedResult l (γ__ρs ρ);
          γ__ρ (NestedListResult l ρs) := NestedListResult l (γ__ρs' ρs);
          γ__ρ ρ := ρ
        }
      where
      γ__ρs : seq (@ResponseObject Name Vals) -> seq (@ResponseObject Name Vals) :=
        {
          γ__ρs [::] := [::];
          γ__ρs (ρ1 :: ρs) := γ__ρ ρ1 :: [seq ρ <- (γ__ρs ρs) | ρ.(rname) != ρ1.(rname)]
        }
      where
      γ__ρs' : seq (seq (@ResponseObject Name Vals)) -> seq (seq (@ResponseObject Name Vals)) :=
        {
          γ__ρs' [::] := [::];
          γ__ρs' (ρs1 :: ρs) := γ__ρs ρs1 :: γ__ρs' ρs
        }.

      Lemma all_neq_filter_eq l (s : seq (@ResponseObject Name Vals)) :
        all (fun r => r.(rname) != l) s ->
        [seq r <- s | r.(rname) != l] = s.
      Proof.
        elim: s => //= hd tl IH /andP [-> Hall].
        by rewrite IH.
      Qed.
      
    End Gamma.
    
  End Filters.


  Lemma in_responses_size (r : seq (@ResponseObject Name Vals)) rs : In r rs -> responses_size r <= responses_size' rs.
  Proof.
    elim: rs => [//| r' rs' IH] Hin /=; rewrite -/(responses_size _).
    move: (in_inv Hin) => [-> | Htl] //.
      by ssromega.
      by move: (IH Htl) => Hleq; ssromega.
  Qed.



  Definition collect := γ__ρs \o β__ρ.

  
  Lemma collect_non_redundant_eq ρ :
    are_non_redundant__ρ ρ ->
    collect ρ = ρ.
  Proof.
    rewrite /collect /=.
    apply_funelim (β__ρ ρ) => // [l | l v | l vs | l σ | l σs] ρs.
    all: do ?[move=> IH /= /and3P [Hall Hnr Hnrs];
                by rewrite IH //= all_neq_filter_eq; simp γ__ρ].
    - move=> IH1 IH2 /= /and3P [Hall Hnr Hnrs].
      simp γ__ρ.
      rewrite βᶿ_all_neq // in IH1 *.
      by rewrite all_neq_filter_eq IH2 ?IH1.
    - move=> IH1 IH2 /= /and3P [Hall Hnr Hnrs].
      rewrite map_in_eq.
      simp γ__ρ.
      rewrite IH2 // all_neq_filter_eq //.
      rewrite β__L_all_neq // in IH1 *.
      
    elim: ρ => //= r rs IH /and3P [Hall Hnr Hnrs].
    rewrite /collect /=.
    
    apply_funelim (collect ρ) => //= [l | l v | l vs | l χ | l ρs] tl IH.
    all: do ?[move/and3P => [Hall Hnr Hnrs]].
    all: do ?congr cons.
    all: do ?[by rewrite IH; [apply: γ_filter_neq_preserves_list | apply: γ_filter_preserves_non_redundancy]].
    
    - move=> IH' /and3P [Hall Hnr Hnrs].
      rewrite IH ?β_filter_nil // ?cats0.
      by congr cons; rewrite IH'; [apply: γ_filter_neq_preserves_list | apply: γ_filter_preserves_non_redundancy].
        by simp is_non_redundant__ρ; case=> [Hnr Hnrs].

    - move=> IH' /and3P [Hall Hnr Hnrs].
      congr cons; last first.
      * by rewrite IH'; [apply: γ_filter_neq_preserves_list | apply: γ_filter_preserves_non_redundancy].
      * congr NestedListResult.
        rewrite /indexed_map => /=.
        rewrite indexed_map_In_β_nil //.
        rewrite -/(indexed_map ρs _) indexed_map_eq_map.
  Admitted.

  
  Lemma collect_preserves_non_redundancy ρs :
    are_non_redundant__ρ ρs ->
    are_non_redundant__ρ (collect ρs).
  Proof.
      by move=> Hnr; rewrite collect_non_redundant_eq.
  Qed.
    

  Lemma collect_all_not_eq flt ρ :
    all (fun r => r.(rname) != flt) ρ ->
    collect (γ_filter flt ρ) = collect ρ.
  Proof.
    by move=> Hall; rewrite γ_filter_neq_preserves_list //.
  Qed.



                  
  Lemma collect_preserves_all_not_eq flt ρ :
    all (fun r => r.(rname) != flt) ρ ->
    all (fun r => r.(rname) != flt) (collect ρ).
  Proof.
    funelim (collect ρ) => //= /andP [Hneq Hall]; apply/andP; split=> //.
    
    all: do ?[by apply: H; move/allP: Hall => Hall; apply/allP => x; rewrite mem_filter => /andP [_ Hin]; apply: Hall].
    
    all: do ?[by apply: H0; move/allP: Hall => Hall; apply/allP => x; rewrite mem_filter => /andP [_ Hin]; apply: Hall].
  Qed.
  
  Lemma in_collect_γ r flt ρ :
    r \in collect (γ_filter flt ρ) ->
          r.(rname) != flt.
  Proof.
  Admitted.
  
  Lemma collect_are_non_redundant ρs :
    are_non_redundant__ρ (collect ρs).
  Proof.
    apply_funelim (collect ρs) => //= [l | l v | l vs | l ρ | l χ] tl IH.

    all: do ?[apply/and3P; split=> //=; by apply: collect_preserves_all_not_eq; apply: γ_filter_all].

    - move=> IHtl; apply/and3P; split=> //=.
      by apply: collect_preserves_all_not_eq; apply: γ_filter_all.

    - move=> Hnr; apply/and3P; split=> //=.
      * by apply: collect_preserves_all_not_eq; apply: γ_filter_all.
      * simp is_non_redundant__ρ.
  Admitted.
    
    
  Hint Resolve collect_are_non_redundant.
  Lemma collect_collect_same (r : seq (@ResponseObject Name Vals)) :
    collect r = collect (collect r).
  Proof.
    rewrite [collect (collect r)]collect_non_redundant_eq //.
  Qed.
 

  Lemma collect_preserves_wf rs :
    wf_responses rs ->
    wf_responses (collect rs).
  Proof.
    by intros; apply: non_redundant_are_wf.
  Qed.

  Lemma collect_preserves_compatible_shapes r rs :
    all (have_compatible_shapes r) rs ->
    all (have_compatible_shapes r) (collect rs).
  Proof.
    apply_funelim (collect rs) => //= [l | l v | l vs | l ρ | l ρs] tl IH.

    all: do ?[by move/andP=> [Hcomp Hall]; apply/andP; split=> //; apply: IH; apply: filter_preserves_pred].


    move=> IHtl /andP [Hcomp Hall].
    apply/andP; split; last by apply: IHtl; apply: filter_preserves_pred.
    case: r Hcomp Hall IH IHtl => [l' | l' v' | l' vs' | l' χ | l' χ]; simp have_compatible_shapes.
    case: eqP => //=; rewrite ?all_In_eq_all.
    Admitted.
   (* move: Hcomp; simp have_compatible_shapes; rewrite all_In_eq_all.
    case: eqP => //= Heq Hcomp; last by apply: H0; apply: filter_preserves_pred.
    apply/andP; split; last by apply: H0; apply: filter_preserves_pred.
    rewrite all_In_eq_all.
    apply/allP => x Hin; rewrite all_In_eq_all.
    move: 
    

    
    
    simp have_compatible_shapes. rewrite all_In_eq_all.
    case: eqP => //= Heq.
    apply/andP; split=> //.
    apply/allP=> x Hin. rewrite all_In_eq_all.
    move: x Hin; apply/allP.

    apply/andP; split=> //.
    
    
    all: do ?[by apply/andP; split=> //; apply: H0; apply: filter_preserves_pred].
    *)

    
  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type graph : @graphQLGraph Name Vals.
  Implicit Type u : @node Name Vals.
  Implicit Type query : @Query Name Vals.

  
  Equations eval schema graph u query : seq.seq (@ResponseObject Name Vals) :=
    {
      eval schema graph u (SingleField name args)
        with u.(fields) (Field name args) :=
        {
        | Some (inl value) =>  [:: SingleResult name value];
        | Some (inr values) => [:: ListResult name values];
        | _ => [:: Null name]
        };
      
      eval schema graph u (LabeledField label name args)
        with u.(fields) (Field name args) :=
        {
        | Some (inl value) => [:: SingleResult label value];
        | Some (inr values) => [:: ListResult label values];
        | _ => [:: Null label]
        };
      
      eval schema graph u (NestedField name args ϕ) :=
        let target_nodes := neighbours_with_field graph u (Field name args) in
        match lookup_field_type schema u.(type) name with
        | Some (ListType _) =>
          [:: NestedListResult name [seq (eval_queries schema graph v ϕ) | v <- target_nodes]]
            
        | Some (NT _) =>
          match ohead target_nodes with
          | Some v => [:: NestedResult name (eval_queries schema graph v ϕ)]
          | _ =>  [:: Null name]
          end
        | _ => [:: Null name]         (* If the field ∉ fields(u) then it's null, right? *)
        end;
                                  
      eval schema graph u (NestedLabeledField label name args ϕ) :=
        let target_nodes := neighbours_with_field graph u (Field name args) in
        match lookup_field_type schema u.(type) name with
        | Some (ListType _) =>
          [:: NestedListResult label [seq (eval_queries schema graph v ϕ) | v <- target_nodes]]
        | Some (NT _) =>
          match ohead target_nodes with
          | Some v => [:: NestedResult label (eval_queries schema graph v ϕ)]
          | _ => [:: Null label]
          end
        | _ => [:: Null label]
        end;
      
      eval schema graph u (InlineFragment t ϕ)
        with u.(type) == t :=
        {
        | true  := eval_queries schema graph u ϕ;
        | _ with u.(type) \in implementation schema t :=
            {
            | true := eval_queries schema graph u ϕ;
            | _ with u.(type) \in union_members schema t :=
                {
                | true := eval_queries schema graph u ϕ;
                | _ := [::]
                }
            }
        }
    }
  where
  eval_queries schema graph u (queries : seq (@Query Name Vals)) : seq (@ResponseObject Name Vals) :=
    {
      eval_queries _ _ _ [::] := [::];
      eval_queries schema graph u (query :: tl) :=  collect ((eval schema graph u query) ++ (eval_queries schema graph u tl))
    }.

  Lemma eval_query_same_response_name schema g u q (H : forall t φ, q <> InlineFragment t φ) :
    forall r, r \in (eval schema g u q) ->
               r.(rname) = (qresponse_name q H).
  Proof.
    case: q H => //= [f α | l f α | f α φ | l f α φ | t φ] H r; simp eval.
    - case: (u.(fields) _) => //=.
      by case=> [v | vs] => //=; rewrite mem_seq1 => /eqP -> /=; simp qresponse_name.
        by rewrite mem_seq1 => /eqP ->; simp qresponse_name.
    - case: (u.(fields) _) => //=.
      by case=> [v | vs] => //=; rewrite mem_seq1 => /eqP -> /=; simp qresponse_name.
      by rewrite mem_seq1 => /eqP ->; simp qresponse_name.
    - case lookup_field_type => //= [rty|].
      case: rty => rty.
      by case: ohead => [v |]; rewrite mem_seq1 => /eqP ->; simp qresponse_name.
      by rewrite mem_seq1 => /eqP ->; simp qresponse_name.
      by rewrite mem_seq1 => /eqP ->; simp qresponse_name.
    - case lookup_field_type => //= [rty|].
      case: rty => rty.
      by case: ohead => [v |]; rewrite mem_seq1 => /eqP ->; simp qresponse_name.
      by rewrite mem_seq1 => /eqP ->; simp qresponse_name.
        by rewrite mem_seq1 => /eqP ->; simp qresponse_name.

    - by move: (H t φ).
  Qed.

  Lemma eval_queries_diff_response_name schema g u q1 q2
        (H1 : forall t φ, q1 <> InlineFragment t φ)
        (H2 : forall t φ, q2 <> InlineFragment t φ):
    (qresponse_name q1 H1) != (qresponse_name q2 H2) ->
    forall r1, r1 \in (eval schema g u q1) ->
    forall r2, r2 \in (eval schema g u q2) ->     
                 r1.(rname) != r2.(rname).
    move=> Hneq r Hin r2 Hin2.
    move: (eval_query_same_response_name _ _ _ q1 H1 r Hin) (eval_query_same_response_name _ _ _ q2 H2 r2 Hin2) => Hreq1 Hreq2.
    case: q1 H1 Hneq Hreq1 Hin => //= [f α | l f α | f α φ | l f α φ | t φ] H1; simp qresponse_name => Hneq ->; last by move: (H1 t φ).
    
    all: do ?[by case: q2 H2 Hneq Hreq2 Hin2 => //= [f' α' | l' f' α' | f' α' χ | l' f' α' χ | t' χ] H2; simp qresponse_name => Hneq -> _ _].
  Qed.
  
  
  Lemma eval_non_redundant :
    forall schema g u φ,
    are_non_redundant__ρ (eval schema g u φ).
  Proof.
    apply (eval_elim
             (fun schema g u q res =>
                are_non_redundant__ρ res)
             (fun schema g u qs res =>
                are_non_redundant__ρ res)) => //=.
    - intros. case Hlook: lookup_field_type => [rty|] //.
      case: rty Hlook => //= ty Hlook.
      case: ohead => [fld|] //=; rewrite andbT; simp is_non_redundant__ρ; apply: H => //; exact: (NT ty).
      rewrite andbT; simp is_non_redundant__ρ.
      apply/allP => x /mapP [r Hin ->]; apply: H; exact: ty.

     - intros. case Hlook: lookup_field_type => [rty|] //.
      case: rty Hlook => //= ty Hlook.
      case: ohead => [fld|] //=; rewrite andbT; simp is_non_redundant__ρ; apply: H => //; exact: (NT ty).
      rewrite andbT; simp is_non_redundant__ρ.
      apply/allP => x /mapP [r Hin ->]; apply: H; exact: ty.
  Qed.

  Lemma eval_queries_are_non_redundant schema g u φ :
    are_non_redundant__ρ (eval_queries schema g u φ).
  Proof.
      by case: φ => //= hd tl. 
  Qed.

  Hint Resolve eval_non_redundant eval_queries_are_non_redundant.

  
  Lemma eval_queries_response_are_wf schema g u qs :
    wf_responses (eval_queries schema g u qs).
  Proof.
    by apply: non_redundant_are_wf.
  Qed.

  Lemma eval_query_responses_are_wf schema g u q :
    wf_responses (eval schema g u q).
  Proof.
      by apply: non_redundant_are_wf.
  Qed.

  Lemma wf_responses_cat_same (s : seq (@ResponseObject Name Vals)) :
    wf_responses s -> wf_responses (s ++ s).
  Proof.
    elim: s => //= hd tl IH.
    
  Admitted.


    
  Lemma qweqw schema g u ty q1 q2 :
    is_field_merging_possible schema q1 ty q2 ty ->
    all (fun r1 => all (fun r2 => have_compatible_shapes r1 r2) (eval schema g u q2)) (eval schema g u q1).
  Proof.
    case: q1 => [f α | l f α | f α φ | l f α φ | t φ].
    case: q2 => [f' α' | l' f' α' | f' α' χ | l' f' α' χ | t' χ]; simp is_field_merging_possible; simp qname.
    case Hlook1: lookup_field_type => [rty1|] //=; simp qresponse_name;
                                       case Hlook2: lookup_field_type => [rty2|] //=; simp qargs; simp qresponse_name.
    
  Admitted.
 
  Lemma asdfasfd schema g u ty q s :
    all ((is_field_merging_possible schema q ty) ^~ ty) s ->
    all (fun r1 => all (fun r2 => have_compatible_shapes r1 r2) (eval_queries schema g u s)) (eval schema g u q).
  Proof.
    elim: s => // [| hd tl IH].
    - by move=> _; apply/allP.
    - move=> /= /andP [Hmerge Hall].
      apply/allP => r Hin.
      apply/allP => r2 Hin2.
      
  Admitted.
      
  Lemma eval_two_merging_queries_are_wf schema g u ty q1 q2 :
    is_field_merging_possible schema q1 ty q2 ty ->
    wf_responses ((eval schema g u q1) ++ (eval schema g u q2)).
  Proof.
    case: q1 => [f α | l f α | f α φ | l f α φ | t φ].
    case: q2 => [f' α' | l' f' α' | f' α' χ | l' f' α' χ | t' χ]; simp is_field_merging_possible; simp qname.

    all: do ?[case Hlook1: lookup_field_type => [rty1|] //=; simp qresponse_name;
              case Hlook2: lookup_field_type => [rty2|] //=; simp qargs; simp qresponse_name;
              case Hfeq: (f == f') => //= /andP [Hshape]; rewrite ?eqxx /=].
    
    all: do ?[by move/andP=> [/eqP Hargs Hall]; move/eqP in Hfeq; rewrite Hfeq Hargs wf_responses_cat_same //;
              apply: eval_query_responses_are_wf].
    all: do ?[move=> _;
              rewrite wf_responses_cat_neq;
              [by apply/andP; split=> //; apply: eval_query_responses_are_wf 
              | move/negbT in Hfeq;
                have Hninl1 : forall t φ, (SingleField f α) <> InlineFragment t φ by [];
               have Hninl2 : forall t φ, (SingleField f' α') <> InlineFragment t φ by [];
               apply/allP => r1 Hin1; apply/allP=> r2 Hin2;
               move: (eval_queries_diff_response_name schema g u (SingleField f α) (SingleField f' α') Hninl1 Hninl2 Hfeq);
                 by move/(_ r1 Hin1 r2 Hin2) => H; rewrite /negb ifN_eqC]].

    case Hleq: (f == l') => //=.
    move/andP=> [/eqP Hargs Hall].
    move/eqP in Hfeq; rewrite Hfeq Hargs.
    simp eval. case : (u.(fields) _) => //=.
    case=> //=.

    move=> _; rewrite wf_responses_cat_neq;
             [by apply/andP; split=> //; apply: eval_query_responses_are_wf 
              | move/negbT in Hleq;
                have Hninl1 : forall t φ, (SingleField f α) <> InlineFragment t φ by [];
               have Hninl2 : forall t φ, (LabeledField l' f' α') <> InlineFragment t φ by [];
               apply/allP => r1 Hin1; apply/allP=> r2 Hin2;
               move: (eval_queries_diff_response_name schema g u (SingleField f α) (LabeledField l' f' α') Hninl1 Hninl2 Hleq);
                 by move/(_ r1 Hin1 r2 Hin2) => H; rewrite /negb ifN_eqC].
    
    all: do ?[rewrite implybF].

    admit.
    move: Hshape; simp have_compatible_response_shapes; simp qresponse_name.
    rewrite Hfeq /= Hlook1 Hlook2.
    (* Missing info on query conformance *)
  Admitted.

  Lemma eval_merging_queries_are_wf schema g u ty q1 qs :
    all ((is_field_merging_possible schema q1 ty) ^~ ty) qs ->
    wf_responses ((eval schema g u q1) ++ (eval_queries schema g u qs)).
  Proof.
    elim: qs => //= [_| hd tl IH].
    - rewrite cats0; apply: eval_query_responses_are_wf.
    - move/andP=> [Hmerge Hall].
  Abort.
    
  Lemma eval_collect_same :
    forall schema graph u query,
      eval schema graph u query = collect (eval schema graph u query).
  Proof.
    by intros; rewrite collect_non_redundant_eq.
  Qed.
 


  Lemma eval_queries_collect_same schema graph u qs :
    eval_queries schema graph u qs = collect (eval_queries schema graph u qs).
  Proof.
    by rewrite collect_non_redundant_eq //. 
  Qed.
  
  Lemma eval_same_query_in_list schema graph u query :
    eval schema graph u query = eval_queries schema graph u [:: query].
  Proof.
    rewrite eval_queries_equation_2 /= cats0.
      by apply: eval_collect_same.
  Qed.
  
  Lemma eval_query_inline schema (g : conformedGraph schema) qs :
    eval schema g g.(root) (InlineFragment schema.(query_type) qs) = eval_queries schema g g.(root) qs.
  Proof.
    simp eval.
    move: (root_query_type  g) => -> /=.
    by case: eqP.
  Qed.

  
  Lemma γ_collect_γ :
    forall n flt s,
      size s <= n ->
      γ_filter flt (collect (γ_filter flt s)) = collect (γ_filter flt s).
  Proof.
    elim=> //= [| n IH] flt s.
    - by rewrite leqn0 => /eqP-/size0nil -> /=; simp collect.
    - move=> Hlt.
      case: s Hlt => //= hd tl Hlt; case: ifP => //=;
      case: hd => /= [l | l v | l vs | l ρs | l ρs] Hneq; simp collect => //=; rewrite ?Hneq.
      all: do ?[rewrite γ_filter_swap; rewrite (IH flt (γ_filter l _)) //].
      all: do ?[move: (γ_size_le l tl) => Hlts; ssromega].
  Qed.      
      


  Lemma response_size_eq_or_gtn_3 (r : @ResponseObject Name Vals) :
    3 <= response_size r.
  Proof.
      by case: r.
  Qed.

      
  Lemma indexed_map_In_β s l lst s2:
    forall i,
    (indexed_map_In s
       (fun i r _ =>
        collect
          (r ++ indexed_β_filter l (collect (γ_filter l lst) ++ s2) i)) i) =
    (indexed_map_In s
       (fun i r _ =>
          collect (r ++ indexed_β_filter l s2 i)) i).
  Proof.
    elim: s => //= hd tl IH i.
    simp indexed_map_In.
    rewrite indexed_β_cat.
    rewrite (indexed_β_nil l _ _); last first.
      by apply: collect_preserves_all_not_eq; apply: γ_filter_all.
    rewrite cat0s; congr cons.
    apply: IH.
  Qed.

  Lemma indexed_map_In_nested_map ρs l lst s2 :
    forall n,
    indexed_map_In
      (indexed_map_In ρs
         (fun i r _ =>
          collect (r ++ indexed_β_filter l lst i)) n)
      (fun i r _ =>
         collect (r ++ indexed_β_filter l s2 i)) n =
    indexed_map_In ρs
      (fun i r _ =>
         collect (collect (r ++ indexed_β_filter l lst i) ++ indexed_β_filter l s2 i)) n.
  Proof.
    elim: ρs => //= hd tl IH n.
    simp indexed_map_In.
    congr cons.
    apply: IH.
  Qed.
         
  Lemma collect_collect_2_cat :
    forall n s1 s2,
      n >= responses_size s1 ->
      collect (collect s1 ++ s2) = collect (s1 ++ s2).
  Proof.
    
    elim=> // [| n IH].
    - case=> //= r tl s2.
      rewrite leqn0 addn_eq0 => /andP [/eqP Hcontr _].
      move: (response_size_n_0 r); rewrite lt0n => /eqP.
        by rewrite Hcontr.
        
    - case => //= hd tl s2 Hlt.
      case: hd Hlt => [l | l v | l vs | l ρ | l ρs].

      
      all: do ?[simp response_size => /= Hlt; simp collect;
                rewrite -/cat !γ_filter_cat /= (γ_collect_γ (size tl) l tl) // IH //;
                move: (γ_responses_size_reduced l tl) => Hltg; ssromega].

      * move=> Hlt; simp collect; rewrite -/cat.
        rewrite β_filter_cat.
        rewrite (β_filter_nil l (collect _)) ?cat0s.
        rewrite IH.
        rewrite -catA -β_filter_cat.
        congr cons.
        rewrite !γ_filter_cat.
        rewrite (γ_collect_γ (size tl) l tl) //.
        rewrite IH //.
        move: (γ_responses_size_reduced l tl) => Hlt'.
        move: Hlt; simp response_size => /= Hlt; ssromega.
        rewrite responses_size_app.
        move: Hlt; simp response_size => /= Hlt.        
        move: (β_responses_size_reduced l tl) => Hlt'; ssromega.

        by apply: collect_preserves_all_not_eq; apply: γ_filter_all.

      * move=> Hlt; simp collect; rewrite -/cat !γ_filter_cat.
        rewrite (γ_collect_γ (size tl) l) //.
        
        rewrite IH.
        congr cons. congr NestedListResult.
        rewrite /indexed_map.
        rewrite indexed_map_In_β.
        rewrite indexed_map_In_nested_map.
        have H : forall n,
            indexed_map_In ρs
               (fun i r _ =>
                  collect (collect (r ++ indexed_β_filter l tl i) ++ indexed_β_filter l s2 i)) n =
            indexed_map_In ρs
               (fun i r _ =>
                  collect (r ++ indexed_β_filter l (tl ++ s2) i)) n.
        elim: ρs Hlt => //= hd' tl' IH' Hlt n'.
        simp indexed_map_In.
        rewrite IH.
        rewrite -catA indexed_β_cat.
        congr cons; apply: IH'.
        move: Hlt; simp response_size => /= Hlt. ssromega.
        move: Hlt; simp response_size => /= Hlt.
        move: (indexed_β_size_reduced l tl n') => Hltb.
        rewrite responses_size_app. ssromega.
        by rewrite H.
       
        move: (γ_responses_size_reduced l tl) => Hltg.
        move: Hlt; simp response_size => /= Hlt. ssromega.
          all: do ?[by rewrite /partial_response_eq].    
  Qed.

  Lemma collect_size_leq s :
    size (collect s) <= size s.
  Proof.
    apply_funelim (collect s) => //= [l | l v | l vs | l ρ | l ρs] tl.
    all: do ?[by move: (γ_size_le l tl) => Hlt Hleq; ssromega].
    all: do ?[by move: (γ_size_le l tl) => Hlt IH Hleq; ssromega].
  Qed.

  Lemma β_γ_diff_flt flt1 flt2 s :
    flt1 != flt2 ->
    β_filter flt1 (γ_filter flt2 s) = β_filter flt1 s .
  Proof.
    elim: s => //= hd tl IH.
    case: ifP => //=; case: hd => //= l ρ Hneq1 Hneq;
    simp β_filter; case: eqP => //= Hfeq.
    all: do ?[by rewrite IH].

    by rewrite -Hfeq Hneq1 in Hneq.
  Qed.

  Lemma indexed_β_γ_diff_flt flt1 flt2 s i :
    flt1 != flt2 ->
    indexed_β_filter flt1 (γ_filter flt2 s) i = indexed_β_filter flt1 s i.
  Proof.
    funelim (indexed_β_filter flt1 s i) => //= Hneq; case: eqP => //= Heq2.
    all: do ?[by apply: H].
    
    by move: Heq Hneq; rewrite Heq2 => /eqP Hcontr /eqP Hneq; rewrite Hcontr in Hneq.
    simp indexed_β_filter; rewrite Heq /=.
      by rewrite (H flt2).
    simp indexed_β_filter; rewrite Heq /=.
      by apply: H.
  Qed.

  
  
  Lemma γ_collect flt s :
    γ_filter flt (collect s) = collect (γ_filter flt s).
  Proof.
    apply_funelim (collect s) => //= [l | l v | l vs | l ρ | l ρs] tl IH;
    case: ifP => Heq; simp collect => /=.
    all: do ?[congr cons].
    all: do ?[by rewrite γ_filter_swap IH].
    all: do ?[by move/eqP: Heq ->; rewrite (γ_collect_γ (size tl) flt)].

    - move=> IH2; congr cons; last by rewrite γ_filter_swap IH2.
      congr NestedResult.
        by rewrite (β_γ_diff_flt l flt).
    - move=> IH2; congr cons; last by rewrite γ_filter_swap IH2.
      congr NestedListResult.
      rewrite /indexed_map.
      have HIn : forall s i, indexed_map_In s (fun i r _ => collect (r ++ indexed_β_filter l tl i)) i =
                        indexed_map_In s (fun i r _ => collect (r ++ indexed_β_filter l (γ_filter flt tl) i)) i.
        elim=> //= hd tl' IH' i; simp indexed_map_In.
        by rewrite (indexed_β_γ_diff_flt l flt) // IH'.
          by apply: HIn.
  Qed.
    



  Lemma β_γ_N_compatible l flt s :
    (forall l ρ, flt != NestedResult l ρ) ->
    all (have_compatible_shapes flt) s ->
    β_filter l (γ_filter flt.(rname) s) = β_filter l s.
  Proof.
    elim: s => //= hd tl IH H /andP [Hcomp Hall].
    case: ifP => //= Heq.
    case: hd Hcomp Heq => [l' | l' v | l' vs | l' ρ | l' ρs]; simp β_filter => /= Hcomp Hneq.
    case: eqP => //= Heq2.
    rewrite IH //.
    case: flt IH Hall H Hcomp Hneq => /= [l2 | l2 v' | l2 vs' | l2 ρ' | l2 ρs'] IH Hall H; simp have_compatible_shapes => //=.
    move/eqP: Heq => Heq.
    case: hd Heq Hcomp => [l' | l' v | l' vs | l' ρ | l' ρs] /= Heq; simp have_compatible_shapes.
    case: flt IH Hall H Heq => //= [l2 | l2 v' | l2 vs' | l2 ρ' | l2 ρs'] IH Hall H Heq; simp have_compatible_shapes => //= /eqP Hcontr.
    all: do ?[by rewrite Heq in Hcontr].
    by move/eqP: (H l2 ρ').
  Qed.

  Lemma β_collect_swap flt1 s :
    wf_responses s ->
    β_filter flt1 (collect s) = collect (β_filter flt1 s).
  Proof.
    apply_funelim (collect s) => // [l | l v | l vs | l ρ | l ρs] tl IH; simp β_filter.
    all: do ?move=> /= /and3P [Hwf Hall Hwfs].
    all: do ?[by rewrite IH; [ rewrite β_γ_N_compatible
                          | apply: γ_filter_preserves_wf]].

    - move=> IHtl /= /and3P [Hwf Hall Hwfs].
      case: eqP => //= Heq; last first.
      rewrite IHtl //; last by apply: γ_filter_preserves_wf.
      rewrite β_γ_diff_flt //.
        by apply/eqP=> Hcontr; rewrite Hcontr in Heq.
      rewrite Heq (β_filter_nil flt1 (collect _)) ?cats0 //.
        by apply: collect_preserves_all_not_eq; apply: γ_filter_all.

    - move=> IHtl /= /and3P [Hwf Hall Hwfs].
      by rewrite IHtl; [rewrite (β_γ_N_compatible flt1 (NestedListResult l ρs))
                    | apply: γ_filter_preserves_wf].
  Qed.
    
    
  
  Lemma collect_β flt s1:
    map_all (@have_compatible_shapes Name Vals) s1 ->
    collect (β_filter flt (collect s1)) = collect (β_filter flt s1).
  Proof.
    funelim (collect s1) => //= /andP [Hall Hcomp];
    simp β_filter.
    all: do ?[by rewrite H; [rewrite (β_γ_N_compatible flt _ l) | apply: filter_preserves_map_all]].

      
    - case: eqP => //= Heq.
      rewrite Heq (β_filter_nil flt (collect _)) ?cats0.
        by rewrite -collect_collect_same.
          by apply: collect_preserves_all_not_eq;  apply: γ_filter_all.
      rewrite H0; last by apply: filter_preserves_map_all.
      rewrite β_γ_diff_flt //.
      by apply/eqP => Hcontr; rewrite Hcontr in Heq.

    - rewrite H0.
        by rewrite (β_γ_N_compatible flt (NestedListResult s4 l2) l).
        by apply: filter_preserves_map_all.
  Qed.
  
  
    
  Lemma collect_indexed_β :
    forall n flt s1 i,
      size s1 <= n ->
      collect (indexed_β_filter flt (collect s1) i) = collect (indexed_β_filter flt s1 i).
  Proof.
    elim=> [| n IH] flt s1 i.
    - by rewrite leqn0 => /eqP /size0nil -> /=; simp collect.
    - case: s1 => //= hd tl Hlt.
      case_response hd; simp collect => //=; simp indexed_β_filter.
      admit.
      admit.
      admit.
      admit.
      rewrite -?indexed_β_filter_equation_6.
      admit.
  Admitted.




  

 

  Lemma β_filter_preserves_wf l ρ flt s :
    wf_responses ρ ->
    all (have_compatible_shapes (NestedResult l ρ)) s ->
    wf_responses (ρ ++ β_filter flt s).
  Proof.
    move=> Hwf.
    funelim (β_filter flt s) => //=.
    - by intros; simp β_filter; rewrite cats0.
    all: do ?[by move/andP=> [Hcomp Hall]; apply: (H l0)].
    all: do ?[by move/andP=> [Hcomp Hall]; apply: (H l1)].
    - simp have_compatible_shapes => /andP [Hcomp Hall].
  Admitted.
      
  
  Hint Resolve responses_size_γ_leq.
  Lemma collect_collect_cat_tail s1 s2 :
    wf_responses (s1 ++ s2) ->
    collect (s1 ++ collect s2) = collect (s1 ++ s2).
  Proof.
    move: {2}(responses_size _) (leqnn (responses_size s1)) => n.
    elim: n s1 s2 => [| n IH].
    - case=> [| hd tl] s2 /= Hlt Hcomp.
      * by rewrite -collect_collect_same.
      * move: Hlt; rewrite leqn0 addn_eq0 => /andP [/eqP Hcontr _].
        move: (response_size_n_0 hd); rewrite lt0n => /eqP.
        by rewrite Hcontr.
    - case=> [| hd tl] s2 /= Hlt.
      * by rewrite -collect_collect_same.
      * case: hd Hlt => [l | l v | l vs | l ρ | l ρs]; simp response_size => Hlt;
        have Htllt : responses_size tl < n by ssromega.   

        all: do ?[by move/and3P=> [_ Hall Hwf]; simp collect => /=; congr cons;
                  rewrite 2!γ_filter_cat γ_collect; apply: IH;[ by apply: responses_size_γ_leq
                                                              | rewrite -γ_filter_cat; apply: γ_filter_preserves_wf]].
        
        
        move/and3P=> [Hwf Hall Hwfs]; simp collect => /=; congr cons; last first.
        by rewrite 2!γ_filter_cat γ_collect; apply: IH;  [ apply: responses_size_γ_leq
                                                         | rewrite -γ_filter_cat; apply: γ_filter_preserves_wf].
             
        congr NestedResult.
        rewrite 2!β_filter_cat 2!catA.
        rewrite β_collect_swap //.
        apply: IH.
        by rewrite responses_size_app; move: (β_responses_size_reduced l tl) => Hbleq; ssromega.
        rewrite -catA -β_filter_cat.
        by apply: (β_filter_preserves_wf l ρ).
        by case: (wf_responses_cat Hwfs).


        move/and3P=> [Hwf Hall Hwfs]; simp collect => /=; congr cons; last first.
        by rewrite 2!γ_filter_cat γ_collect; apply: IH;  [ apply: responses_size_γ_leq
                                                         | rewrite -γ_filter_cat; apply: γ_filter_preserves_wf].
      
        congr NestedListResult.
        rewrite /indexed_map.  
        have H : forall n,
            indexed_map_In ρs
              (fun i r _ =>
                 collect (r ++ indexed_β_filter l (tl ++ collect s2) i)) n =
            indexed_map_In ρs
              (fun i r _ =>
                 collect (r ++ indexed_β_filter l (tl ++ s2) i)) n.
        
  Admitted.



  



      
  Lemma eval_collect_cat schema g u s1 s2 :
    wf_responses (eval_queries schema g u s1 ++ eval_queries schema g u s2) ->
    eval_queries schema g u (s1 ++ s2) =
    collect (eval_queries schema g u s1 ++ eval_queries schema g u s2).
  Proof.
    elim: s1 s2 => [ /= | hd tl IH] s2 Hwf.
    - by apply: eval_queries_collect_same.
    - rewrite {2}/eval_queries -/eval_queries cat_cons /= IH.
      rewrite (collect_collect_2_cat (responses_size (eval schema g u hd ++ eval_queries schema g u tl)) _ _) // -catA.

      rewrite (collect_collect_cat_tail) //.
      
      simpl in Hwf.
  Admitted.

      
  Lemma collect_eval_cat schema g u s1 s2 :
    collect (eval_queries schema g u s1 ++ eval_queries schema g u s2) =
    eval_queries schema g u (s1 ++ s2).
  Proof.
    elim: s2 s1 => //= [| hd tl IH] s1.
    - by rewrite !cats0 -eval_queries_collect_same.

    - elim: s1 => //= [ | hd' tl' IH'].
        by rewrite [collect(collect _)]collect_non_redundant_eq //.
        
      
  Admitted.
  
  Lemma implementation_nil_for_object schema ty :
    is_object_type schema ty ->
    implementation schema ty = fset0.
  Proof.
    funelim (is_object_type schema ty) => //= _.
    rewrite /implementation.
  Admitted.

  Lemma union_nil_for_object schema ty :
    is_object_type schema ty ->
    union_members schema ty = fset0.
  Admitted.
    
    
  Lemma inline_nested_empty schema (g : @conformedGraph Name Vals schema) :
    forall t1 t2 ϕ,
      is_object_type schema t1 ->
      is_object_type schema t2 ->
      t1 <> t2 ->
      eval schema g g.(root) (InlineFragment t1 [:: (InlineFragment t2 ϕ)]) = [::].
  Proof.
    move=> t1 t2 ϕ Hobj Hobj' /eqP /negbTE Hneq /=.
    move: (query_has_object_type schema).
    move: (root_query_type g) => <- Hscope.
    simp eval.
    case: eqP => //= Heq; [simp eval; rewrite Heq Hneq /=|];
    rewrite implementation_nil_for_object //=;
    rewrite union_nil_for_object //=.
  Qed.
  

  Lemma inline_query_preserves schema (g : @conformedGraph Name Vals schema):
    forall ϕ u,
      u \in nodes g.(graph) ->
      eval schema g u ϕ = eval schema g u (InlineFragment u.(type) [:: ϕ]).
  Proof.
    move=> ϕ u Hin; case: g Hin.
    move=> g Hr He Hf Hn /= Hin.
    rewrite /nodes_have_object_type in Hn.
    move/seq.allP /(_ u Hin): Hn.
    case: u Hin => ty flds Hin. rewrite /type. funelim (is_object_type schema ty) => //.
    move=> _.
    Admitted.

  Lemma asf schema (g : @conformedGraph Name Vals schema)  u type_in_scope ti ϕ :
     query_conforms schema type_in_scope (InlineFragment ti ϕ) ->
     type_in_scope \in implementation schema ti ->
            eval schema g u (InlineFragment ti ϕ) = eval schema g u (InlineFragment type_in_scope ϕ). 
  Proof.
    move=> Hqc Himpl.
    move: (has_implementation_is_interface Himpl) => Hint.
    rewrite !eval_equation_5.
    funelim (is_interface_type schema ti) => //.
    
    Abort.
  (* Missing info on node -> type of node should be same as the one in scope *)
  

  
  

  Lemma nf_queries_eq schema (g : @conformedGraph Name Vals schema) u n α ϕ ϕ' :
    (forall v, eval_queries schema g v ϕ = eval_queries schema g v ϕ') ->
    eval schema g u (NestedField n α ϕ) = eval schema g u (NestedField n α ϕ').
  Proof.
    move=> Hqs.
    do 2 rewrite eval_equation_3.
    case lookup_field_type => //=.
    case=> [nt | lt].
    case neighbours_with_field => // v1 vn /=.
      by rewrite Hqs.
    case neighbours_with_field => // v1 vn /=.
    congr cons.
    congr NestedListResult.
    rewrite Hqs.
    congr cons.
  Admitted.

  
    
      
End QuerySemantic.


Arguments γ_filter [Name Vals].
Arguments β_filter [Name Vals].
Arguments indexed_β_filter [Name Vals].

Arguments collect [Name Vals].
Arguments eval [Name Vals].
Arguments eval_queries [Name Vals].
