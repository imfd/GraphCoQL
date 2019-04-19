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

Section QuerySemantic.

  Variables N Name Vals : ordType.
  
  
  Ltac case_response r := case: r => [l | l v | l vs | l ρ | l ρs].
    
  Section Aux.    
    Variables (T1 T2 : Type).
    
    Equations indexed_map_In s (f : forall (i : nat) (x : T1), In x s -> T2) (index : nat) : seq T2 :=
      { 
        indexed_map_In [::] _ _ := [::];
        indexed_map_In (hd :: tl) f i := (f i hd _) :: (indexed_map_In tl (fun i x H => f i x _) i.+1)
      }.
      
    (**
       indexed_map : (s : seq T1) -> (nat -> x : T1 -> x ∈ s -> T2) -> seq T2
       Applies the function to every element in the given list.
       It is a regular map function but it allows to use the information
       about the index of the element where the function is being applied.
       The function also requires a proof that the element where it's being
       applied belongs to the list. This is mainly to be able to prove some
       obligations afterwards.
     **)
    Definition indexed_map (s : list T1) (f : forall (i : nat) (x : T1), In x s -> T2)  : list T2 :=
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
     
     

       (**
         β_filter : ResponseObject -> seq ResponseObject -> seq ResponseObject
         Traverses the list of response objects and extracts the nested result from an object,
         whenever it matches the filter response given as argument.
         
         This differs slightly from the definition given in Jorge and Olaf [WWW'18],
         where responses not matching would return an ϵ result (empty string). Here, 
         an empty list is returned (using β) but it gets deleted when it concatenates
         to the remaining list.
        **)
      
      Equations β_filter (filter : Name) (responses : seq (@ResponseObject Name Vals)) : seq (@ResponseObject Name Vals) :=
        {
          β_filter _ [::] := [::];
          
          β_filter filter ((NestedResult l χ) :: tl)
            with l == filter :=
            {
            | true := χ ++ (β_filter filter tl);
            | _ := (β_filter filter tl)
            };
          
          β_filter filter (_ :: tl) := β_filter filter tl
            
        }.
      
      
      (** Auxiliary lemmas **)
      
      Lemma β_responses_size_reduced (flt : Name) (lst : seq ResponseObject)  :
        responses_size (β_filter flt lst) <= responses_size lst.
      Proof.
        funelim (β_filter flt lst) => //=; do ?ssromega.
        rewrite responses_size_app.
        by simp response_size; ssromega.
      Qed.

      Lemma β_filter_nil l rs :
        all (fun r => r.(rname) != l) rs ->
        β_filter l rs = [::].
      Proof.
        funelim (β_filter l rs) => //= /andP [Hneq Hall].
        all: do ? by apply: H.
        by rewrite Heq in Hneq.
      Qed.

      Lemma β_filter_cat flt s1 s2 :
        β_filter flt (s1 ++ s2) = β_filter flt s1 ++ β_filter flt s2.
      Proof.
        elim: s1=> //= hd tl IH.
        case: hd => //= l ρ;
                     simp β_filter.
        case: eqP => //=.
          by rewrite -catA -IH.
       Qed.

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
      

      Definition γ_filter (flt : Name) (responses : seq (@ResponseObject Name Vals)) : seq (@ResponseObject Name Vals) :=
        [seq r <- responses | r.(rname) != flt].
      



      (** Auxiliary Lemmas **)

      Lemma γ_filter_all flt rs :
        all (fun r => r.(rname) != flt) (γ_filter flt rs).
      Proof.
          by apply/allP=> x; rewrite mem_filter => /andP [H].
      Qed.
      
      Lemma γ_responses_size_reduced (flt : Name) (lst : seq ResponseObject)  :
        responses_size (γ_filter flt lst) <= responses_size lst.
      Proof.
        rewrite /γ_filter.
        elim: lst=> //= hd tl IH.
        by case: ifP => //= H; ssromega.
      Qed.

      Lemma γ_filter_same_with_no_eq flt rs :
        all (fun r => r.(rname) != flt) rs ->
        γ_filter flt rs = rs.
      Proof.
        elim: rs => //= hd tl IH /andP [Hhd Htl].
        by rewrite Hhd IH.
      Qed.

      
      Lemma γ_filter_neq_preserves_list flt s :
        all (fun r => r.(rname) != flt) s ->
        γ_filter flt s = s.
      Proof.
        elim: s => //= hd tl IH /andP [-> Hall].
          by rewrite IH.
      Qed.

      Lemma γ_filter_same_hasN flt s :
        γ_filter flt s = s ->
        forall r, r \in s -> r.(rname) != flt.
      Proof.
        move=> <-.
          by move=> r; rewrite /γ_filter mem_filter => /andP [H].
      Qed.
  
      Lemma γ_filter_cat flt s1 s2 :
        γ_filter flt (s1 ++ s2) = γ_filter flt s1 ++ γ_filter flt s2.
      Proof.
        by rewrite /γ_filter filter_cat. 
      Qed.

      Lemma γ_filter_swap flt1 flt2 s :
        γ_filter flt1 (γ_filter flt2 s) = γ_filter flt2 (γ_filter flt1 s).
      Proof.
        elim: s => //= hd tl IH.
        case: ifP => Hpeq /=;
        case: ifP => Hpeq2 /=.
        
        all: do ?[by rewrite Hpeq IH].
        all: do ?[by rewrite IH].
      Qed.

      Lemma γ_filter_preserves_non_redundancy flt responses :
        are_non_redundant__ρ responses ->
        are_non_redundant__ρ (γ_filter flt responses).
      Proof.
        elim: responses => //= hd tl IH /and3P [Hall Hnr Hnrs].
        case: eqP => //= Heq.
          by apply: IH.
        apply/and3P; split=> //.
        move/allP: Hall => Hall.
        apply/allP => x; rewrite mem_filter => /andP [_ Hin].
          by apply: Hall.
          by apply: IH.
      Qed.


      Lemma γ_size_le flt s :
        size (γ_filter flt s) <= size s.
      Proof.
        elim: s => //= hd tl IH.
        case: ifP => //= _.
          by ssromega.
      Qed.

      
      Lemma γ_size_lt flt s n :
        size s < n.+1 ->
        size (γ_filter flt s) <= n.
      Proof.
          by move=> Hlt; move: (γ_size_le flt s) => Hleq; ssromega.
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


  (** Collect 



   **)
  Equations collect (responses : seq (@ResponseObject Name Vals)) : seq (@ResponseObject Name Vals)
    by wf (responses_size responses) lt :=
      collect [::] := [::];
      collect ((NestedResult l σ) :: tl) :=
                       (NestedResult l (collect (σ ++ (β_filter l tl))))   
                         :: (collect (γ_filter l tl));
                         
      collect ((NestedListResult l rs) :: tl) :=
                         (NestedListResult l
                           (indexed_map rs             
                              (fun i r (H : In r rs) =>
                                 (collect (r ++ (indexed_β_filter l tl i))))))
                           :: (collect (γ_filter l tl));
                               
      collect (cons hd tl) := hd :: (collect (γ_filter hd.(rname) tl)).
  Next Obligation.
    by move: (γ_responses_size_reduced s tl) => *; simp response_size; ssromega.
  Qed.
  Next Obligation.
      by move: (γ_responses_size_reduced s0 tl) => *; simp response_size; ssromega.
  Qed.
  Next Obligation.
    by move: (γ_responses_size_reduced s2 tl) => *; simp response_size; ssromega.
  Qed.
  Next Obligation.
    rewrite responses_size_app. move: (β_responses_size_reduced l tl) => *.
    have: responses_size σ < response_size (NestedResult l σ).
      by rewrite response_size_equation_4; ssromega.
        by move=> *; apply: sum_lt.
  Qed.    
  Next Obligation.
      by move: (γ_responses_size_reduced l tl) => *; simp response_size;  ssromega.
  Qed.
  Next Obligation.
    rewrite responses_size_app -/(responses_size' rs).
    move: (in_responses_size r rs H) => Hleq.
    move: (indexed_β_size_reduced l tl i) => Hleq'; simp response_size.
      by ssromega.
  Qed.
  Next Obligation.
      by move: (γ_responses_size_reduced l tl) => *; simp response_size; ssromega.
  Qed.


  Definition χ__ρ response responses :=
    match response with
    | NestedResult l ρ => NestedResult l (collect (ρ ++ (β_filter l responses)))
    | NestedListResult l ρs =>
      (NestedListResult l
         (indexed_map ρs             
             (fun i r (H : In r ρs) =>
                (collect (r ++ (indexed_β_filter l responses i))))))
    | _ => response
    end.


  Lemma collect_χ__ρ r rs :
    collect (r :: rs) = (χ__ρ r rs) :: collect (γ_filter r.(rname) rs).
  Proof.
    by case_response r; rewrite /χ__ρ; simp collect.
  Qed.

  (*
  Lemma collect_nr_with_no_eq l ρ tl :
    all (fun r => ~~partial_response_eq (NestedResult l ρ) r) tl ->
    collect (NestedResult l ρ :: tl) = (NestedResult l (collect ρ)) :: collect tl.
  Proof.
    move=> Hneq; simp collect.
    rewrite β_filter_nil //=; rewrite cats0.
    rewrite γ_filter_same_with_no_eq //.
  Qed.

   *)
  
  Lemma indexed_map_In_eq l :
    forall ρ n tl χ,
      all (fun r => ~~partial_response_eq (NestedListResult l χ) r) tl ->
      indexed_map_In ρ
      (fun (i : nat) (r : seq ResponseObject) (_ : In r ρ) => collect (r ++ indexed_β_filter l tl i)) n =
      indexed_map_In ρ (fun (_ : nat) (r : seq ResponseObject) (_ : In r ρ) => collect r) n.
  Proof.
    elim=> // hd tl IH n tl0 Hneq; simp indexed_map_In.
    Admitted.
  (*  rewrite indexed_β_nil // cats0.
    congr cons.
    apply (IH n.+1 tl0 χ Hneq).
  Qed.
  
   *)
  
  Lemma indexed_map_nlr l ρs:
    (NestedListResult l
       (indexed_map ρs
          (fun i r _ => collect (r ++ indexed_β_filter l [::] i)))) =
    (NestedListResult l
       (indexed_map ρs
          (fun i r _ => collect r))).
  Proof.
    congr NestedListResult.
    rewrite /indexed_map.
    elim: ρs => //= hd tl IH.
    simp indexed_map_In => /=.
    simp indexed_β_filter; rewrite cats0.
  Admitted.

  
  Lemma indexed_map_In_β_nil :
    forall ρs l s i,
    all (fun r => r.(rname) != l) s ->
    indexed_map_In ρs
                (fun i r _ => collect (r ++ indexed_β_filter l s i)) i =
    indexed_map_In ρs
                   (fun i r _ => collect r) i.
  Proof.
    elim => //= hd tl IH l s i Hall; simp indexed_map_In.
    by rewrite indexed_β_nil // cats0 IH.
  Qed.
  
 

  Lemma indexed_map_eq_forall_i s2 l lst n :
    (forall s1 s2, responses_size s1 <= n -> collect (collect s1 ++ s2) = collect (s1 ++ s2)) ->
    forall i,
      indexed_map [seq collect r | r <- s2] (fun i r _ => collect (r ++ indexed_β_filter l lst i)) =
      indexed_map s2 (fun i r _ => collect (r ++ indexed_β_filter l lst i)) ->
      indexed_map_In [seq collect r | r <- s2] (fun i r _ => collect (r ++ indexed_β_filter l lst i)) i =
      indexed_map_In s2 (fun i r _ => collect (r ++ indexed_β_filter l lst i)) i.
  Proof.
    move=> Hcollect.
    elim: s2 => //= hd tl IH i.
    rewrite /indexed_map; simp indexed_map_In.
  Admitted.
  
  Lemma map_collect_eq flt s1 s2 i :
    has (partial_response_eq flt) s2 = false ->
    all (are_non_redundant__ρ (Vals:=Vals)) s1 ->
    (forall r : seq ResponseObject,
        In r s1 ->
        are_non_redundant__ρ (r ++ indexed_β_filter flt.(rname) s2 i) ->
        collect (r ++ indexed_β_filter flt.(rname) s2 i) = r ++ indexed_β_filter flt.(rname) s2 i) ->
    [seq collect x | x <- s1] = s1.
  Proof.
    move=> Hhas.
  Admitted.
  (*
    rewrite indexed_β_eq //.
    move=> Hnr H.
    elim: s1 Hnr H => //= hd tl IH /andP [Hnr Hnrs] H.
    have/(H hd): hd = hd \/ In hd tl by left.
    rewrite cats0; move/(_ Hnr) => ->; congr cons.
    apply: IH => //.
    by move=> r Hin Hnr'; apply: H => //; right.
  Qed.
   *)
  
  Lemma collect_non_redundant_eq ρ :
    are_non_redundant__ρ ρ ->
    collect ρ = ρ.
  Proof.
    
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
    funelim (collect ρs) => //=; apply/and3P; split=> //.
    all: do ?[by apply: collect_preserves_all_not_eq; apply: γ_filter_all].
    simp is_non_redundant__ρ.
    apply/allP => r Hin.
    Admitted.
    
    
  Hint Resolve collect_are_non_redundant.
  Lemma collect_collect_same (r : seq (@ResponseObject Name Vals)) :
    collect r = collect (collect r).
  Proof.
    rewrite [collect (collect r)]collect_non_redundant_eq //.
  Qed.
 


  
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
      

 
(*
  Lemma γ_filter_χ_eq flt s1 s2 :
    γ_filter flt s1 = γ_filter (χ__ρ flt s2) s1.
  Proof.
    elim: s1 => //= hd tl.
      by case_response flt; rewrite /χ__ρ; case: ifP.
  Qed. 


    
  Lemma χ__ρ_cat r s1 s2 :
    χ__ρ r (s1 ++ s2) = χ__ρ (χ__ρ r s1) s2.
  Proof.
    elim: s1 => //=.
    rewrite {3}/χ__ρ.
    case: r => // [l ρ | l ρs].
    
  Admitted.
                          
    
  Lemma χ__ρ_eq r s1 s2 s3 :
    all (fun r' => ~~partial_response_eq r r') s1 ->
    χ__ρ (χ__ρ r s2) (s1 ++ s3) = χ__ρ r (s2 ++ s3).
  Proof.
    case_response r => Hneq //=.
      
  Admitted.

   *)
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
    - move: (γ_size_le (Null l) tl) => Hlt Hleq; ssromega.
    - move: (γ_size_le (SingleResult l v) tl) => Hlt Hleq; ssromega.
    - move: (γ_size_le (ListResult l vs) tl) => Hlt Hleq; ssromega.
    - move: (γ_size_le (NestedResult l ρ) tl) => Hlt IH Hleq; ssromega.
    - move: (γ_size_le (NestedListResult l ρs) tl) => Hlt IH Hleq; ssromega.
  Qed.
      
  Lemma collect_γ :
    forall n flt s1,
      size s1 <= n ->
    collect (γ_filter flt (collect s1)) =
    collect (γ_filter flt s1).
  Proof.
    elim=> [| n IH] flt s1.
    - by rewrite leqn0 => /eqP /size0nil -> /=; simp collect.
    - case: s1 => //= hd tl Hlt.
      case_response hd; simp collect => /=;
      case: ifP => Heq; simp collect.
      congr cons.
      rewrite -(IH (Null l) (γ_filter flt _)).
      rewrite (IH flt (γ_filter _ tl)).
      rewrite γ_filter_swap.
      rewrite (IH (Null l) (γ_filter (Null l) (γ_filter flt tl))).
        by rewrite /γ_filter filter_id.
        admit.
        admit.
        admit.
      move/negbFE: Heq; rewrite /partial_response_eq; case: flt => //= l' /eqP ->.
      rewrite γ_filter_same_with_no_eq.
      by rewrite -collect_collect_same.
      by apply: collect_preserves_all_not_eq; apply: γ_filter_all.

  Admitted.

  Lemma β_filter_γ_Neq flt1 flt2 s :
    (forall l ρ, ~~partial_response_eq (NestedResult l ρ) flt2) ->
    β_filter flt1 (γ_filter flt2 s) = β_filter flt1 s.
  Proof.
    case: flt2 => // [l' _ | l' v' _ | l' vs' _ | l' χ | l' χ _];
    elim: s => //= hd tl IH; case: hd => //= l.

    all: do ?[by intros; case: ifP; simp β_filter].

    all: do ?[by intros; simp β_filter; case: eqP => //= Heq; rewrite IH].

    move=> ρ Hneq.
    case: eqP => [Hcontr | /= H]; simp β_filter.
      by move/eqP: (Hneq l [::]); rewrite Hcontr.
    by case: eqP => //=; rewrite IH.
  Qed.

  Lemma β_filter_γ_Neq2 flt l ρ s :
    l <> flt ->
    β_filter flt (γ_filter (NestedResult l ρ) s) = β_filter flt s.
  Proof.
    move=> Hneq.
    elim: s => //= hd tl IH.
    case: hd => //= l' χ.
    case: eqP => //= Heq; simp β_filter.
    case: eqP => //=.
      by rewrite -Heq => Hcontr; rewrite Hcontr in Hneq.
      by case: eqP => //= _; rewrite IH.
  Qed.

  Lemma collect_β :
    forall n flt s1,
      size s1 <= n ->
      collect (β_filter flt (collect s1)) = collect (β_filter flt s1).
  Proof.
    elim=> [| n IH] flt s1.
    - by rewrite leqn0 => /eqP /size0nil -> /=; simp collect.
    - case: s1 => //= hd tl Hlt.
      case_response hd; simp collect; simp β_filter.
      all: do ?[rewrite (IH flt (γ_filter _ tl)); last by apply: γ_size_lt].
      all: do ?[by rewrite β_filter_γ_Neq].

      case: eqP => //= Heq.
      rewrite Heq (β_filter_nil flt ρ (collect _)) ?cats0.
        by rewrite -collect_collect_same.
      apply: collect_preserves_all_not_eq;  apply: γ_filter_all.
        
      rewrite (IH flt (γ_filter _ tl)); last by apply: γ_size_lt.
      by rewrite β_filter_γ_Neq2.
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


  Lemma responses_size_γ_leq flt s n :
    responses_size s < n ->
    responses_size (γ_filter flt s) <= n.
  Proof.
    move=> Hlt.
    move: (γ_responses_size_reduced s flt) => Hleq.
    ssromega.
  Qed.

(*
   Lemma collect_collect_cat_tail :
    forall n s1 s2,
      size s1 + size s2 <= n ->
      collect (s1 ++ collect s2) = collect (s1 ++ s2).
   Proof.
     elim=> [| n IH] s1 s2.
     - by rewrite leqn0 addn_eq0 => /andP [/eqP/size0nil -> /eqP/size0nil ->] /=; simp collect.
     - case: s1 => //=.
       * by move=> _; rewrite -collect_collect_same.
       * move=> hd tl /= Hlt.
         rewrite -cat1s .
         rewrite -IH.
         rewrite (IH tl s2).
         rewrite IH.
           by rewrite cat1s.
         rewrite size_cat /= addnA add1n.
           
         rewrite -[X in  collect ([:: hd] ++ X)](IH tl (collect s2)).
 *)
  
  Hint Resolve responses_size_γ_leq.
  Lemma collect_collect_cat_tail :
    forall n s1 s2,
      responses_size s1 <= n ->
      collect (s1 ++ collect s2) = collect (s1 ++ s2).
  Proof.
    elim=> [| n IH].
    - case=> [| hd tl] s2 /= Hlt.
      * by rewrite -collect_collect_same.
      * move: Hlt; rewrite leqn0 addn_eq0 => /andP [/eqP Hcontr _].
        move: (response_size_n_0 hd); rewrite lt0n => /eqP.
        by rewrite Hcontr.
    - case=> [| hd tl] s2 /= Hlt.
      * by rewrite -collect_collect_same.
      * case: hd Hlt => [l | l v | l vs | l ρ | l ρs]; simp response_size => Hlt;
        have Htllt : responses_size tl < n by ssromega.   
        all: do ?[simp collect; congr cons; rewrite ?γ_filter_cat].
       
        rewrite -IH //.
        rewrite -(IH (γ_filter (Null l) tl) (γ_filter (Null l) s2)).
          by rewrite (collect_γ (size s2)).
        all: do ?[by apply: responses_size_γ_leq].
        rewrite -IH.
        rewrite -(IH (γ_filter (SingleResult l v) tl) (γ_filter (SingleResult l v) s2)).
          by rewrite (collect_γ (size s2)).
        all: do ?[by apply: responses_size_γ_leq].

        rewrite -IH.
        rewrite -(IH (γ_filter (ListResult l vs) tl) (γ_filter (ListResult l vs) s2)).
          by rewrite (collect_γ (size s2)).
        all: do ?[by apply: responses_size_γ_leq].

        congr NestedResult.
        rewrite !β_filter_cat !catA.
        rewrite -IH.
        rewrite -[RHS]IH.
          by rewrite (collect_β (size s2) l).
        all: do ?[rewrite responses_size_app;
                  move: (β_responses_size_reduced l tl) => Hleqb; ssromega].

         
        rewrite -IH.
        rewrite -(IH (γ_filter (NestedResult l ρ) tl) (γ_filter (NestedResult l ρ) s2)).
          by rewrite (collect_γ (size s2)).
        all: do ?[by apply: responses_size_γ_leq].

        congr NestedListResult.
        rewrite /indexed_map.  
        have H : forall n,
            indexed_map_In ρs
              (fun i r _ =>
                 collect (r ++ indexed_β_filter l (tl ++ collect s2) i)) n =
            indexed_map_In ρs
              (fun i r _ =>
                 collect (r ++ indexed_β_filter l (tl ++ s2) i)) n.
        elim: ρs Hlt => //= hd' tl' IH'; rewrite -/(responses_size hd') => Hlt n'.
        simp indexed_map_In.
        rewrite IH' //. congr cons.
        rewrite !indexed_β_cat !catA.
        rewrite -IH.
        rewrite -[RHS]IH.
        rewrite (collect_indexed_β (size s2) l s2 n') //.
        all: do ?[rewrite responses_size_app;
                  move: (indexed_β_size_reduced l tl n') => Hleqb; ssromega].

          by ssromega.
        apply: H.
        rewrite -IH.
        rewrite -(IH (γ_filter (NestedListResult l ρs) tl) (γ_filter (NestedListResult l ρs) s2)).
          by rewrite (collect_γ (size s2)).
        all: do ?[by apply: responses_size_γ_leq].
  Qed.
  
  (* χ 

 rewrite collect_χ__ρ cat_cons !collect_χ__ρ.
      rewrite !γ_filter_cat.
      rewrite γ_collect_γ ?IH.
      rewrite -γ_filter_χ_eq; congr cons.
      
      have Hp : forall s1 s3 s4,
          all (fun r' => ~~partial_response_eq hd r') s1 ->
          χ__ρ (χ__ρ hd s3) (s1 ++ s4) = χ__ρ hd (s3 ++ s4).

      elim => //= [| hd' tl' IH'] s3 s4.
      move=> _.
      elim: s3 => // [| hd'' tl'' IH''].
      rewrite cat0s.
      case: hd Hlt => //= [l ρ | l ρs] Hlt.
      * rewrite (β_filter_hasNnr_nil [::] l ρ) // cats0.
        rewrite IH //.
          by move: Hlt; simp response_size => Hlt; ssromega.
      * rewrite indexed_map_β_nil.
        rewrite indexed_map_eq_map.
        congr NestedListResult.
        elim: ρs Hlt => //= x rs IHrs Hlt.
        rewrite /indexed_map; simp indexed_map_In => /=.
        rewrite IH.
        congr cons.

        move: (indexed_map_eq_forall_i rs l s4 n IH) => /(_ 1) H.
        have Hlt': response_size (NestedListResult l rs) + responses_size tl <= n.+1.
          by move: Hlt; simp response_size => /= Hlt; ssromega.
          move: (IHrs Hlt') => Hasd.
        by move: (H Hasd).

        by move: Hlt; simp response_size => /= => Hlt; ssromega.

        
*)



      
  Lemma eval_collect_cat schema g u s1 s2 :
    eval_queries schema g u (s1 ++ s2) =
    collect (eval_queries schema g u s1 ++ eval_queries schema g u s2).
  Proof.
    elim: s1 s2 => [ /= | hd tl IH] s2.
    - by apply: eval_queries_collect_same.
    - rewrite {2}/eval_queries -/eval_queries cat_cons /= IH.
      rewrite (collect_collect_2_cat (responses_size (eval schema g u hd ++ eval_queries schema g u tl)) _ _) // -catA.

      rewrite (collect_collect_cat_tail (responses_size (eval schema g u hd))) //.
  Qed.

      
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
