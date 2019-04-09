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
      
      Equations indexed_β_filter (filter :  @ResponseObject Name Vals) (responses : seq (@ResponseObject Name Vals))  (index : nat) : seq.seq (@ResponseObject Name Vals) :=
        {
          indexed_β_filter _ [::] _ := [::];
          indexed_β_filter filter (hd :: tl) index :=
            (β_aux filter hd index) ++ (indexed_β_filter filter tl index)
            where
            β_aux (flt result : @ResponseObject Name Vals) (i : nat) : seq (@ResponseObject Name Vals) :=
              {
                β_aux (NestedListResult l' _) (NestedListResult l rs)  i
                  with l == l' :=
                  {
                  | true := get_nth [::] rs i;
                  | false => [::]
                  };
                β_aux _ _ _ := [::]
              }
        }.
    
    

      (** Auxiliary lemmas **)
      
    
  
      Lemma indexed_β_size_reduced (lst : seq.seq ResponseObject) (r : ResponseObject) (i : nat) :
        responses_size (indexed_β_filter r lst i) <= responses_size lst.
      Proof.
        apply (indexed_β_filter_elim
                 (fun flt rsp index res => responses_size res <= responses_size rsp)
                 (fun flt hd tl index r1 r2 i res => responses_size res <= response_size r2)) => //.
        - move=> flt hd tl index IH IH'.
          by rewrite responses_size_app /=; ssromega.
        -  move=> l1 l2 flt hd tl index rs' rs i'.
          
          funelim (get_nth [::] rs i') => //= Heq.
          simp response_size. ssromega.
          simp response_size.
          rewrite [responses_size t + _]addnC. 
          rewrite two_times_Sn; rewrite [4 + (2 * size l + 2)]addnA.
          rewrite -addnA -[2 + _]addnCA addnA; rewrite -[4 + 2 * size l + responses_size' l]/(response_size (NestedListResult l1 l)).
            by move: (H lst r i l1 l2 flt hd tl index rs' Heq ) => *; apply: leq_addr. 
      Qed.
      
      Lemma indexed_β_nil :
        forall flt rs i,
        all (fun r => ~~partial_response_eq flt r) rs ->
        indexed_β_filter flt rs i = [::].
      Proof.
        apply (indexed_β_filter_elim
                 (fun flt rsp index res =>
                    all (fun r => ~~partial_response_eq flt r) rsp ->
                    res = [::])
                 (fun flt hd tl index r1 r2 i res =>
                    ~~partial_response_eq r1 r2 ->
                    res = [::])) => //=.
        - move=> flt hd tl i IH IH' /andP [Hhd Htl].
            by rewrite IH // IH'.

        - by move=> l l' _ _ _ _ _ l2 i /eqP -> /eqP.
      Qed.

      
    End Indexed_Beta.

    Section Beta.
      (**
         β : ResponseObject -> ResponseObject -> seq ResponseObject
         Auxiliary function used in β_filter, used to extract the nested result 
         in a NestedResult response, whenever it matches the filter response 
         given as argument.
       **)
      
      Equations β (filter response: @ResponseObject Name Vals) : seq.seq (@ResponseObject Name Vals) :=
        {
          β (NestedResult l' _) (NestedResult l χ) with l == l' :=
            {
            | true => χ;
            | false => [::]
            };
          β _ _ := [::]
          }.
     

       (**
         β_filter : ResponseObject -> seq ResponseObject -> seq ResponseObject
         Traverses the list of response objects and extracts the nested result from an object,
         whenever it matches the filter response given as argument.
         
         This differs slightly from the definition given in Jorge and Olaf [WWW'18],
         where responses not matching would return an ϵ result (empty string). Here, 
         an empty list is returned (using β) but it gets deleted when it concatenates
         to the remaining list.
        **)
      
      Equations β_filter (filter : @ResponseObject Name Vals) (responses : seq.seq (@ResponseObject Name Vals)) : seq.seq (@ResponseObject Name Vals) :=
        β_filter _ nil := [::];
        β_filter filter (cons hd tl) := (β filter hd) ++ (β_filter filter tl).


      
      (** Auxiliary lemmas **)
      
      Lemma β_responses_size_reduced (lst : seq.seq ResponseObject) (flt : ResponseObject) :
        responses_size (β_filter flt lst) <= responses_size lst.
      Proof.
        funelim (β_filter flt lst) => //=.
        funelim (β filter r) => //=; try ssromega.
        rewrite responses_size_app.
        by simp response_size; ssromega.
      Qed.

      Lemma β_filter_nil flt rs :
        all (fun r => ~~partial_response_eq flt r) rs ->
        β_filter flt rs = [::].

      Proof.
        elim: rs => //= hd tl IH /andP [Hhd Htl].
        case: flt IH Hhd Htl => //.
        move=> f rs IH Hhd Htl; simp β_filter.
        rewrite {}IH // cats0.
        case: hd Hhd => // {Htl} f' rs'; simp β.
        rewrite /partial_response_eq => /eqP.
        by case: eqP => //= ->.
      Qed.
      
    End Beta.

        Section Gamma.

      (**
         γ : ResponseObject -> ResponseObject -> bool
         Predicate establishing whether a response object is partially equal to 
         another. The comparison is "superficial", not recursing in possible nested results.
       **)
      Equations γ (flt r : @ResponseObject Name Vals) : bool :=
        {
          γ (SingleResult l v) (SingleResult l' v') := (l == l') && (v == v');
          γ (ListResult l v) (ListResult l' v') := (l == l') && (v == v');
          γ (Null l) (Null l') := l == l';
          γ (NestedResult l _) (NestedResult l' _) := l == l'; 
          γ (NestedListResult l _) (NestedListResult l' _) := l == l';   (* Should check for equal size of sublists? *)
          γ _ _ => false
        }.


      (**
         γ_filter : ResponseObject -> seq ResponseObject -> seq ResponseObject 
         Filters out response objects that are partially equal to the filter
         response object given as argument.
         This differs slightly from the definition given in Jorge and Olaf [WWW'18],
         where matching responses would return an ϵ result (empty string) but here 
         these are deleted.
       **)
      (*Equations γ_filter (flt : @ResponseObject Name Vals) (responses : seq.seq (@ResponseObject Name Vals)) : seq.seq (@ResponseObject Name Vals) :=
        {
          γ_filter flt nil := nil;
          γ_filter flt (cons hd tl) <= γ flt hd => {
            γ_filter flt (cons hd tl) true => γ_filter flt tl;
            γ_filter flt (cons hd tl) false => cons hd (γ_filter flt tl)
          }
        }.*)

      Definition γ_filter (flt : @ResponseObject Name Vals) (responses : seq (@ResponseObject Name Vals)) : seq (@ResponseObject Name Vals) :=
        [seq r <- responses | ~~partial_response_eq flt r].
      



      (** Auxiliary Lemmas **)

      Lemma γ_responses_size_reduced (lst : seq.seq ResponseObject) (r : ResponseObject) :
        responses_size (γ_filter r lst) <= responses_size lst.
      Proof.
        rewrite /γ_filter.
        elim: lst=> // hd tl IH.
        simpl.
        case: ifP => // H.
        simpl. ssromega.
        ssromega.
      Qed.

      Lemma γ_filter_same_with_no_eq flt rs :
        all (fun r => ~~partial_response_eq flt r) rs ->
        γ_filter flt rs = rs.
      Proof.
        elim: rs => //= hd tl IH /andP [Hhd Htl].
        rewrite Hhd.
        by rewrite IH.
      Qed.

      Lemma γ_filter_cat flt s1 s2 :
        γ_filter flt (s1 ++ s2) = γ_filter flt s1 ++ γ_filter flt s2.
      Proof.
        by rewrite /γ_filter filter_cat. 
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

 
  Equations collect (responses : seq (@ResponseObject Name Vals)) : seq (@ResponseObject Name Vals)
    by wf (responses_size responses) lt :=
      collect [::] := [::];
      collect (cons (NestedResult l σ) tl) :=
                       (NestedResult l (collect (σ ++ (β_filter (NestedResult l σ) tl))))   
                         :: (collect (γ_filter (NestedResult l σ) tl));
                         
      collect (cons (NestedListResult l rs)  tl) :=
                         (NestedListResult l
                           (indexed_map rs             
                              (fun i r (H : In r rs) =>
                                 (collect (r ++ (indexed_β_filter (NestedListResult l rs) tl i))))))
                           :: (collect (γ_filter (NestedListResult l rs) tl));
                               
      collect (cons hd tl) := hd :: (collect (γ_filter hd tl)).
  Next Obligation.
    by move: (γ_responses_size_reduced tl (Null s)) => *; simp response_size; ssromega.
  Qed.
  Next Obligation.
      by move: (γ_responses_size_reduced tl (SingleResult s0 s1)) => *; simp response_size; ssromega.
  Qed.
  Next Obligation.
    by move: (γ_responses_size_reduced tl (ListResult s2 l0)) => *; simp response_size; ssromega.
  Qed.
  Next Obligation.
    rewrite responses_size_app. move: (β_responses_size_reduced tl (NestedResult l σ)) => *.
    have: responses_size σ < response_size (NestedResult l σ).
      by rewrite response_size_equation_4; ssromega.
        by move=> *; apply: sum_lt.
  Qed.    
  Next Obligation.
      by move: (γ_responses_size_reduced tl (NestedResult l σ)) => *; simp response_size;  ssromega.
  Qed.
  Next Obligation.
    rewrite responses_size_app -/(responses_size' rs).
    move: (in_responses_size r rs H) => Hleq.
    move: (indexed_β_size_reduced tl (NestedListResult l rs) i) => Hleq'; simp response_size.
      by ssromega.
  Qed.
  Next Obligation.
      by move: (γ_responses_size_reduced tl (NestedListResult l rs)) => *; simp response_size; ssromega.
  Qed.



  Lemma collect_nr_with_no_eq l ρ tl :
    all (fun r => ~~partial_response_eq (NestedResult l ρ) r) tl ->
    collect (NestedResult l ρ :: tl) = (NestedResult l (collect ρ)) :: collect tl.
  Proof.
    move=> Hneq; simp collect.
    rewrite β_filter_nil //=; rewrite cats0.
    rewrite γ_filter_same_with_no_eq //.
  Qed.


  Lemma indexed_map_In_eq l :
    forall ρ n tl χ,
      all (fun r => ~~partial_response_eq (NestedListResult l χ) r) tl ->
    indexed_map_In ρ
    (fun (i : nat) (r : seq ResponseObject) (_ : In r ρ) => collect (r ++ indexed_β_filter (NestedListResult l χ) tl i)) n =
    indexed_map_In ρ (fun (_ : nat) (r : seq ResponseObject) (_ : In r ρ) => collect r) n.
  Proof.
    elim=> // hd tl IH n tl0 χ Hneq; simp indexed_map_In.
    rewrite indexed_β_nil // cats0.
    congr cons.
    apply (IH n.+1 tl0 χ Hneq).
  Qed.
  
  
  Lemma collect_nlr_with_no_eq l ρ tl :
    all (fun r => ~~partial_response_eq (NestedListResult l ρ) r) tl ->
    collect (NestedListResult l ρ :: tl) = (NestedListResult l (indexed_map ρ (fun i r H => collect r))) :: collect tl.
  Proof.
    move=> Hneq; simp collect.
    rewrite γ_filter_same_with_no_eq //.
    congr cons; congr NestedListResult.
    rewrite /indexed_map.
    by apply indexed_map_In_eq.
  Qed.

  
  Lemma filter_preserves_non_redundancy flt responses :
    are_non_redundant__ρ responses ->
    are_non_redundant__ρ (γ_filter flt responses).
  Proof.
    elim: responses => //= hd tl IH.
    case Hhas: has => //=.
    move/andP=> [Hnr Hnrtl].
    case: ifP => //; last first.
      by move=> _; apply: IH => //=.
    rewrite are_non_redundant__ρ_equation_2.
    case Hhas': has => //=.  
    move/negbT: Hhas => /hasPn Hhas.
    move/hasP: Hhas' => [q].
    rewrite mem_filter => /andP [Hneq Hin].
    by move: (Hhas q Hin) => /negbTE ->.
    by move=> _; apply/andP; split => //; apply IH.
  Qed.

  
    
  Lemma γ_filter_eq flt s :
    has (fun r => partial_response_eq flt r) s = false ->
    γ_filter flt s = s.
  Proof.
    elim: s => // hd tl IH /hasPn H /=.
    case: ifP => // Heq.
    rewrite IH //.
    apply/hasPn => x Hin.
      by apply: H; apply: mem_tail.
    have Hin : hd \in hd :: tl by apply: mem_head.
      by move: (H hd Hin); rewrite Heq.
  Qed.

  
  Lemma β_filter_eq flt s :
    has (fun r => partial_response_eq flt r) s = false ->
    β_filter flt s = [::].
  Proof.
    elim: s => // hd tl IH /hasPn.
    case: hd => // [l | l v | l vs | l ρ | l ρs] Hhas; simp β_filter; case: flt IH Hhas => //.
    all: do ?[by intros; simp β; rewrite cat0s IH //;
              apply/hasPn => x Hin; apply: Hhas; apply: mem_tail].

    move=> l' χ IH Hhas; simp β.
    case: eqP => //= Heq.
    - move: (Hhas (NestedResult l ρ) (mem_head (NestedResult l ρ) _)) => /= /eqP.
      by rewrite Heq.
    - apply: IH; apply/hasPn=> x Hin.
      by apply: Hhas; apply: mem_tail.
  Qed.

  Lemma indexed_β_eq flt s i :
     has (fun r => partial_response_eq flt r) s = false ->
     indexed_β_filter flt s i = [::].
  Proof.
    elim: s => // hd tl IH /hasPn.
    case: hd => // [l | l v | l vs | l ρ | l ρs] Hhas; simp indexed_β_filter => /=; case: flt IH Hhas => //.

    all: do ?[by intros=> /=; apply: IH; apply/hasPn => x Hin; apply: Hhas; apply: mem_tail].

    move=> l' χ IH Hhas /=.
    case: eqP => Heq //=.
    move: (Hhas (NestedListResult l ρs) (mem_head (NestedListResult l ρs) _)) => /= /eqP.
      by rewrite Heq.
    by apply: IH; apply/hasPn => x Hin; apply: Hhas; apply: mem_tail.
  Qed.


 (* Lemma indexed_map_In_eq_2 s s2 flt:
    are_non_redundant__ρ s2 ->
    (forall (i : nat) (r : seq ResponseObject),
       In r s ->
       are_non_redundant__ρ (r ++ indexed_β_filter flt s2 i) ->
       collect (r ++ indexed_β_filter flt s2 i) = r ++ indexed_β_filter flt s2 i) ->
    all (fun x : response_eqType Name Vals => ~~ partial_response_eq flt x) s2 ->
    (indexed_map s
       (fun (i : nat) (r : seq ResponseObject) (_ : In r s) => collect (r ++ indexed_β_filter flt s2 i))) =
    s.
  Proof.
    elim: s s2 => // hd tl IH s2 Hnr H Hall.
    rewrite /indexed_map; simp indexed_map_In.
  *)

  Lemma map_collect_eq flt s1 s2 i :
    has (partial_response_eq flt) s2 = false ->
    all (are_non_redundant__ρ (Vals:=Vals)) s1 ->
    (forall r : seq ResponseObject,
        In r s1 ->
        are_non_redundant__ρ (r ++ indexed_β_filter flt s2 i) ->
        collect (r ++ indexed_β_filter flt s2 i) = r ++ indexed_β_filter flt s2 i) ->
    [seq collect x | x <- s1] = s1.
  Proof.
    move=> Hhas.
    rewrite indexed_β_eq //.
    move=> Hnr H.
    elim: s1 Hnr H => //= hd tl IH /andP [Hnr Hnrs] H.
    have/(H hd): hd = hd \/ In hd tl by left.
    rewrite cats0; move/(_ Hnr) => ->; congr cons.
    apply: IH => //.
    by move=> r Hin Hnr'; apply: H => //; right.
  Qed.
  
  Lemma collect_non_redundant_eq ρ :
    are_non_redundant__ρ ρ ->
    collect ρ = ρ.
  Proof.
    
    apply_funelim (collect ρ) => //= [l | l v | l vs | l χ | l ρs] tl IH.
   
    all: do ?[by case Hhas : has => //= /andP [Hnr Hnrs]; do ?[congr cons]; rewrite γ_filter_eq // in IH *; apply: IH].
  
    - move=> IH'.
      case Hhas: has => //= /andP.
      simp is_non_redundant__ρ; case=> [Hnr Hnrs]. 
      rewrite β_filter_eq // ?cats0 ?γ_filter_eq // in IH IH' *.
      by rewrite IH // IH'.

    - rewrite -collect_equation_6.
      
      move=> IH'.
      case Hhas: has => //= /andP.
      simp is_non_redundant__ρ; case=> [Hnr Hnrs].
      rewrite collect_nlr_with_no_eq // ?indexed_map_eq_map.
      rewrite ?γ_filter_eq // in IH IH' *; rewrite IH' //.
      congr cons; congr NestedListResult.
      pose i := 0.
      move: (IH i) => H.
      apply: (map_collect_eq (NestedListResult l ρs) ρs tl i) => //.
      by move/hasPn: Hhas => /allP.
  Qed.

  Lemma collect_preserves_non_redundancy ρs :
    are_non_redundant__ρ ρs ->
    are_non_redundant__ρ (collect ρs).
  Proof.
      by move=> Hnr; rewrite collect_non_redundant_eq.
  Qed.
    
    
  Lemma in_collect_γ r flt ρ :
    r \in collect (γ_filter flt ρ) ->
    ~~partial_response_eq flt r.
  Proof.
    elim: ρ flt => //= hd tl IH flt.
    case: ifP => Heq; last by apply: IH.
    case: hd Heq => //= [l | l v | l vs | l ρ | l ρs] Heq; simp collect; rewrite inE => /orP [/eqP -> // | Hin];
    apply: IH.
    
  Admitted.
  
  Lemma collect_are_non_redundant ρs :
    are_non_redundant__ρ (collect ρs).
  Proof.
    elim: ρs => // hd tl IH.
  Admitted.
    
    
    
 


  
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

     - intros.
       apply: collect_are_non_redundant.
  Qed.

  Lemma eval_queries_are_non_redundant schema g u φ :
    are_non_redundant__ρ (eval_queries schema g u φ).
  Proof.
      by case: φ => //= hd tl; apply: collect_are_non_redundant.
  Qed.
      
  Lemma gamma_filter_single_result_null f f' v (lst : seq (@ResponseObject Name Vals)) :
    γ_filter (SingleResult f v) ((Null f') :: lst) = (Null f') :: γ_filter (SingleResult f v) lst. Proof. done. Qed.

  
  Lemma collect_single_result l v :
    collect [:: (SingleResult l v)] = [:: (SingleResult l v)].
  Proof. done. Qed.

  Lemma collect_null_result l :
    collect [:: Null l] = [:: Null l].
  Proof. done. Qed.


  Lemma γ_filter_swap flt1 flt2 s :
    γ_filter flt1 (γ_filter flt2 s) = γ_filter flt2 (γ_filter flt1 s).
  Proof.
    elim: s => //= hd tl IH.
    case: ifP => Hpeq /=;
    case: ifP => Hpeq2 /=.

    all: do ?[by rewrite Hpeq IH].
    all: do ?[by rewrite IH].
  Qed.
  
  Lemma collect_γ_filter flt lst :
    γ_filter flt (collect (γ_filter flt lst)) = collect (γ_filter flt lst).
  Proof.
  Admitted.


  Hint Resolve collect_are_non_redundant.
  Lemma collect_collect_same (r : seq (@ResponseObject Name Vals)) :
    collect r = collect (collect r).
  Proof.
    rewrite [collect (collect r)]collect_non_redundant_eq //.
  Qed.

  Hint Resolve eval_non_redundant eval_queries_are_non_redundant.
  Lemma eval_collect_same :
    forall schema graph u query,
      eval schema graph u query = collect (eval schema graph u query).
  Proof.
    intros; rewrite collect_non_redundant_eq //.
  Qed.
   (* apply (eval_elim
             (fun schema g u q res =>
                res = collect res)
             (fun schema g u qs res =>
                res = collect res)) => schema g u.
    - move=> f α φ /= IH1 IH2.
      case Hty: lookup_field_type => [rty|] //=.
      case: rty Hty => // rty Hty.
      case: ohead => [v|] //=.
      rewrite collect_nr_with_no_eq //=; simp collect.
      rewrite -IH1 //; exact: (NT rty).
      rewrite collect_nlr_with_no_eq //=; simp collect.
      congr cons; congr NestedListResult.
      rewrite indexed_map_eq_map /=.
      rewrite -map_comp /= /funcomp.

      have H: (forall v : node, eval_queries schema g v φ = collect (eval_queries schema g v φ)) ->
            forall s, [seq eval_queries schema g v φ | v <- s] =
                 [seq collect (eval_queries schema g v φ) | v <- s].
      move=> H; elim=> //= hd tl IH.
        by rewrite -H IH.
      apply: H.
      by apply: IH2.  

    - move=> l f α φ /= IH1 IH2.
      case Hty: lookup_field_type => [rty|] //=.
      case: rty Hty => // rty Hty.
      case: ohead => [v|] //=.
      rewrite collect_nr_with_no_eq //=; simp collect.
      rewrite -IH1 //; exact: (NT rty).
      rewrite collect_nlr_with_no_eq //=; simp collect.
      congr cons; congr NestedListResult.
      rewrite indexed_map_eq_map /=.
      rewrite -map_comp /= /funcomp.

      have H: (forall v : node, eval_queries schema g v φ = collect (eval_queries schema g v φ)) ->
            forall s, [seq eval_queries schema g v φ | v <- s] =
                 [seq collect (eval_queries schema g v φ) | v <- s].
      move=> H; elim=> //= hd tl IH.
        by rewrite -H IH.
      apply: H.
      by apply: IH2.  

    all: do ?[by intros; simp collect].
      
    - move=> hd tl IHhd IHtl.
      by rewrite -collect_collect_same.
  Qed.*)


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

  Lemma γ_collect_γ flt s :
    γ_filter flt (collect (γ_filter flt s)) = collect (γ_filter flt s).
  Proof.
    elim: s => //= hd tl IH.
    case: flt IH => [l | l v | l vs | l ρ | l ρs] IH; case: ifP => //.
    Admitted.


  
  Lemma collect_collect_2_cat s1 s2 :
    collect (collect s1 ++ s2) = collect (s1 ++ s2).
  Proof.
    elim: s1 s2 => // hd tl IH s2.
    case_response hd; simp collect; do ? rewrite -/(cat _ _).
    congr cons.
    rewrite 2!γ_filter_cat γ_collect_γ.
    
    (*
    elim: s2 s1 => // [| hd tl IH] s1.
    - by rewrite 2!cats0 -collect_collect_same.
    - 
      case: s1 => //= hd' tl'.
      case: hd' => //.
      move=> l; rewrite ?collect_equation_2 -/(cat _ _).
      congr cons.
      rewrite 2!γ_filter_cat.
      

  Abort. *)
    
      
  Lemma collect_collect_3_cat s1 s2 s3 :
    collect (collect(s1 ++ s2) ++ s3) =
    collect (s1 ++ collect(s2 ++ s3)).
  Proof.
    elim: s1 s2 s3 => // [| hd tl IH] s2 s3.
    rewrite 2!cat0s.
    elim: s2 s3 => //=.
    - by move=> s3; simp collect; rewrite cat0s -collect_collect_same.
    - move=> hd tl IH s3.
  Abort.

  Lemma eval_collect_cat schema g u s1 s2 :
    eval_queries schema g u (s1 ++ s2) =
    collect (eval_queries schema g u s1 ++ eval_queries schema g u s2).
  Proof.
    elim: s2 s1 => // [ /=| hd tl IH] s1.
    - by rewrite 2!cats0 -eval_queries_collect_same.

    -


      
  Lemma collect_eval_cat schema g u s1 s2 :
    collect (eval_queries schema g u s1 ++ eval_queries schema g u s2) =
    eval_queries schema g u (s1 ++ s2).
  Proof.
    elim: s2 s1 => //=.
    - intros; rewrite !cats0.
        by rewrite -eval_queries_collect_same.

    - move=> hd tl IH s1.
      rewrite [RHS]eval_queries_collect_same.
      
    elim: s1 s2 => //=.
    - move=> s2. by rewrite -eval_queries_collect_same.
    - move=> hd tl IH s2.
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

Arguments collect [Name Vals].
Arguments eval [Name Vals].
Arguments eval_queries [Name Vals].