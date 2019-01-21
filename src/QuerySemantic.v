From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord fmap.
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

Require Import List.

Section QuerySemantic.

  Variables N Name Vals : ordType.
  
  Notation "'ϵ'" := Empty.
  Notation "l <- 'null'" := (Null l) (at level 50).
  Notation "l <- v" := (SingleResult l v) (at level 50).
  Notation "l <<- vals" := (ListResult l vals) (at level 50).
  Notation "l <- {{ ρ }}" := (NestedResult l ρ) (at level 40). 
  Notation "l <<- [{ ρ }]" := (NestedListResult l ρ) (at level 40).


  
  Section Aux.    
    Variables (T1 T2 : Type).
    
    Equations indexed_map_In s (f : forall (i : nat) (x : T1), In x s -> T2) (index : nat) : seq.seq T2 :=
      indexed_map_In [::] _ _ := [::];
      indexed_map_In (cons hd tl) f i := cons (f i hd _) (indexed_map_In (fun i x H => f i x _) i.+1).


    (**
       indexed_map : (s : seq T1) -> (nat -> x : T1 -> x ∈ s -> T2) -> seq T2
       Applies the function to every element in the given list.
       It is a regular map function but it allows to use the information
       about the index of the element where the function is being applied.
       The function also requires a proof that the element where it's being
       applied belongs to the list. This is mainly to be able to prove some
       obligations afterwards.
     **)
    Equations indexed_map (s : list T1) (f : forall (i : nat) (x : T1), In x s -> T2)  : list T2 :=
      indexed_map s f := indexed_map_In f 0.

    
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

    
    Lemma In_r_size' (r : (@Result Name Vals)) rs0 : In r rs0 -> result_size r <= results_size rs0.
    Proof. elim: rs0 => [//| x rs' IH].
      move=> [-> | Hin].
      by simpl; ssromega.
      by move/IH: Hin => * /=; ssromega.
    Qed.
    
    Lemma le_lt_trans n m p : n < m -> m <= p -> n < p.
    Proof. by intros; ssromega. Qed.

    Lemma sum_lt a b c d : a < c -> b <= d -> (a + b < c + d)%coq_nat.
    Proof. intros. ssromega. Qed.

    Lemma sum_lt' a b c d : a < c -> b <= d -> a + b <= c + d.
    Proof. by move=> *; ssromega. Qed.
    
    Lemma two_times_Sn n : 2 * n.+1 = 2 * n + 2.
    Proof.  by []. Qed.
      
  End Aux.


  
  Section Filters.


    Section Indexed_Beta.

      (** 
          β_aux : ResponseObject -> ResponseObject -> nat -> seq ResponseObject.
 
          Auxiliary function used in indexed_β function, that extracts the i-th 
          element from a NestedListResult, whenever this response matches the 
          filter response passed as second argument. 
       **)

      Equations β_aux (result flt : @ResponseObject Name Vals) (i : nat) : seq.seq (@ResponseObject Name Vals) :=
        β_aux (NestedListResult l rs) (NestedListResult l' rs') i <= l == l' => {
          β_aux (NestedListResult l rs) _ i true := get_nth (Results [::]) rs i;
          β_aux _ _ _ false => Results [::]
        };
        β_aux _ _ _ := Results [::].
     
      (**
         indexed_β_filter : seq ResponseObject -> ResponseObject -> nat -> seq ResponseObject 
         Traverses the list and extracts the i-th element from a response, whenever it 
         corresponds to a NestedListResult and it matches the filter response.
         This differs slightly from the definition given in Jorge and Olaf [WWW'18],
         where responses not matching would return an ϵ result (empty string). Here,
         an empty list is returned, which gets deleted when the flattening occurs.
       **)
      
      Equations indexed_β_filter (responses : seq.seq (@ResponseObject Name Vals)) (filter :  @ResponseObject Name Vals) (index : nat) : seq.seq (@ResponseObject Name Vals) :=
        indexed_β_filter [::] _ _ := Results [::];
        indexed_β_filter (cons hd tl) filter index := (β_aux hd filter index) ++ (indexed_β_filter tl filter index).
    
    

      (** Auxiliary lemmas **)
      
      Lemma indexed_β_cons  (lst : seq.seq ResponseObject) (r x : ResponseObject) (i : nat) :
        indexed_β_filter (x :: lst) r i = (β_aux x r i) ++ (indexed_β_filter lst r i).
      Proof. by []. Qed.
  
      Lemma indexed_β_size_reduced (lst : seq.seq ResponseObject) (r : ResponseObject) (i : nat) :
        responses_size (indexed_β_filter lst r i) <= responses_size lst.
      Proof.
        elim: lst i => [//| x lst' IH] i.
        rewrite indexed_β_cons responses_size_app /=.
        funelim (β_aux x r i) => //=; do ?[move: (IH i) => H]; do ?ssromega.
        
        have: responses_size (get_nth (Results []) l0 i) < response_size (s4 <<- [{l0}]).
        funelim (get_nth (Results []) l0 i).
          - by [].
          - case: t => lt; rewrite result_size_helper_1_equation_5 /= addnA.
            by move: (responses_lt_result lt (Results lt)) => *; ssromega. 
          - rewrite result_size_helper_1_equation_5 /= [result_size t + _]addnC.
            rewrite two_times_Sn; rewrite [4 + (2 * size l + 2)]addnA.
            rewrite -addnA -[2 + _]addnCA addnA. rewrite -[4 + 2 * size l + results_size l]/(response_size (s4 <<- [{l}])).
            by move: (H s4 s5 l1 Heq lst' IH (IH n)) => *; apply: ltn_addr.
            by move=> Hl; apply: sum_lt'.
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
        β (NestedResult l' _) (NestedResult l χ) <= l == l' => {
          β (NestedResult l' _) (NestedResult l χ) true => χ;
          β (NestedResult l' _) (NestedResult l χ) false => [::]
        };
        β _ _ := [::].

     

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
        rewrite responses_size_app.
        have: responses_size (β filter r) < response_size r.
          move: response_size_n_0 => H0.
          funelim (β filter r) => //=.
          rewrite result_size_helper_1_equation_4; case: r0 => l0.
          by move: (responses_lt_result l0 (Results l0)) => *; ssromega.
        by move=> *; ssromega.
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
      Equations γ_filter (flt : @ResponseObject Name Vals) (responses : seq.seq (@ResponseObject Name Vals)) : seq.seq (@ResponseObject Name Vals) :=
        {
          γ_filter flt nil := nil;
          γ_filter flt (cons hd tl) <= γ flt hd => {
            γ_filter flt (cons hd tl) true => γ_filter flt tl;
            γ_filter flt (cons hd tl) false => cons hd (γ_filter flt tl)
          }
        }.



      (** Auxiliary Lemmas **)

      Lemma γ_responses_size_reduced (lst : seq.seq ResponseObject) (r : ResponseObject) :
        responses_size (γ_filter r lst) <= responses_size lst.
      Proof. by funelim (γ_filter r lst) => /=; ssromega. Qed.

    End Gamma.
    
  End Filters.



    
  Equations collect (responses : seq.seq (@ResponseObject Name Vals)) : seq.seq (@ResponseObject Name Vals) := 
    collect responses by rec (responses_size responses) lt :=
      collect [::] := [::];
      collect (cons (NestedResult l (Results σ)) tl) :=
                       (NestedResult l (Results (collect (σ ++ (β_filter (NestedResult l (Results σ)) tl)))))   
                         :: (collect (γ_filter (NestedResult l (Results σ)) tl));
                         
      collect (cons (NestedListResult l rs)  tl) :=
                         (NestedListResult l
                           (indexed_map                
                              (fun i r (H : In r rs) =>
                                 Results (collect (r ++ (indexed_β_filter tl (NestedListResult l rs) i))))))
                           :: (collect (γ_filter (NestedListResult l rs) tl));
                               
      collect (cons hd tl) := hd :: (collect (γ_filter hd tl)).
  Next Obligation.
    by move: (γ_responses_size_reduced tl hd) => *;  ssromega.
  Qed.
  Next Obligation.
    by move: (γ_responses_size_reduced tl hd) => *;  ssromega.
  Qed.
 Next Obligation.
    by move: (γ_responses_size_reduced tl hd) => *;  ssromega.
 Qed.
 Next Obligation.
   rewrite responses_size_app. move: (β_responses_size_reduced tl (NestedResult l (Results σ))) => *.
   have: responses_size σ < response_size (NestedResult l (Results σ)).
     by rewrite result_size_helper_1_equation_4; move: (responses_lt_result σ (Results σ)) => *; ssromega.
   by move=> *; apply: sum_lt.
 Qed.    
 Next Obligation.
     by move: (γ_responses_size_reduced tl (NestedResult l (Results σ))) => *;  ssromega.
 Qed.
 Next Obligation.
   case: r H => l0 Hin.
     rewrite responses_size_app.
     have: responses_size l0 < response_size (l <<- [{rs}]).
     move: (In_r_size' Hin) => Hrlt.  
     move: (responses_lt_result l0 (Results l0)) => Hr.

     move: (le_lt_trans Hr Hrlt) => Htrans.
     rewrite result_size_helper_1_equation_5.
     rewrite [4 + 2 * size rs + _]addnC.
       by apply: ltn_addr; apply: Htrans.
     move=> *; apply: sum_lt => [//|].
       by move: (indexed_β_size_reduced tl (l <<- [{rs}]) i).
   Qed.
   Next Obligation.
       by move: (γ_responses_size_reduced tl (NestedListResult l rs)) => *;  ssromega.
   Qed.
 
    
    Implicit Type schema : @wfSchema Name Vals.
    Implicit Type graph : @graphQLGraph N Name Vals.
    Implicit Type u : @node N Name Vals.
    Implicit Type query_set : @QuerySet Name Vals.
    Implicit Type query : @Query Name Vals.


    Fixpoint eval schema graph u query_set : @Result Name Vals :=
      match query_set with
      | SingleQuery q => match eval_query schema graph u q with
                        | inl r => Results [:: r]
                        | inr r => r
                        end
      | SelectionSet q q' =>
        let: Results res := eval schema graph u q' in
        match eval_query schema graph u q with
        | inl r => Results (collect (r :: res))
        | inr (Results r) => Results (collect (r ++ res))    (* I'm "lifting" the "on T { }" results to be at the same level as the others *)
        end
      end
     
    with eval_query schema graph u query : (@ResponseObject Name Vals) + @Result Name Vals :=
           match query with
           | SingleField name args => match u.(fields) (Field name args) with
                                     | Some (inl value) =>  inl (SingleResult name value)
                                     | _ => inl (Null name)
                                     end
           | LabeledField label name args =>  match u.(fields) (Field name args) with
                                             | Some (inl value) => inl (SingleResult label value)
                                             | _ => inl (Null name)
                                             end
           | NestedField name args ϕ => let target_nodes := get_target_nodes_with_field graph u (Field name args) in
                                       match lookup_field_type schema u.(type) name with
                                       | Some (ListType _) =>
                                         inl (NestedListResult name (map (fun v => eval schema graph v ϕ) target_nodes))
                                       | Some (NT _) =>
                                         match ohead target_nodes with
                                         | Some v => inl (NestedResult name (eval schema graph v ϕ))
                                         | _ => inl (Null name)
                                         end
                                       | _ => inl (Null name)         (* If the field ∉ fields(u) then it's null, right? *)
                                       end
                                         
           | NestedLabeledField label name args ϕ =>  let target_nodes := get_target_nodes_with_field graph u (Field name args) in
                                                      match lookup_field_type schema u.(type) name with
                                                      | Some (ListType _) =>
                                                        inl (NestedListResult label (map (fun v => eval schema graph v ϕ) target_nodes))
                                                      | Some (NT _) =>
                                                        match ohead target_nodes with
                                                        | Some v => inl (NestedResult label (eval schema graph v ϕ))
                                                        | _ => inl (Null label)
                                                        end
                                                      | _ => inl (Null label)         
                                                      end
           | InlineFragment t ϕ => match lookup_type schema t with
                                   | Some (ObjectTypeDefinition _ _ _) => if t == u.(type) then
                                                                            inr (eval schema graph u ϕ)
                                                                          else
                                                                            inr (Results [::])
                                   | Some (InterfaceTypeDefinition _ _) => if declares_implementation schema u.(type) t then
                                                                             inr (eval schema graph u ϕ)
                                                                           else
                                                                             inr (Results [::])
                                   | Some (UnionTypeDefinition _ mbs) => if u.(type) \in mbs then
                                                                           inr (eval schema graph u ϕ)
                                                                         else
                                                                           inr (Results [::])
                                   | _ => inr (Results [::])
                                   end
           end.


    Definition eval_query_set schema  (g : @conformedGraph N Name Vals schema) (selection : @conformedQuery Name Vals schema) : @Result Name Vals :=
      let: ConformedQuery selection _ := selection in
      eval schema g.(graph) g.(graph).(root) selection.

    
    

End QuerySemantic.