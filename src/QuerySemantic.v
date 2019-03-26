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
  
 
  
  Section Aux.    
    Variables (T1 T2 : Type).
    
   
      
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
       indexed_map s f := indexed_map_In s f 0
    
    where indexed_map_In s (f : forall (i : nat) (x : T1), In x s -> T2) (index : nat) : seq T2 :=
            { 
              indexed_map_In [::] _ _ := [::];
              indexed_map_In (hd :: tl) f i := (f i hd _) :: (indexed_map_In tl (fun i x H => f i x _) i.+1)
            }.
    
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
      
      Equations indexed_β_filter (responses : seq.seq (@ResponseObject Name Vals)) (filter :  @ResponseObject Name Vals) (index : nat) : seq.seq (@ResponseObject Name Vals) :=
        {
          indexed_β_filter [::] _ _ := [::];
          indexed_β_filter (cons hd tl) filter index :=
            (β_aux hd filter index) ++ (indexed_β_filter tl filter index)
            where β_aux (result flt : @ResponseObject Name Vals) (i : nat) : seq.seq (@ResponseObject Name Vals) :=
                    {
                      β_aux (NestedListResult l rs) (NestedListResult l' rs') i with l == l' :=
                        {
                        | true := get_nth [::] rs i;
                        | false => [::]
                        };
                      β_aux _ _ _ := [::]
                    }
        }.
    
    

      (** Auxiliary lemmas **)
      
    
  
      Lemma indexed_β_size_reduced (lst : seq.seq ResponseObject) (r : ResponseObject) (i : nat) :
        responses_size (indexed_β_filter lst r i) <= responses_size lst.
      Proof.
        apply (@indexed_β_filter_elim (fun rsp flt index res => responses_size res <= responses_size rsp)
                                      (fun hd tl flt index r1 r2 i res => responses_size res <= response_size r1)) => //.
        - move=> hd tl flt index IH IH'.
          rewrite responses_size_app /=. ssromega.
        -  move=> l1 l2 hd tl flt index rs rs' i'.
          
          funelim (get_nth [::] rs i') => //= Heq.
          simp response_size. ssromega.
          simp response_size.
          rewrite [responses_size t + _]addnC. 
          rewrite two_times_Sn; rewrite [4 + (2 * size l + 2)]addnA.
          rewrite -addnA -[2 + _]addnCA addnA; rewrite -[4 + 2 * size l + responses_size' l]/(response_size (NestedListResult l1 l)).
            by move: (H lst r i l1 l2 hd tl flt index rs' Heq ) => *; apply: leq_addr. 
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

      Definition partial_response_eq (r1 r2 : @ResponseObject Name Vals) : bool :=
        match r1, r2 with
        | (SingleResult l v), (SingleResult l' v') => (l == l') && (v == v')
        | (ListResult l v), (ListResult l' v') => (l == l') && (v == v')
        | (Null l), (Null l') => l == l'
        | (NestedResult l _), (NestedResult l' _) => l == l' 
        | (NestedListResult l _), (NestedListResult l' _) => l == l'   
        | _, _ => false
        end.
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

      Definition γ_filter (flt : @ResponseObject Name Vals) (responses : seq.seq (@ResponseObject Name Vals)) : seq.seq (@ResponseObject Name Vals) :=
        filter (fun r => ~~partial_response_eq flt r) responses.
      



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
                                 (collect (r ++ (indexed_β_filter tl (NestedListResult l rs) i))))))
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
  
  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type graph : @graphQLGraph Name Vals.
  Implicit Type u : @node Name Vals.
  Implicit Type query : @Query Name Vals.

  (*
  Fixpoint eval schema graph u query : seq.seq ResponseObject :=
    match query with
    | SingleField name args => match u.(fields) (Field name args) with
                              | Some (inl value) =>  [:: SingleResult name value]
                              | _ => [:: Null name]
                              end
    | LabeledField label name args =>  match u.(fields) (Field name args) with
                                      | Some (inl value) => [:: SingleResult label value]
                                      | _ => [:: Null label]
                                      end
    | NestedField name args ϕ => let target_nodes := get_target_nodes_with_field graph u (Field name args) in
                                match lookup_field_type schema u.(type) name with
                                | Some (ListType _) =>
                                  [:: NestedListResult name [seq (eval_queries schema graph v ϕ) | v <- target_nodes]]
                                    
                                | Some (NT _) =>
                                  match ohead target_nodes with
                                  | Some v => [:: NestedResult name (eval_queries schema graph v ϕ)]
                                  | _ =>  [:: Null name]
                                  end
                                | _ => [:: Null name]         (* If the field ∉ fields(u) then it's null, right? *)
                                end
                                    
    | NestedLabeledField label name args ϕ =>  let target_nodes := get_target_nodes_with_field graph u (Field name args) in
                                              match lookup_field_type schema u.(type) name with
                                              | Some (ListType _) =>
                                                [:: NestedListResult label [seq (eval_queries schema graph v ϕ) | v <- target_nodes]]
                                              | Some (NT _) =>
                                                match ohead target_nodes with
                                                | Some v => [:: NestedResult label (eval_queries schema graph v ϕ)]
                                                | _ => [:: Null label]
                                                end
                                              | _ => [:: Null label]
                                              end
    | InlineFragment t ϕ => match lookup_type schema t with
                           | Some (ObjectTypeDefinition _ _ _) => if t == u.(type) then
                                                                   (eval_queries schema graph u ϕ)
                                                                 else
                                                                   [::]
                           | Some (InterfaceTypeDefinition _ _) => if declares_implementation schema u.(type) t then
                                                                   (eval_queries schema graph u ϕ)
                                                                  else
                                                                    [::]
                           | Some (UnionTypeDefinition _ mbs) => if u.(type) \in mbs then
                                                                   (eval_queries schema graph u ϕ)
                                                                else
                                                                  [::]
                           | _ =>  [::]
                           end
    end
  with
  eval_queries schema graph u (queries : seq (@Query Name Vals)) {struct queries} : seq (@ResponseObject Name Vals) :=
    match queries with
    | [::] => [::]
    | query :: [::] => eval schema graph u query
    | query :: (hd :: tl) => collect ((eval schema graph u query) ++ (eval schema graph u hd) ++ (eval_queries schema graph u tl))
    end.
   *)
  
  Equations eval schema graph u query : seq.seq (@ResponseObject Name Vals) :=
    {
      eval schema graph u (SingleField name args)
        with u.(fields) (Field name args) :=
        {
        | Some (inl value) =>  [:: SingleResult name value];
        | _ => [:: Null name]
        };
      
      eval schema graph u (LabeledField label name args)
        with u.(fields) (Field name args) :=
        {
        | Some (inl value) => [:: SingleResult label value];
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
        with lookup_type schema t :=
        {
        | Some (ObjectTypeDefinition _ _ _) := if t == u.(type) then
                                                eval_queries schema graph u ϕ
                                              else
                                                [::];
        | Some (InterfaceTypeDefinition _ _) := if declares_implementation schema u.(type) t then
                                                 eval_queries schema graph u ϕ
                                               else
                                                 [::];
        | Some (UnionTypeDefinition _ mbs) := if u.(type) \in mbs then
                                               eval_queries schema graph u ϕ
                                             else
                                               [::];
        | _ =>  [::]
        }
    }
  where
  eval_queries schema graph u (queries : seq (@Query Name Vals)) : seq (@ResponseObject Name Vals) :=
    {
      eval_queries _ _ _ [::] := [::];
      eval_queries schema graph u (cons query nil) := eval schema graph u query;
      eval_queries schema graph u (cons query (cons hd tl)) := collect ((eval schema graph u query) ++ (eval schema graph u hd) ++ (eval_queries schema graph u tl))
    }.

  (*
  Definition eval_queries schema graph u (queries : seq.seq Query) : seq.seq ResponseObject :=
    collect (flatten (map (eval schema graph u) queries)).
   *)

  Lemma eval_single_field schema graph u f α :
    (exists v, eval schema graph u (SingleField f α) = [:: SingleResult f v]) \/
    eval schema graph u (SingleField f α) = [:: Null f].
  Proof.
    rewrite eval_equation_1.
    case Hv : (u.(fields) (Field f α)) => [val|]; last by right.
    case: val Hv => val Hv.
      by left; exists val.
      by right.
  Qed.

    Lemma eval_labeled_field schema graph u l f α :
    (exists v, eval schema graph u (LabeledField l f α) = [:: SingleResult l v]) \/
    eval schema graph u (LabeledField l f α) = [:: Null l].
  Proof.
    rewrite eval_equation_2.
    case Hv : (u.(fields) (Field f α)) => [val|]; last by right.
    case: val Hv => val Hv.
      by left; exists val.
      by right.
  Qed.
  

  Lemma eval_single_field_size_1 schema graph u f α :
    size (eval schema graph u (SingleField f α)) = 1.
  Proof.
    move: (eval_single_field schema graph u f α) => [| ->] //.
      by case=> v ->.
  Qed.

  Lemma collect_app_nil r :
    collect (r ++ [::]) = collect r.
  Proof.
      by rewrite cats0.
  Qed.

  Lemma gamma_filter_single_result_null f f' v (lst : seq (@ResponseObject Name Vals)) :
    γ_filter (SingleResult f v) ((Null f') :: lst) = (Null f') :: γ_filter (SingleResult f v) lst. Proof. done. Qed.

  
  Lemma collect_single_result l v :
    collect [:: (SingleResult l v)] = [:: (SingleResult l v)].
  Proof. done. Qed.

  Lemma collect_null_result l :
    collect [:: Null l] = [:: Null l].
  Proof. done. Qed.


 (* Lemma collect_nested_result l r :
    collect [:: NestedResult l r] = [:: NestedResult l (collect r)].
  Proof.
    funelim (collect [:: NestedResult l r]) => //=.
      by rewrite collect_equation_1 collect_app_nil.
  Qed. *)

  Lemma collect_nested_list_result (l : Name) (r : seq (seq (@ResponseObject Name Vals))) :
    collect [:: NestedListResult l r] = [:: NestedListResult l (map collect r)].
  Proof.
  Admitted.
  

  

  
  Lemma collect_collect_same (r : seq (@ResponseObject Name Vals)) :
    collect r = collect (collect r).
  Proof.
  Admitted.

  Lemma eval_same_query_in_list schema graph u query :
    eval schema graph u query = eval_queries schema graph u [:: query].
  Proof. done. Qed.

  Lemma eval_query_inline schema (g : conformedGraph schema) qs :
    eval schema g g.(root) (InlineFragment schema.(query_type) qs) = eval_queries schema g g.(root) qs.
  Proof.
    simp eval.
    move: (query_has_object_type schema) => /is_object_type_E [obj [intfs [flds Hlook]]].
    rewrite Hlook /=.
    move: (root_query_type g) => -> /=.
    case: ifP => //; case/eqP => //.
  Qed.
    


  Lemma inline_nested_empty schema (g : @conformedGraph Name Vals schema) :
    forall t1 t2 ϕ,
      is_object_type schema t1 ->
      is_object_type schema t2 ->
      t1 <> t2 ->
      eval schema g g.(root) (InlineFragment t1 [:: (InlineFragment t2 ϕ)]) = [::].
  Proof.
    move=> t1 t2 ϕ.
    funelim (is_object_type schema t1) => //.
    funelim (is_object_type schema t2) => //.
    move=> _ _ Hdiff.
    rewrite eval_equation_5 Heq0.
    rewrite /eval_queries /= eval_equation_5 Heq.
    case: eqP => //= <-.
    case: eqP => // H.
    by rewrite H in Hdiff.
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
    rewrite eval_equation_5 Heq /=.
    by case: ifP => // /eqP.
  Qed.

  Lemma asf schema (g : @conformedGraph Name Vals schema)  u type_in_scope ti ϕ :
     query_conforms schema type_in_scope (InlineFragment ti ϕ) ->
     type_in_scope \in implementation schema ti ->
            eval schema g u (InlineFragment ti ϕ) = eval schema g u (InlineFragment type_in_scope ϕ). 
  Proof.
    move=> Hqc Himpl.
    move: (has_implementation_is_interface Himpl) => Hint.
    rewrite !eval_equation_5.
    funelim (is_interface_type schema ti) => //.
    rewrite Heq.
    move: (in_implementation_is_object Himpl) => /is_object_type_E [obj [intfs [flds Hlook]]].
    rewrite Hlook /=.
    case: ifP => //.
    Abort.
  (* Missing info on node -> type of node should be same as the one in scope *)
  

  
  

  Lemma nf_queries_eq schema (g : @conformedGraph Name Vals schema) u n α ϕ ϕ' :
    (forall v, eval_queries schema g v ϕ = eval_queries schema g v ϕ') ->
    eval schema g u (NestedField n α ϕ) = eval schema g u (NestedField n α ϕ').
  Proof.
    move=> Hqs.
    do 2 rewrite eval_equation_3.
    case lookup_field_type => //.
    case=> [nt | lt].
    case neighbours_with_field => // v1 vn /=.
    case ohead => // node.
      by move: (Hqs node) => ->. 
    case neighbours_with_field => // v1 vn /=.
    congr cons.
    congr NestedListResult.
    
  Admitted.
    
End QuerySemantic.