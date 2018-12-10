From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord fmap.


Require Import SchemaWellFormedness.
Require Import GraphConformance.
Require Import QueryConformance.
Require Import SchemaAux.
Require Import GraphAux.
Require Import QueryAux.

Require Import Schema.
Require Import Query.
Require Import Graph.


Require Import CpdtTactics.

Require Import Program.
Require Import Omega.
Require Import Extraction.

Section QuerySemantic.

  Variables N Name Vals : ordType.

  
  (*Definition response_size_order (r1 r2 : @ResponseObject Name Vals) : Prop :=
    response_size r1 < response_size r2.

  Hint Constructors Acc.

  Lemma response_size_order_wf' : forall len r, response_size r <= len -> Acc response_size_order r.
  Proof.
    rewrite /response_size_order; elim.
    move=> rs; rewrite leqn0; move/eqP=> H.
    apply Acc_intro; rewrite H => y H'; inversion H'.
    move=> n IH r H; apply Acc_intro => y Hl.
    apply: IH; move: (leq_trans Hl H); auto.
  Defined.
  
  Theorem response_size_order_wf : well_founded response_size_order.
  Proof.
    red; intro; eapply response_size_order_wf'; eauto.
  Defined.*)



  Fixpoint indexed_β_filter (response : @ResponseObject Name Vals) (filter :  @ResponseObject Name Vals) (index : nat) : ResponseObject :=
    match response, filter with
    | NestedListResult l rs, NestedListResult l' rs' => if l == l' then
                                                         nth Empty rs index
                                                       else
                                                         Empty
    | ResponseList rs, NestedListResult _ _ => ResponseList (map (fun r => (indexed_β_filter r filter index)) rs)
    | _, _ => Empty
    end.
  (*
    Fixpoint indexed_β_filter (response : @ResponseObject Name Vals) (indexed_result : nat * @ResponseObject Name Vals) : ResponseObject :=
    match response, indexed_result with
    | NestedListResult l rs, (i, NestedListResult l' rs') => if l == l' then
                                                              nth Empty rs i
                                                            else
                                                              Empty
    | _, _ => Empty
    end.
   *)                                             
  Fixpoint β_filter (filter_response response : @ResponseObject Name Vals) : @ResponseObject Name Vals :=
    match response, filter_response with
    | NestedResult l χ, NestedResult l' _ => if (l == l') then χ else Empty
    | ResponseList rs, _ => ResponseList (map (β_filter filter_response) rs)
    | _, _ => Empty
    end.

  
  Lemma t : forall n x, n < 1 + n + x.
  Proof. crush. Qed.

  

  Lemma asdf : forall (n : nat) (m : {m : nat | 0 < m}),  n < `m + n.
  Proof. move=> n m; case: m; crush. Qed.

  Hint Resolve  t neq_0_lt asdf.
  
  Definition responses_size (responses : seq (@ResponseObject Name Vals)) : nat :=
    sumn (map (fun r => proj1_sig (response_size r)) responses).

  Open Scope coq_nat.

  Obligation Tactic := crush.
  Program Fixpoint γ_filter (filter_response : ResponseObject) (responses : seq ResponseObject) {measure (responses_size responses)} : seq (@ResponseObject Name Vals) :=
    match responses with
    | [::] => [::]
    | response :: tl =>
      let γ_filtered := γ_filter filter_response tl in
      match response, filter_response with
      | NestedResult l _, NestedResult l' _ => if l == l' then γ_filtered else response :: γ_filtered
      | NestedListResult l _, NestedListResult l' _ => if l == l' then γ_filtered else response :: γ_filtered
      | ResponseList rs, _ => (ResponseList (γ_filter filter_response rs)) :: γ_filtered
      | _, _ => if response == filter_response then γ_filtered else response :: γ_filtered
      end
    end.
  Next Obligation.
    rewrite /responses_size /=; case (response_size response); crush.
  Defined.
  Next Obligation.
    rewrite /responses_size /=; crush.
  Defined.

  
  About γ_filter.
  Check γ_filter.
  Print γ_filter.
  Notation "'ϵ'" := Empty.
  Notation "l <- 'null'" := (Null l) (at level 50).
  Notation "l <- v" := (SingleResult l v) (at level 50).
  Notation "l <<- vals" := (ListResult l vals) (at level 50).
  Notation "l <- {{ ρ }}" := (NestedResult l ρ) (at level 40). 
  Notation "l <<- [{ ρ }]" := (NestedListResult l ρ) (at level 40).
  Notation "[- ρ -]" := (ResponseList ρ) (at level 40).

  Variables (l : Name) (v : Vals).
  Eval compute in proj1_sig (response_size ([- [:: (l <- v)] -])).
  
  Eval compute in (γ_filter (l <- v) [:: (l <- v)]).

  
  Section Map.
    
    Variables (T1 T2 : Type) (x2 : T2) (f : nat -> T1 -> T2) (s : seq T1).
    Definition indexed_map s :=
      let fix imap (f : nat -> T1 -> T2) (s : seq T1) i {struct s} : seq T2 :=
          if s is hd :: tl then (f i hd) :: imap f tl (i + 1) else [::]
      in
      imap f s 0.

  End Map.
  
  Example sum_index : indexed_map (fun i x => x + i) [:: 1; 2; 3] = [:: 1; 3; 5].
  Proof. by []. Qed.


  Lemma γ_empty_preserves : forall l, γ_filter ϵ l = l.
  Proof.
    elim=> [| r rs IH] //=.
    rewrite /γ_filter. 
    elim=> [| r rs IH] //.
    case: r => //=.
    move=> rs' /=. rewrite /γ_filter.
    
    Open Scope coq_nat.
    Program Fixpoint collect_list (responses : seq ResponseObject) {measure (size responses)}: seq ResponseObject :=
      match responses with
      | [::] => responses
      | hd :: tl =>
        let γ_filtered := (γ_filter hd) tl in
        match hd with
        | Empty => hd :: (collect_list γ_filtered)
        | NestedResult l σ => (NestedResult l (ResponseList (collect_list (σ :: (map (β_filter hd) tl))))) :: (collect_list γ_filtered)
        | NestedListResult l rs => (NestedListResult l (indexed_map (fun i r => ResponseList (map (fun r' => indexed_β_filter r' r i) tl)) rs)) :: (collect_list γ_filtered)
        | ResponseList ρ => collect_list ρ
        | _ => hd :: (collect_list γ_filtered)
        end
      end.
    Next Obligation.
      simpl. rewrite γ_empty_preserves. case: tl collect_list => [| r rs collect_list] //.
        by move=> _.
        
        
        Admit Obligations.

        
        Fixpoint collect (response : @ResponseObject Name Vals) : @ResponseObject Name Vals :=
          match response with
          | ResponseList rs => ResponseList (collect_list rs)                         
          | _ => response
          end.
        
        
        Fixpoint eval (schema : @wfSchema Name Vals)  (g : graphQLGraph) (u : @node N Name Vals) (query : Query) : @ResponseObject Name Vals :=
          match query with
          | SingleField name args => match u.(fields) (Field name args) with
                                    | Some (inl value) => SingleResult name value
                                    | _ => Null name
                                    end
          | LabeledField label name args =>  match u.(fields) (Field name args) with
                                             | Some (inl value) => SingleResult label value
                                             | _ => Null name
                                             end
          | NestedField name args ϕ => let target_nodes := get_target_nodes_with_field g u (Field name args) in
                                       match lookup_field_type schema (NamedType u.(type)) name with
                                       | Some (ListType _) =>
                                         NestedListResult name (map (fun v => eval schema g v ϕ) target_nodes)
                                       | Some (NamedType _) =>
                                         match ohead target_nodes with
                                         | Some v => (NestedResult name (eval schema g v ϕ))
                                         | _ => Null name
                                         end
                                       | _ => Null name         (* If the field ∉ fields(u) then it's null, right? *)
                                       end
                                         
          | NestedLabeledField label name args ϕ =>  let target_nodes := get_target_nodes_with_field g u (Field name args) in
                                                     match lookup_field_type schema (NamedType u.(type)) name with
                                                     | Some (ListType _) =>
                                                       NestedListResult label (map (fun v => eval schema g v ϕ) target_nodes)
                                                     | Some (NamedType _) =>
                                                       match ohead target_nodes with
                                                       | Some v => (NestedResult label (eval schema g v ϕ))
                                                       | _ => Null name
                                                       end
                                                     | _ => Null name         
                                                     end
          | InlineFragment t ϕ => match lookup_type schema (NamedType t) with
                                  | Some (ObjectTypeDefinition _ _ _) => if t == u.(type) then
                                                                           eval schema g u ϕ
                                                                         else
                                                                           Empty
                                  | Some (InterfaceTypeDefinition _ _) => if declares_implementation schema (NamedType u.(type)) (NamedType t) then
                                                                            eval schema g u ϕ
                                                                          else
                                                                            Empty
                                  | Some (UnionTypeDefinition _ mbs) => if (NamedType u.(type)) \in mbs then
                                                                          eval schema g u ϕ
                                                                        else
                                                                          Empty
                                  | _ => Empty
                                  end
          | SelectionSet ϕ ϕ' => collect (ResponseList (eval schema g u ϕ) (eval schema g u ϕ'))
          end.


        Definition eval_query (schema : @wfSchema Name Vals)  (g : @conformedGraph N Name Vals schema) (query : @wfQuery Name Vals schema) : @ResponseObject Name Vals :=
          let: WFQuery query _ := query in
          eval schema g.(graph) g.(graph).(root) query.

        
        

End QuerySemantic.