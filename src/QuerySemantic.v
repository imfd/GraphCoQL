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

Require Recdef.

Section QuerySemantic.

  Variables N Name Vals : ordType.

    Open Scope coq_nat.

  
  Lemma t : forall n x, n < 1 + n + x.
  Proof. crush. Qed.

  

  Lemma asdf : forall (n : nat) (m : {m : nat | 0 < m}),  n < `m + n.
  Proof. move=> n m; case: m; crush. Qed.

  Hint Resolve  t asdf.
  
  Definition responses_size (responses : seq (@ResponseObject Name Vals)) : nat :=
    sumn (map (fun r => proj1_sig (response_size r)) responses).



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
  Fixpoint β_filter (filter_response response : @ResponseObject Name Vals) : @ResponseObject Name Vals :=
    match response, filter_response with
    | NestedResult l χ, NestedResult l' _ => if (l == l') then χ else Empty
    | ResponseList rs, _ => ResponseList (map (β_filter filter_response) rs)
    | _, _ => Empty
    end.
   *)
  
  Function β_filter (filter : @ResponseObject Name Vals) (responses : seq (@ResponseObject Name Vals)) {measure (fun r => responses_size r) responses} : seq ResponseObject :=
    match responses with
    | [::] => responses
    | hd :: tl =>
      let β_filtered := (β_filter filter tl) in 
      match hd, filter with
      | NestedResult l χ, NestedResult l' _ => if (l == l') then χ :: β_filtered else β_filtered
      | ResponseList rs, _ => (ResponseList (β_filter filter rs)) :: β_filtered
      | _, _ => β_filter filter tl
      end
    end.
  Proof. 
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
  Qed.

  

  Function γ_filter (filter_response : ResponseObject) (responses : seq ResponseObject) {measure (fun r => (responses_size r)) responses} : seq (@ResponseObject Name Vals) :=
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
  Proof.    
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.    
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.    
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
    intros; crush; rewrite /responses_size; crush.
  Qed.
  
  
  
  About γ_filter.
  Check γ_filter.
  Check γ_filter_equation.
  Print γ_filter.
  
  Notation "'ϵ'" := Empty.
  Notation "l <- 'null'" := (Null l) (at level 50).
  Notation "l <- v" := (SingleResult l v) (at level 50).
  Notation "l <<- vals" := (ListResult l vals) (at level 50).
  Notation "l <- {{ ρ }}" := (NestedResult l ρ) (at level 40). 
  Notation "l <<- [{ ρ }]" := (NestedListResult l ρ) (at level 40).
  Notation "[- ρ -]" := (ResponseList ρ) (at level 40).



  Lemma γ_size_reduced : forall r l, size (γ_filter r l) <= size l.
  Proof.
    move=> r; elim=> [| x l' IH] //=.
      by rewrite γ_filter_equation /=.
      case: x; case: r IH; intros; rewrite γ_filter_equation //=; crush; case (_ == _) => //=.
  Admitted.

  Lemma γ_responses_size_reduced : forall r l, responses_size (γ_filter r l) <= responses_size l.
  Proof.
    move=> r; elim=> [| x l' IH] //=.
      by rewrite γ_filter_equation /=.
  Admitted.

    Lemma β_responses_size_reduced : forall r l, responses_size (β_filter r l) <= responses_size l.
  Proof.
    move=> r; elim=> [| x l' IH] //=.
      by rewrite β_filter_equation /=.
      Admitted.
      
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


  Lemma alkl : forall r : { m : nat | 0 < m}, 0 < proj1_sig r + 0.
  Proof. case=> /=; crush. Qed.
  
  Lemma qwe : forall r l, responses_size l < responses_size (r :: l).
  Proof.
    move=> r; case=> //=; rewrite /responses_size /=; case (response_size r); crush.
  Qed.

      
  Hint Resolve γ_size_reduced γ_responses_size_reduced β_responses_size_reduced qwe.

  Obligation Tactic := rewrite /responses_size; crush.
  Program Fixpoint collect_list (responses : seq ResponseObject) {measure (responses_size responses)}: seq ResponseObject :=
    match responses with
    | [::] => responses
    | hd :: tl =>
      let γ_filtered := γ_filter hd tl in
      match hd with
      | Empty => hd :: (collect_list γ_filtered)
      | NestedResult l σ => (NestedResult l (ResponseList (collect_list (σ :: (β_filter hd tl))))) :: (collect_list γ_filtered)
      | NestedListResult l rs => (NestedListResult l (indexed_map (fun i r => ResponseList (map (fun r' => indexed_β_filter r' r i) tl)) rs)) :: (collect_list γ_filtered)
      | ResponseList ρ => collect_list ρ
      | _ => hd :: (collect_list γ_filtered)
      end
    end.
  Next Obligation.
    by apply: Lt.le_lt_n_Sm; apply: γ_responses_size_reduced. 
  Qed.
  Next Obligation.
    have: sumn [seq ` (response_size r) | r <- β_filter (l <- {{σ}}) tl] <= sumn [seq ` (response_size r) | r <- tl].
    apply: β_responses_size_reduced.
    intros; crush.
  Qed.
  Next Obligation.
    have: sumn [seq ` (response_size r) | r <- γ_filter (l <- {{σ}}) tl] <= sumn [seq ` (response_size r) | r <- tl]. apply: γ_responses_size_reduced. 
    intros; crush.
  Qed.
  Next Obligation.
    have: sumn [seq ` (response_size r) | r <- γ_filter (l <<- [{rs}]) tl] <= sumn [seq ` (response_size r) | r <- tl].
      by apply: γ_responses_size_reduced.
    intros; crush.
  Qed.
  Next Obligation.
    have: sumn [seq ` (response_size r) | r <- γ_filter hd tl] <= sumn [seq ` (response_size r) | r <- tl].
      by apply: γ_responses_size_reduced.
      intros; case (response_size hd); crush.
  Qed.

      
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
    | SelectionSet ϕ ϕ' => collect (ResponseList [:: (eval schema g u ϕ); (eval schema g u ϕ')])
    end.


      Definition eval_query (schema : @wfSchema Name Vals)  (g : @conformedGraph N Name Vals schema) (query : @wfQuery Name Vals schema) : @ResponseObject Name Vals :=
        let: WFQuery query _ := query in
        eval schema g.(graph) g.(graph).(root) query.

      
      

End QuerySemantic.