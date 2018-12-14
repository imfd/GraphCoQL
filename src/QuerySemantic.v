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
  


  Fixpoint indexed_β_filter (response : @ResponseObject Name Vals) (filter :  @ResponseObject Name Vals) (index : nat) : seq ResponseObject :=
    match response, filter with
    | NestedListResult l rs, NestedListResult l' rs' => if l == l' then
                                                         let res := nth Empty rs index in
                                                         if res is ResponseList χ then χ else [::]
                                                         
                                                       else
                                                         [::]
    | _, _ => [::]
    end.

  
  Fixpoint β_filter (filter : @ResponseObject Name Vals) (responses : seq (@ResponseObject Name Vals)) : seq ResponseObject :=
    match responses with
    | [::] => responses
    | hd :: tl =>
      match hd, filter with
      | NestedResult l χ, NestedResult l' _ => if (l == l') then χ :: (β_filter filter tl) else (β_filter filter tl)
      | _, _ => β_filter filter tl
      end
    end.

  Fixpoint γ_filter (filter_response : ResponseObject) (responses : seq ResponseObject) : seq (@ResponseObject Name Vals) :=
    match responses with
    | [::] => [::]
    | response :: tl =>
      match response, filter_response with
      | NestedResult l _, NestedResult l' _ => if l == l' then γ_filter filter_response tl else response :: (γ_filter filter_response tl)
      | NestedListResult l _, NestedListResult l' _ => if l == l' then γ_filter filter_response tl else response :: (γ_filter filter_response tl)
      | ResponseList rs, _ => response :: (γ_filter filter_response tl)
      | _, _ => if response == filter_response then (γ_filter filter_response tl) else response :: (γ_filter filter_response tl)
      end
    end.
  
  
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
      case: x; case: r IH; intros; crush; case (_ == _) => //=.
  Admitted.

  Lemma γ_reduce_one : forall l r x, γ_filter r (x :: l) = γ_filter r l \/  γ_filter r (x :: l) = x :: γ_filter r l.
  Proof.
    elim=> [| r' l' IH] //=; intros.
  Admitted.
  
  Lemma γ_responses_size_reduced : forall l r, responses_size (γ_filter r l) <= responses_size l.
  Proof.
    elim=> [| x l' IH].
      by [].
      move=> r; move: (γ_reduce_one l' r x) => [H1 | H2].
        rewrite H1; have: responses_size (γ_filter r l') <= responses_size (l').
          apply: (IH r).
          rewrite /responses_size /=; case (response_size x); crush.
        rewrite H2; have: responses_size (γ_filter r l') <= responses_size (l').
          apply: (IH r).
          intros; rewrite /responses_size; case (response_size x); crush.     
  Qed.

    Lemma β_responses_size_reduced : forall r l, responses_size (β_filter r l) <= responses_size l.
  Proof.
    move=> r; elim=> [| x l' IH] //=.
      crush.
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


  Lemma response_size_gt_0 : forall (r : @ResponseObject Name Vals), 0 < response_size r.
  Proof. case; crush. Qed.
  

      
  Function collect (responses : seq ResponseObject) {measure (fun r => responses_size r) responses}: seq ResponseObject :=
    match responses with
    | [::] => responses
    | hd :: tl =>
      let γ_filtered := γ_filter hd tl in
      match hd with
      | NestedResult l σ => (NestedResult l (ResponseList (collect (σ :: (β_filter hd tl))))) :: (collect (γ_filter hd tl))
      | NestedListResult l rs => (NestedListResult l
                                  (collect (indexed_map
                                              (fun i r => if r is ResponseList rs' then
                                                         ResponseList (rs' ++ (flatten (map
                                                                                 (fun r' => indexed_β_filter r' hd i) tl)))
                                                       else
                                                         Empty) rs)))
                                  :: (collect (γ_filter hd tl))

                                  (* Esto supone que estamos en el caso de una query bien formada, donde el único punto donde collect se puede encontrar con ResponseList es en una NestedListResult *)
      | ResponseList ρ => (ResponseList (collect ρ)) :: (collect tl)
      | _ => hd :: (collect (γ_filter hd tl))
      end
    end.
  Proof.
    Admitted. (*
   - by intros; rewrite /responses_size; crush; apply: Lt.le_lt_n_Sm; apply: γ_responses_size_reduced.
   - intros; rewrite /responses_size /=.
     have:  sumn [seq response_size r | r <- γ_filter (s <- null) tl] <= sumn [seq response_size r | r <- tl].
       by apply: γ_responses_size_reduced.
       intros. crush.
       crush.
   - intros; rewrite /responses_size /=.
     have: sumn [seq response_size r | r <- γ_filter (s <- s0) tl] <= sumn [seq response_size r | r <- tl].
       by apply: γ_responses_size_reduced.
       crush.
   - intros; rewrite /responses_size /=.
     have: sumn [seq response_size r | r <- γ_filter (s <<- l) tl] <= sumn [seq response_size r | r <- tl].
       by apply: γ_responses_size_reduced.
       crush.
   - intros; rewrite /responses_size /=.
     have: sumn [seq response_size r | r <- γ_filter (l <- {{σ}}) tl] <= sumn [seq response_size r | r <- tl].
       by apply: γ_responses_size_reduced.
       crush.
   - intros; rewrite /responses_size /=.
     have: sumn [seq response_size r | r <- β_filter (l <- {{σ}}) tl] <= sumn [seq response_size r | r <- tl].
       by apply: β_responses_size_reduced.
       crush.
   - intros; rewrite /responses_size /=.
     have: sumn [seq response_size r | r <- γ_filter (l <<- [{rs}]) tl] <= sumn [seq response_size r | r <- tl].
       by apply: γ_responses_size_reduced.
       crush.
   - intros. rewrite /responses_size. Admitted. *)
  

     
      
      
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
                                      NestedListResult name (map (fun v =>
                                                                               let res := eval schema g v ϕ in 
                                                                               if res is ResponseList _ then
                                                                                 res
                                                                               else
                                                                                 ResponseList [:: res]) target_nodes)
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
                                                NestedListResult label (map (fun v =>
                                                                               let res := eval schema g v ϕ in 
                                                                               if res is ResponseList _ then
                                                                                 res
                                                                               else
                                                                                 ResponseList [:: res]) target_nodes)
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
    | SelectionSet ϕ => ResponseList (collect (map (eval schema g u) ϕ))
    end.


      Definition eval_query (schema : @wfSchema Name Vals)  (g : @conformedGraph N Name Vals schema) (query : @conformedQuery Name Vals schema) : @ResponseObject Name Vals :=
        let: ConformedQuery (WFQuery query _) _ := query in
        eval schema g.(graph) g.(graph).(root) query.

      
      

End QuerySemantic.