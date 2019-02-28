Require Import List.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Asymmetric Patterns.

From Equations Require Import Equations.
From extructures Require Import ord fmap.


Require Import treeordtype.
Require Import Schema.
Require Import SchemaAux.


Require Import CpdtTactics.


Delimit Scope query_scope with QUERY.
Open Scope query_scope.


Section Forallt.
    Inductive Forallt {A : Type} (P : A -> Type) : list A -> Type :=
      Forallt_nil : Forallt P nil
    | Forallt_cons : forall (x : A) (l : list A),
        P x -> Forallt P l -> Forallt P (x :: l).

End Forallt.

Section Query.
  
  Variables Name Vals : ordType.

  Unset Elimination Schemes.
  Inductive Query : Type :=
  | SingleField : Name -> {fmap Name -> Vals} -> Query
  | LabeledField : Name -> Name -> {fmap Name -> Vals} -> Query
  | NestedField : Name -> {fmap Name -> Vals} -> seq Query -> Query
  | NestedLabeledField : Name -> Name -> {fmap Name -> Vals} -> seq Query -> Query
  | InlineFragment : @NamedType Name -> seq Query -> Query.


  Inductive ResponseObject : Type :=
  | Null : Name -> ResponseObject
  | SingleResult : Name -> Vals -> ResponseObject
  | ListResult : Name -> seq Vals -> ResponseObject
  | NestedResult : Name -> seq ResponseObject -> ResponseObject
  | NestedListResult : Name -> seq (seq ResponseObject) -> ResponseObject.
  
  Set Elimination Schemes.
  
  Definition Query_rect (P : Query -> Type)
             (Pl : seq Query -> Type)
             (IH_SF : forall n α, P (SingleField n α))
             (IH_LF : forall l n α, P (LabeledField l n α))
             (IH_NF : forall n α ϕ, Pl ϕ -> P (NestedField n α ϕ))
             (IH_NLF : forall l n α ϕ, Pl ϕ -> P (NestedLabeledField l n α ϕ))
             (IH_IF : forall t ϕ, Pl ϕ -> P (InlineFragment t ϕ))
             (IH_Nil : Pl [::])
             (IH_Cons : forall q, P q -> forall qs, Pl qs -> Pl (q :: qs))
    :=
    fix loop query : P query :=
      let fix F (qs : seq Query) : Pl qs :=
          match qs with
          | [::] => IH_Nil
          | hd :: tl => IH_Cons hd (loop hd) tl (F tl)
          end
      in
      match query with
      | SingleField n α => IH_SF n α
      | LabeledField l n α => IH_LF l n α
      | NestedField n α ϕ => IH_NF n α ϕ (F ϕ)
      | NestedLabeledField l n α ϕ => IH_NLF l n α ϕ (F ϕ)
      | InlineFragment t ϕ => IH_IF t ϕ (F ϕ)
      end.

  Definition Query_rec (P : Query -> Set) := @Query_rect P.

  Definition Query_ind (P : Query -> Prop)
             (Pl : seq Query -> Prop)
            (IH_SF : forall n α, P (SingleField n α))
            (IH_LF : forall l n α, P (LabeledField l n α))
            (IH_NF : forall n α ϕ, Pl ϕ -> P (NestedField n α ϕ))
            (IH_NLF : forall l n α ϕ, Pl ϕ -> P (NestedLabeledField l n α ϕ))
            (IH_IF : forall t ϕ, Pl ϕ -> P (InlineFragment t ϕ))
            (IH_Nil : Pl [::])
            (IH_Cons : forall q, P q -> forall qs, Pl qs -> Pl (q :: qs))
    :=
      fix loop query : P query :=
        let fix F (qs : seq Query) : Pl qs :=
          match qs with
          | [::] => IH_Nil
          | hd :: tl => IH_Cons hd (loop hd) tl (F tl)
          end
        in
        match query with
        | SingleField n α => IH_SF n α
        | LabeledField l n α => IH_LF l n α
        | NestedField n α ϕ => IH_NF n α ϕ (F ϕ)
        | NestedLabeledField l n α ϕ => IH_NLF l n α ϕ (F ϕ)
        | InlineFragment t ϕ => IH_IF t ϕ (F ϕ)
        end.

  
  Definition ResponseObject_rect (P : ResponseObject -> Type)
             (IH_Null : forall n, P (Null n))
             (IH_SR : forall n v, P (SingleResult n v))
             (IH_LR : forall n vals, P (ListResult n vals))
             (IH_NR : forall n ρ, Forallt P ρ -> P (NestedResult n ρ))
             (IH_NLR : forall n ρ, Forallt (fun rs => Forallt P rs) ρ -> P (NestedListResult n ρ)) :=
      fix loop response : P response :=
        let fix F0 (ρ : seq ResponseObject) : Forallt P ρ :=
            match ρ with
            | [::] => Forallt_nil _
            | hd :: tl => @Forallt_cons _ P hd tl (loop hd) (F0 tl)
            end
        in
        let fix F1 (ρ : seq (seq ResponseObject)) : Forallt (fun rs => Forallt P rs) ρ :=
            match ρ as r with
            | [::] => Forallt_nil _
            | hd :: tl => @Forallt_cons _ (fun rs => Forallt P rs) hd tl (F0 hd) (F1 tl)
            end
        in
        match response with
        | Null n => IH_Null n
        | SingleResult n v => IH_SR n v
        | ListResult n vals => IH_LR n vals
        | NestedResult n ρ => IH_NR n ρ (F0 ρ)
        | NestedListResult n ρ => IH_NLR n ρ (F1 ρ)                                                
      end.

  Definition ResponseObject_rec (P : ResponseObject -> Set) := @ResponseObject_rect P.

  Definition ResponseObject_ind (P : ResponseObject -> Prop)
             (IH_Null : forall n, P (Null n))
             (IH_SR : forall n v, P (SingleResult n v))
             (IH_LR : forall n vals, P (ListResult n vals))
             (IH_NR : forall n ρ, Forall P ρ -> P (NestedResult n ρ))
             (IH_NLR : forall n ρ, Forall (fun rs => Forall P rs) ρ -> P (NestedListResult n ρ))
    :=
      fix loop response : P response :=
        let fix F0 (ρ : seq ResponseObject) : Forall P ρ :=
            match ρ with
            | [::] => Forall_nil _
            | hd :: tl => @Forall_cons _ P hd tl (loop hd) (F0 tl)
            end
        in
        let fix F1 (ρ : seq (seq ResponseObject)) : Forall (fun rs => Forall P rs) ρ :=
            match ρ as r with
            | [::] => Forall_nil _
            | hd :: tl => @Forall_cons _ (fun rs => Forall P rs) hd tl (F0 hd) (F1 tl)
            end
        in
        match response with
        | Null n => IH_Null n
        | SingleResult n v => IH_SR n v
        | ListResult n vals => IH_LR n vals
        | NestedResult n ρ => IH_NR n ρ (F0 ρ)
        | NestedListResult n ρ => IH_NLR n ρ (F1 ρ)
      end.
  
  

  (** Boolean predicate to state equivalence between queries, needed for canonical instance.

   Maybe an isomorphism to another structure would be better (tree) but it was a bit chaotic,
   so I left it there hanging for a while. **)
  Equations query_eq (q1 q2 : Query) : bool :=
    {
      query_eq (SingleField n α) (SingleField n' α') := (n == n') && (α == α');
      query_eq (LabeledField l n α) (LabeledField l' n' α') := [&& (l == l'), (n == n') & (α == α')];
      query_eq (NestedField n α ϕ) (NestedField n' α' ϕ') := [&& (n == n'), (α == α') & queries_eq ϕ ϕ'];
      query_eq (NestedLabeledField l n α ϕ) (NestedLabeledField l' n' α' ϕ') := [&& (l == l'), (n == n'), (α == α') & queries_eq ϕ ϕ'];
      query_eq (InlineFragment t ϕ) (InlineFragment t' ϕ') := (t == t') && (queries_eq ϕ ϕ');
      query_eq _ _ := false
    }
  where
  queries_eq (q1 q2 : seq Query) : bool :=
    {
      queries_eq [::] [::] := true;
      queries_eq (cons hd tl) (cons hd' tl') := query_eq hd hd' && queries_eq tl tl';
      queries_eq _ _ := false
    }.

  Lemma Forall_cons_inv {A : Type} (P : A -> Prop) x s : Forall P (x :: s) -> P x /\ Forall P s.
  Proof. by move=> H; inversion H. Qed.
    
  

  Lemma query_eqP : Equality.axiom query_eq.
  Proof.
    move=> q1 q2; apply (iffP idP) => [| <-].
    move: q2.
    elim q1 using Query_ind with (Pl := (fun qs => forall qs', queries_eq qs qs' -> qs = qs')).
    by move=> n α; case=> // n' α'; rewrite query_eq_equation_1; move/andP=> [/eqP -> /eqP ->].
    by move=> l n α; case=> // l' n' α'; rewrite query_eq_equation_7; move/and3P=> [/eqP -> /eqP -> /eqP ->].
  Admitted.

  
  Canonical query_eqType := EqType Query (EqMixin query_eqP).


  (** Extractors for queries **)
  Definition qname query : option Name :=
    match query with
    | SingleField name _
    | LabeledField _ name _
    | NestedField name _ _
    | NestedLabeledField _ name _ _ => Some name
    | _ => None
    end.

  Definition qlabel query : option Name :=
    match query with
    | LabeledField label _ _
    | NestedLabeledField label _ _ _ => Some label
    | _ => None
    end.
  
  Definition qsubquery query : seq Query :=
    match query with
    | NestedField _ _ ϕ
    | NestedLabeledField _ _ _ ϕ
    | InlineFragment _ ϕ => ϕ
    | _ => [::]
    end.

  Definition qargs query : {fmap Name -> Vals} :=
    match query with
    | SingleField _ α
    | LabeledField _ _ α
    | NestedField _ α _
    | NestedLabeledField _ _ α _ => α
    | _ => emptym
    end.


  (** Extractors for response objects **)
  Definition rname response : Name :=
    match response with
    | Null name
    | SingleResult name _
    | ListResult name _
    | NestedResult name _
    | NestedListResult name _ => name
    end.
  
  
End Query.

Arguments Query [Name Vals].
Arguments SingleField [Name Vals].
Arguments LabeledField [Name Vals].
Arguments NestedField [Name Vals].
Arguments NestedLabeledField [Name Vals].
Arguments InlineFragment [Name Vals].

Arguments ResponseObject [Name Vals].
Arguments Null [Name Vals].