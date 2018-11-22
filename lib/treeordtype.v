(* I believe this file was written by Arthur Azevedo *)
From mathcomp Require Import all_ssreflect.

From extructures Require Import ord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TreeOrdType.

Variable T : ordType.

Implicit Types t : GenTree.tree T.

Fixpoint tree_leq t1 t2 :=
  match t1, t2 with
  | GenTree.Leaf x1, GenTree.Leaf x2   => (x1 <= x2)%ord
  | GenTree.Leaf x1, _                 => true
  | GenTree.Node n1 s1, GenTree.Leaf _ => false
  | GenTree.Node n1 s1, GenTree.Node n2 s2 =>
    let fix loop s1 s2 {struct s1} :=
      match s1, s2 with
      | [::], _ => true
      | t1 :: s1, [::] => false
      | t1 :: s1, t2 :: s2 =>
        if t1 == t2 then loop s1 s2 else tree_leq t1 t2
      end in
    (n1 < n2) ||
    (n1 == n2) && loop s1 s2
  end.

Lemma tree_leqP : Ord.axioms tree_leq.
Proof.
have anti: antisymmetric tree_leq.
  elim=> [x1|n1 s1 IH] [x2|n2 s2] //= => [/Ord.anti_leq ->|] //.
  have [l21|l12] /= := leqP n2 n1.
    case: eqP=> [->|] //; rewrite eqxx ltnn /= => H.
    rewrite (_ : s1 = s2) //.
    elim: s1 s2 IH H {l21 n1 n2} => [|t1 s1 IH] [|t2 s2] //=.
    case=> anti_t1 /IH {IH} IH.
    by rewrite [t2 == _]eq_sym; case: eqP=> [-> /IH ->|_ /anti_t1] //.
  by rewrite gtn_eqF //= ltnNge ltnW //=.
split=> //.
- elim=> [x|n s IH] //=; first exact: Ord.leqxx.
  apply/orP; right; rewrite eqxx /=.
  elim: s IH {n}=> /= [|t s IHs [-> /IHs ->]] //.
  by rewrite eqxx.
- elim=> [x2|n2 s2 IH] [x1|n1 s1] [x3|n3 s3] //=.
    exact: Ord.leq_trans.
  case/orP=> [e12|].
    case/orP=> [e23|]; first by rewrite (ltn_trans e12 e23).
    by case/andP=> [/eqP <-]; rewrite e12.
  case/andP=> [/eqP <- e12].
  case/orP=> [->|/andP [-> e23]] //=.
  apply/orP; right.
  elim: s2 s1 s3 IH e12 e23=> [|t2 s2 IH] [|t1 s1] [|t3 s3] //=.
  case=> t2_trans /IH {IH} IH.
  case: ifPn => [/eqP <-|ne12]; first by case: eqP; eauto.
  case: ifPn => [/eqP <-|ne23]; first by rewrite (negbTE ne12).
  move: ne12 ne23; case: (t1 =P t3) => [<-|]; last by eauto.
  move=> ne _ l12 l21; move: (anti t1 t2) ne; rewrite l12 l21.
  by move=> /(_ erefl) ->; rewrite eqxx.
- elim=> [x1|n1 s1 IH] [x2|n2 s2] //=; first exact: Ord.leq_total.
  case: ltngtP=> //= _.
  elim: s1 s2 IH {n1 n2}=> [|t1 s1 IH] [|t2 s2] //= [total_t1 /IH {IH} IH].
  by rewrite [t2 == _]eq_sym; case: (t1 =P t2)=> //.
Qed.

Definition tree_ordMixin := OrdMixin tree_leqP.
Canonical tree_ordType := Eval hnf in OrdType (GenTree.tree T) tree_ordMixin.

End TreeOrdType.

Section Example.

Variable L : ordType.

Inductive type : Type :=
| TBool  of L
| TUnit
| TArrow of type & L & L & type
| TRef   of L & type.

Implicit Types (τ σ : type) (l l_c l_o : L).

Notation "τ1 '-⟨' l1 '⟩->_{' l2 '}' τ2" := (TArrow τ1 l1 l2 τ2)
  (at level 30, right associativity, format "τ1  '-⟨' l1 '⟩->_{' l2 '}'  τ2").

Fixpoint tree_of_type τ :=
  match τ with
  | TBool l          => GenTree.Node 0 [:: GenTree.Leaf l]
  | TUnit            => GenTree.Node 1 [::]
  | τ -⟨l_c⟩->_{l} σ =>
    GenTree.Node 2 [:: tree_of_type τ; GenTree.Leaf l_c;
                       GenTree.Leaf l; tree_of_type σ]
  | TRef l τ =>
    GenTree.Node 3 [:: GenTree.Leaf l; tree_of_type τ]
  end.

Fixpoint type_of_tree t :=
  match t with
  | GenTree.Node 0 [:: GenTree.Leaf l] =>
    TBool l
  | GenTree.Node 1 [::] => TUnit
  | GenTree.Node 2 [:: t1; GenTree.Leaf l_c; GenTree.Leaf l; t2] =>
    type_of_tree t1 -⟨l_c⟩->_{l} type_of_tree t2
  | GenTree.Node 3 [:: GenTree.Leaf l; t] => TRef l (type_of_tree t)
  | _ => TUnit
  end.

Lemma tree_of_typeK : cancel tree_of_type type_of_tree.
Proof. by elim=> /= [l||τ -> l_c l σ ->|l τ ->]. Qed.

Definition type_eqMixin := CanEqMixin tree_of_typeK.
Canonical type_eqType := Eval hnf in EqType type type_eqMixin.
Definition type_choiceMixin := CanChoiceMixin tree_of_typeK.
Canonical type_choiceType := Eval hnf in ChoiceType type type_choiceMixin.
Definition type_ordMixin := CanOrdMixin tree_of_typeK.
Canonical type_ordType := Eval hnf in OrdType type type_ordMixin.

End Example.