(* begin hide *)
From mathcomp Require Import all_ssreflect.
(* Set Implicit Arguments. *)
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Values</h1>
        <p class="lead">
         This file contains the definition of values used throughout the rest of the 
         project, in graphs and queries.
        </p>
         
  </div>
</div>#
 *)

Section Value.

  Variable (Scalar : eqType).

  (* Unsetting because the automatically generated induction principle is not good enough. *)
  Unset Elimination Schemes.

  (** ---- *)
  (**
     Values are not specified in the Spec, since GraphQL is agnostic to the underlying technology
     used. However, it is still possible to distinguish (at least) two types of values: 
     - Scalar values
     - List values (collections)

     A third possible type of value could be object values but we do not include this notion yet
     (nodes in a graph would represent elements of this third kind).

   *)
  Inductive Value : Type :=
  | SValue : Scalar -> Value
  | LValue : seq Value -> Value.

  Set Elimination Schemes.

   
  (** ---- *)
  (**
     Defining the induction principle for [Value].
   *)
  Definition Value_rect (P : Value -> Type)
             (Pl : seq Value -> Type)
             (IH_SValue : forall s, P (SValue s))
             (IH_LValue : forall vs, Pl vs -> P (LValue vs))
             (IH_Nil : Pl [::])
             (IH_Cons : forall v, P v -> forall vs, Pl vs -> Pl (v :: vs))
    :=
    fix loop value : P value :=
      let fix F (qs : seq Value) : Pl qs :=
          match qs with
          | [::] => IH_Nil
          | hd :: tl => IH_Cons hd (loop hd) tl (F tl)
          end
      in
      match value with
      | SValue s => IH_SValue s
      | LValue vs => IH_LValue vs (F vs)
      end.

  Definition Value_rec (P : Value -> Set) := @Value_rect P.

  Definition Value_ind (P : Value -> Prop)
             (Pl : seq Value -> Prop)
             (IH_SValue : forall s, P (SValue s))
             (IH_LValue : forall vs, Pl vs -> P (LValue vs))
             (IH_Nil : Pl [::])
             (IH_Cons : forall v, P v -> forall vs, Pl vs -> Pl (v :: vs))
    :=
      fix loop value : P value :=
        let fix F (qs : seq Value) : Pl qs :=
          match qs with
          | [::] => IH_Nil
          | hd :: tl => IH_Cons hd (loop hd) tl (F tl)
          end
        in
        match value with
        | SValue s => IH_SValue s
        | LValue vs => IH_LValue vs (F vs)
        end.


  (**
     We also establish that this type has a decidable procedure for equality but 
     we omit it here to unclutter the doc (it may still be seen in the source code).
   *)

  (* begin hide *)
  (** ---- *)
  (**
     #<strong></strong>#: Value → Value → Bool

     Decidable equality between values. 
   *)
  Equations value_eq (v1 v2 : Value) : bool :=
    {
      value_eq (SValue s1) (SValue s2) := s1 == s2;
      value_eq (LValue vs1) (LValue vs2) := value_seq_eq vs1 vs2;
      value_eq _ _ := false
    }
  where value_seq_eq (vs1 vs2 : seq Value) : bool :=
          {
            value_seq_eq [::] [::] := true;
            value_seq_eq (v1 :: vs1) (v2 :: vs2) := value_eq v1 v2 && value_seq_eq vs1 vs2;
            value_seq_eq _ _ := false
          }.
  
  (** ---- **)
  (**
     Reflexive lemma for [value_eq] and [eq].
   *)
  Lemma value_eq_axiom : Equality.axiom value_eq.
  Proof.
    rewrite /Equality.axiom => x y.                 
    apply: (iffP idP) => [| ->]; last first.
    - elim y using Value_ind with (Pl := fun vs1 => value_seq_eq vs1 vs1); intros; simp value_eq => //; apply/andP; split=> //.

    - move: y; elim x using Value_ind with
                   (Pl := fun vs1 => forall vs2, value_seq_eq vs1 vs2 -> vs1 = vs2) => [s | vs IHvs | | v IHv vs IHvs]; case=> //=.
      * by move=> s2; simp value_eq => /eqP ->.
      * by move=> vs2; simp value_eq => Hvseq; rewrite (IHvs vs2).
      * by move=> v2 vs2 /andP [/IHv -> /IHvs ->].
  Qed.
  
  Canonical value_eqType := EqType Value (EqMixin value_eq_axiom).
  
  (* end hide *)
  
End Value.

Arguments Value [Scalar].
Arguments SValue [Scalar].
Arguments LValue [Scalar].



(** #<a href='GraphCoQL.Schema.html' class="btn btn-info" role='button'>Continue Reading → Schema </a># *)