From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

From extructures Require Import ord.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import QueryConformance.


Require Import NRGTNF.

Require Import Ssromega.

Require Import SeqExtra.

Require Import QueryTactics.

Section QueryRewrite.

  Variables Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type query : @Query Name Vals.


  Variable s : @wfSchema Name Vals.
  


  (* Lemma inlined_fields_are_grounded2 ty q pty : *)
  (*   is_object_type s ty = false -> *)
  (*   (get_possible_types s ty == [::]) = false -> *)
  (*   all (is_object_type s) pty -> *)
  (*   q.(is_field) -> *)
  (*   (forall t, is_grounded2 s t q) -> *)
  (*   are_grounded2 s ty [seq InlineFragment t [:: q] | t <- pty]. *)
  (* Proof. *)
  (*   move=> Hscope Hptys Hobjs Hfield Hg. *)
  (*   elim: pty Hobjs => //= hd tl IH /andP [Hobj Hobjs]. *)
  (*   Admitted. *)

 
  (* Lemma filter_preserves_grounded2 ty f qs : *)
  (*   are_grounded2 s ty qs -> *)
  (*   are_grounded2 s ty (filter_queries_with_label f qs). *)
  (* Proof. *)
  (*   funelim (filter_queries_with_label f qs) => //=; case Hscope: is_object_type => //=. *)
    
  (*   - simp is_grounded2 => /and3P [_ /andP [Hobj Hg] Hgs]; apply_and3P. *)
  (*     * by apply_andP; apply: H. *)
  (*     * by apply: H0. *)

  (*       all: do [by case/and3P => *; do ? apply_and3P; apply: H]. *)
  (* Qed.   *)

  


  (* Lemma filter_fields_preserves_not_similar q k (qs : seq (@Query Name Vals)) : *)
  (*   all (fun q' => ~~ are_similar q' q) qs -> *)
  (*   all (fun q' => ~~ are_similar q' q) (filter_queries_with_label k qs). *)
  (* Proof. *)
  (*   funelim (filter_queries_with_label _ qs) => //= /andP [Hsim Hall]; simp are_similar; apply_andP. *)
  (*   all: do ? by apply: H. *)
  (*   by apply: H0. *)
  (* Qed. *)

  (* Lemma all_not_similar_to_query_after_filter_fields q qs (Hfield : q.(is_field)) : *)
  (*   all (fun q' => ~~ are_similar q' q) (filter_queries_with_label (qresponse_name q Hfield) qs). *)
  (* Proof. *)
  (*   funelim (filter_queries_with_label _ qs) => //=; apply_andP; case_query q => //=; simp are_similar; intros; by apply/nandP; left => /=. *)
  (* Qed. *)


  
  (* Supposed to be applied over an object type *)
  Equations? reground (type_in_scope : @NamedType Name) (queries : seq (@Query Name Vals)) :
    seq (@Query Name Vals) by wf (queries_size queries) :=
    {
      reground _ [::] := [::];

      reground ty (SingleField f α :: qs)
        with lookup_field_in_type s ty f :=
        {
        | Some _ := SingleField f α :: reground ty (filter_queries_with_label f qs);
        | _ := reground ty qs
        };
      
      reground ty (LabeledField l f α :: qs)
        with lookup_field_in_type s ty f :=
        {
        | Some _ := LabeledField l f α :: reground ty (filter_queries_with_label l qs);
        | _ := reground ty qs
        };

      reground ty (NestedField f α φ :: qs)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s fld.(return_type) :=
            {
            | true := NestedField f α (reground fld.(return_type) (φ ++ merge_selection_sets (find_queries_with_label s f ty qs)))
                                 :: reground ty (filter_queries_with_label f qs);
            | _ := NestedField f α [seq InlineFragment t (reground t (φ ++ merge_selection_sets (find_queries_with_label s f ty qs))) | t <- get_possible_types s fld.(return_type)] ::
                              reground ty (filter_queries_with_label f qs)
            };
        
        | _ => reground ty qs
        };
      
      reground ty (NestedLabeledField l f α φ :: qs)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s fld.(return_type) :=
            {
            | true := NestedLabeledField l f α (reground fld.(return_type) (φ ++ merge_selection_sets (find_queries_with_label s l ty qs)))
                                        :: reground ty (filter_queries_with_label l qs);
            | _ := NestedLabeledField l f α [seq InlineFragment t (reground t (φ ++ merge_selection_sets (find_queries_with_label s l ty qs))) | t <- get_possible_types s fld.(return_type)] ::
                              reground ty (filter_queries_with_label l qs)
            };
        
        | _ => reground ty qs
        };
        
      
      reground ty (InlineFragment t φ :: qs)
        with does_fragment_type_apply s ty t :=
        {
        | true := reground ty (φ ++ qs);
        | _ := reground ty qs
        }

    }.
  Proof.
    all: do [leq_queries_size].
  Qed.

  Equations ground_queries (type_in_scope : @NamedType Name) (queries : seq (@Query Name Vals)) :
    seq (@Query Name Vals) :=
    {
      ground_queries ty qs
        with is_object_type s ty :=
        {
              | true := reground ty qs;
              | _ := [seq InlineFragment t (reground t qs) | t <- get_possible_types s ty]
        }
    }.

 
End QueryRewrite.


Arguments reground [Name Vals].
Arguments ground_queries [Name Vals].