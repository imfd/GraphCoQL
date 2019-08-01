From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord fmap fset.
From Equations Require Import Equations.


Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.

Require Import Query.
Require Import QueryConformance.
Require Import QueryAux.
Require Import QueryAuxLemmas.

Require Import Response.

Require Import Graph.
Require Import GraphAux.
Require Import GraphConformance.


Require Import QueryTactics.


Section QuerySemantic.

  Variables N Name Vals : ordType.
  
  
  Variable s : @wfSchema Name Vals.
  Variable g : @conformedGraph Name Vals s.
  
  Implicit Type u : @node Name Vals.
  Implicit Type query : @Query Name Vals.
  Implicit Type queries : seq (@Query Name Vals).

 

  Reserved Notation "⟦ φ ⟧ˢ 'in' u" (at level 40).
  
  Equations? execute_selection_set u (queries : seq (@Query Name Vals)) :
    
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      ⟦ [::] ⟧ˢ in _ := [::];
      
      ⟦ f[[α]] :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(type) f :=
        {
        | Some _
            with u.(fields) (Field f α) :=
            {
            | Some (inl value) => (f, Leaf (SingleValue value)) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
            | Some (inr values) => (f, Array (map (Leaf \o SingleValue) values)) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
            | None => (f, Leaf Null) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u  (* Should throw error? *)
            };
        | _ := ⟦ φ ⟧ˢ in u (* Should throw error *)
        };
      
      ⟦ l:f[[α]] :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(type) f :=
        {
        | Some _
            with u.(fields) (Field f α) :=
            {
            | Some (inl value) => (l, Leaf (SingleValue value)) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
            | Some (inr values) => (l, Array (map (Leaf \o SingleValue) values)) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
            | None => (l, Leaf Null) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u (* Should throw error? *)
            };

        | _ := ⟦ φ ⟧ˢ in u (* Should throw error *)
        };

      
      ⟦ f[[α]] { β } :: φ ⟧ˢ in u 
        with lookup_field_in_type s u.(type) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | [ _ ] := (f, Array [seq {- (⟦ β ++ merge_selection_sets (find_queries_with_label s f u.(type) φ) ⟧ˢ in v) -} | v <- neighbours_with_field g u (Field f α)])
                              :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
            | NT _
                with ohead (neighbours_with_field g u (Field f α)) :=
                {
                | Some v => (f, {- (⟦ β ++ merge_selection_sets (find_queries_with_label s f u.(type) φ) ⟧ˢ in v) -}) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
                
                | _ =>  (f, Leaf Null) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u
                }
            };

        | None => ⟦ φ ⟧ˢ in u (* Should throw error *)
        };

      ⟦ l:f[[α]] { β } :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(type) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | [ _ ] := (l, Array [seq {- (⟦ β ++ merge_selection_sets (find_queries_with_label s l u.(type) φ) ⟧ˢ in v) -} | v <- neighbours_with_field g u (Field f α)])
                              :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
            | NT _
                with ohead (neighbours_with_field g u (Field f α)) :=
                {
                | Some v => (l, {- (⟦ β ++ merge_selection_sets (find_queries_with_label s l u.(type) φ) ⟧ˢ in v) -}) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
                
                | _ =>  (l, Leaf Null) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u
                }
            };

        | None => ⟦ φ ⟧ˢ in u (* Should throw error *)
        };

       ⟦ on t { β } :: φ ⟧ˢ in u
        with does_fragment_type_apply s u.(type) t :=
        {
        | true := ⟦ β ++ φ ⟧ˢ in u;
        | _ := ⟦ φ ⟧ˢ in u
        }

    }
  where "⟦ queries ⟧ˢ 'in' u" := (execute_selection_set u queries).
  Proof.
    all: do [leq_queries_size].
  Qed.

  


  
 

  

  Reserved Notation "⦃ queries 'in' u ⦄" (at level 50).
  
  Equations? execute_selection_set2 u queries :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      execute_selection_set2 _ [::] := [::];

      execute_selection_set2 u (SingleField f α :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some _ 
            with u.(fields) (Field f α) :=
            {
            | Some (inl value) => (f, Leaf (SingleValue value)) :: ⦃ qs in u ⦄;
            | Some (inr values) => (f, Array (map (Leaf \o SingleValue) values)) :: ⦃ qs in u ⦄;
            | None => (f, Leaf Null) :: ⦃ qs in u ⦄
            };
        | _ := ⦃ qs in u ⦄ (* Error *)
        };
      
      execute_selection_set2 u (LabeledField l f α :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some _ 
            with u.(fields) (Field f α) :=
            {
            | Some (inl value) => (l, Leaf (SingleValue value)) :: ⦃ qs in u ⦄;
            | Some (inr values) => (l, Array (map (Leaf \o SingleValue) values)) :: ⦃ qs in u ⦄;
            | None => (l, Leaf Null) :: ⦃ qs in u ⦄
            };
        | _ := ⦃ qs in u ⦄ (* Error *)
        };

      
      execute_selection_set2 u (NestedField f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | ListType _ => (f, Array [seq {- ⦃ φ in v ⦄ -} | v <- neighbours_with_field g u (Field f α)]) :: ⦃ qs in u ⦄;
        
            | NT ty
                with ohead (neighbours_with_field g u (Field f α)) :=
                {
                | Some v => (f, {- ⦃ φ in v ⦄ -}) :: ⦃ qs in u ⦄;
                
                | _ =>  (f, Leaf Null) :: ⦃ qs in u ⦄
                }
            };

        | None => ⦃ qs in u ⦄ (* Error *)
        };
    execute_selection_set2 u (NestedLabeledField l f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | ListType _ => (l, Array [seq {- ⦃ φ in v ⦄ -} | v <- neighbours_with_field g u (Field f α)]) :: ⦃ qs in u ⦄;
        
            | NT ty
                with ohead (neighbours_with_field g u (Field f α)) :=
                {
                | Some v => (l, {- ⦃ φ in v ⦄ -}) :: ⦃ qs in u ⦄;
                
                | _ =>  (l, Leaf Null) :: ⦃ qs in u ⦄
                }
            };

        | None => ⦃ qs in u ⦄ (* Error *)
        };

       
        execute_selection_set2 u (InlineFragment t φ :: qs)
        with does_fragment_type_apply s u.(type) t :=
        {
        | true := ⦃ φ ++ qs in u ⦄;
        | _ := ⦃ qs in u ⦄
        }

    }
  where "⦃ queries 'in' u ⦄" := (execute_selection_set2 u queries).
  Proof.
    all: do [leq_queries_size].
  Qed.

  
 


  
  

        
  

  Equations resolve_field_value u (field_name : Name) (argument_values : {fmap Name -> Vals}) : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals)) :=
    {
      resolve_field_value u f α
        with u.(fields) (Field f α) :=
        {
        | Some value := Some (inl (inl value));
        | _ with neighbours_with_field g u (Field f α) :=
            {
            | [::] := None;
            | [:: v] => Some (inl (inr v));
            | vs := Some (inr vs)
            }
        }
    }.


  (* Equations' bug ? *)
  (* Equations? execute_selection_set3 u (queries : seq (@Query Name Vals)) : *)
  (*   seq (Name * ResponseNode) by wf (queries_size queries) := *)
  (*   { *)
  (*     execute_selection_set3 _ [::] := [::]; *)
      
  (*     execute_selection_set3 u (InlineFragment t φ :: qs) *)
  (*       with does_fragment_type_apply s u.(type) t := *)
  (*       { *)
  (*       | true := execute_selection_set u (φ ++ qs); *)
  (*       | _ := execute_selection_set u qs *)
  (*       }; *)

  (*     execute_selection_set3 u (q :: qs) *)
  (*       with lookup_field_type s u.(type) (qname q _) := *)
  (*       { *)
  (*       | Some (ListType ty) := ((qresponse_name q _), complete_value (resolve_field_value u (qname q _) (qargs q _))) *)
  (*                        :: execute_selection_set3 u (filter_queries_with_label (qresponse_name q _) qs) *)

  (*          where complete_value (result : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals))) : ResponseNode := *)
  (*                  { *)
  (*                    complete_value None := Leaf Null; *)

  (*                    complete_value (Some (inr vs)) := Array *)
  (*                                                       [seq Object *)
  (*                                                            (execute_selection_set v (q.(qsubqueries) ++ merge_selection_sets (find_queries_with_label s v.(type) (qresponse_name q _) qs))) | v <- vs]; *)

  (*                    complete_value _ := Leaf Null *)
  (*                  }; *)

  (*       | Some (NT ty) := ((qresponse_name q _), complete_value (resolve_field_value u (qname q _) (qargs q _))) *)
  (*                        :: execute_selection_set3 u (filter_queries_with_label (qresponse_name q _) qs) *)

  (*          where complete_value (result : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals))) : ResponseNode := *)
  (*                  { *)
  (*                    complete_value None := Leaf Null; *)

  (*                    complete_value (Some (inl (inl value))) *)
  (*                      with value := *)
  (*                      { *)
  (*                      | inl v := Leaf (SingleValue v); *)
  (*                      | inr vs := Array (map (Leaf \o SingleValue) vs) *)
  (*                      }; *)

  (*                    complete_value (Some (inl (inr v))) := Object (execute_selection_set v (q.(qsubqueries) ++ merge_selection_sets (find_queries_with_label s v.(type) (qresponse_name q _) qs))); *)

  (*                    complete_value _ := Leaf Null *)
  (*                  }; *)

  (*       | _ := ((qresponse_name q _), Leaf Null) :: execute_selection_set3 u (filter_queries_with_label (qresponse_name q _) qs) *)
  (*       } *)
  (*   }. *)
  (* Proof. *)
  (*   all: do [leq_queries_size]. *)
    
  (* Qed. *)

  
  

    

  (* Leaving it commented for the moment

  Reserved Notation "ty '⊢' φ '≡' φ'" (at level 80). 
         
  Equations? Equiv  (ty : Name) (φ1 φ2 : seq (@Query Name Vals)) : bool by wf (queries_size φ1 + queries_size φ2) :=
    {
      _ ⊢ [::] ≡ [::] := true;

      ty ⊢ SingleField f α :: φ1 ≡ SingleField f' α' :: φ2
        with (f == f') && (α == α') :=
        {
        | true 
            with lookup_field_in_type s ty f :=
            {
            | Some fld := ty ⊢ filter_queries_with_label f φ1 ≡ filter_queries_with_label f φ2;
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };
      
       ty ⊢ SingleField f α :: φ1 ≡ LabeledField l f' α' :: φ2
        with [&& (f == l), (f == f') & (α == α')] :=
        {
        | true 
            with lookup_field_in_type s ty f :=
            {
            | Some fld := ty ⊢ filter_queries_with_label f φ1 ≡ filter_queries_with_label f φ2;
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };

       ty ⊢ LabeledField l f α :: φ1 ≡ SingleField f' α' :: φ2
        with [&& (l == f'), (f == f') & (α == α')] :=
        {
        | true 
            with lookup_field_in_type s ty f :=
            {
            | Some fld := ty ⊢ filter_queries_with_label l φ1 ≡ filter_queries_with_label l φ2;
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };
          
       ty ⊢ LabeledField l f α :: φ1 ≡ LabeledField l' f' α' :: φ2
        with [&& (l == l'), (f == f') & (α == α')] :=
        {
        | true 
            with lookup_field_in_type s ty f :=
            {
            | Some fld := ty ⊢ filter_queries_with_label l φ1 ≡ filter_queries_with_label l φ2;
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        }; 

      ty ⊢ NestedField f α β :: φ1 ≡ NestedField f' α' χ :: φ2
        with (f == f') && (α == α') :=
        {
        | true
            with lookup_field_in_type s ty f :=
            {
            | Some fld := (all (fun t => t ⊢ β ++ merge_selection_sets (find_queries_with_label s f ty φ1) ≡
                                       χ ++ merge_selection_sets (find_queries_with_label s f ty φ2))
                             (get_possible_types s fld.(return_type))) &&
                             (ty ⊢ filter_queries_with_label f φ1 ≡ filter_queries_with_label f φ2);
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };

      ty ⊢ NestedField f α β :: φ1 ≡ NestedLabeledField l f' α' χ :: φ2
        with [&& (f == l), (f == f') & (α == α')] :=
        {
        | true
            with lookup_field_in_type s ty f :=
            {
            | Some fld := (all (fun t => t ⊢ β ++ merge_selection_sets (find_queries_with_label s f ty φ1) ≡
                                       χ ++ merge_selection_sets (find_queries_with_label s f ty φ2))
                             (get_possible_types s fld.(return_type))) &&
                             (ty ⊢ filter_queries_with_label f φ1 ≡ filter_queries_with_label f φ2);
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };

      ty ⊢ NestedLabeledField l f α β :: φ1 ≡ NestedField f' α' χ :: φ2
        with [&& (f == l), (f == f') & (α == α')] :=
        {
        | true
            with lookup_field_in_type s ty f :=
            {
            | Some fld := (all (fun t => t ⊢ β ++ merge_selection_sets (find_queries_with_label s l ty φ1) ≡
                                       χ ++ merge_selection_sets (find_queries_with_label s l ty φ2))
                             (get_possible_types s fld.(return_type))) &&
                             (ty ⊢ filter_queries_with_label l φ1 ≡ filter_queries_with_label l φ2);
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };

      ty ⊢ NestedLabeledField l f α β :: φ1 ≡ NestedLabeledField l' f' α' χ :: φ2
        with [&& (l == l'), (f == f') & (α == α')] :=
        {
        | true
            with lookup_field_in_type s ty f :=
            {
            | Some fld := (all (fun t => t ⊢ β ++ merge_selection_sets (find_queries_with_label s l ty φ1) ≡
                                       χ ++ merge_selection_sets (find_queries_with_label s l ty φ2))
                             (get_possible_types s fld.(return_type))) &&
                             (ty ⊢ filter_queries_with_label l φ1 ≡ filter_queries_with_label l φ2);
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };

      (* ty ⊢ InlineFragment t1 β :: φ1 ≡ InlineFragment t2 χ :: φ2 *)
      (*   with does_fragment_type_apply s ty t1, does_fragment_type_apply s ty t2 := *)
      (*   { *)
      (*   | true | true := ty ⊢ β ++ φ1 ≡ χ ++ φ2; *)
      (*   | true | false := ty ⊢ β ++ φ1 ≡ φ2; *)
      (*   | false | true := ty ⊢ φ1 ≡ χ ++ φ2; *)
      (*   | _ | _ := ty ⊢ φ1 ≡ φ2 *)
      (*   }; *)
          
      ty ⊢ InlineFragment t β :: φ1 ≡ φ2
        with does_fragment_type_apply s ty t :=
        {
        | true := ty ⊢ β ++ φ1 ≡ φ2;
        | _ := ty ⊢ φ1 ≡ φ2
        };
      
      ty ⊢ φ1 ≡ InlineFragment t β :: φ2
        with does_fragment_type_apply s ty t :=
        {
        | true := ty ⊢ φ1 ≡ β ++ φ2;
        | _ := ty ⊢ φ1 ≡ φ2
        };
         
      _ ⊢ _ ≡ _ := false
    }
  where "ty '⊢' φ1 '≡' φ2" := (Equiv ty φ1 φ2).
  Proof.
    all: do [leq_queries_size].

    all: do ?[ by have Hfleq := (found_queries_leq_size s f ty φ1);
               have Hmleq := (merged_selections_leq (find_queries_with_label s f ty φ1)); 
                            leq_queries_size].
    all: do ? [have Hfleq := (found_queries_leq_size s l ty φ1);
               have Hmleq := (merged_selections_leq (find_queries_with_label s l ty φ1));
                            leq_queries_size].  
  Qed.

  *)

  

        
End QuerySemantic.

Arguments execute_selection_set [Name Vals].

Delimit Scope query_eval with QEVAL.
Open Scope query_eval.

Notation "s , g ⊢ ⟦ φ ⟧ˢ 'in' u" := (execute_selection_set s  g u φ) (at level 30).