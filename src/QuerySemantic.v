(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.


From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.

Require Import Query.
Require Import QueryConformance.
Require Import QueryAux.
Require Import QueryAuxLemmas.

Require Import Response.

Require Import Graph.
Require Import GraphConformance.


Require Import QueryTactics.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Query Semantics</h1>
        <p class="lead">
         This file contains the definitions for the semantics 
         in a graph setting and the simplified version used 
         for normalised queries.
        </p>         
  </div>
</div>#
 *)

Section QuerySemantic.

  Variables Vals : eqType.
  
  
  Variable s : @wfGraphQLSchema Vals.
  Variable g : @conformedGraph Vals s.

  (** ---- *)
  (** *** Coercion
      
      The semantics require an unspecified coercion function. 
      We define it as a function from Vals (scalar values) to 
      a JSON value. Since this transformation can introduce 
      redundancy, we include a proof that the coerced result is 
      non-redundant.
   *)
  Record wfCoercion :=
    WFCoercion {
        fn :> Vals -> @ResponseNode (option Vals);
        _ : forall (value : Vals), Response.is_non_redundant (fn value)
      }.
  
  
  Variable (coerce : wfCoercion).

  (** ---- *)
  
  Implicit Type u : @node Vals.
  Implicit Type query : @Selection Vals.
  Implicit Type queries : seq (@Selection Vals).

 
  Fixpoint is_valid_response_value (ty : type) (response : @ResponseNode (option Vals)) : bool :=
    match response with
    | Leaf (Some v) => s.(is_valid_value) ty v
    | Response.Object rs => all (fun r => is_valid_response_value ty r.2) rs
    | Array rs => all (is_valid_response_value ty) rs
    | _ => false 
    end.

  
  Reserved Notation "⟦ φ ⟧ˢ 'in' u" (at level 40).
  
  (** * Semantics in a Graph setting *)
  (** ---- *)
  (**
     #<strong>execute_selection_set</strong># : Node → List Selection → List (Name * ResponseNode)

     Evaluates the list of queries and returns a GraphQL Response.

   *)
  Equations? execute_selection_set u (queries : seq (@Selection Vals)) :
    
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      ⟦ [::] ⟧ˢ in _ := [::];
      
      ⟦ f[[α]] :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fdef
            with field_seq_value u.(nprops) (Field f α) :=
            {
            | Some value => let coerced_value := coerce value in
                           if is_valid_response_value fdef.(return_type) coerced_value then
                             (f, coerced_value) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u
                           else
                             (f, Leaf None) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;

            | None => (f, Leaf None) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u  (* Should throw error? *)
            };
        | _ := ⟦ φ ⟧ˢ in u (* Should throw error *)
        };
      
      ⟦ l:f[[α]] :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fdef
            with field_seq_value u.(nprops) (Field f α) :=
            {
            | Some value => let coerced_value := coerce value in
                           if is_valid_response_value fdef.(return_type) coerced_value then
                             (l, coerced_value) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u
                           else
                             (l, Leaf None) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
            | None => (l, Leaf None) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u (* Should throw error? *)
            };

        | _ := ⟦ φ ⟧ˢ in u (* Should throw error *)
        };

      
      ⟦ f[[α]] { β } :: φ ⟧ˢ in u 
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | [ _ ] := (f, Array [seq {- (⟦ β ++ merge_selection_sets (find_queries_with_label s f u.(ntype) φ) ⟧ˢ in v) -} | v <- neighbors_with_field g u (Field f α)])
                              :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
            | NamedType _
                with ohead (neighbors_with_field g u (Field f α)) :=
                {
                | Some v => (f, {- (⟦ β ++ merge_selection_sets (find_queries_with_label s f u.(ntype) φ) ⟧ˢ in v) -}) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
                
                | _ =>  (f, Leaf None) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u
                }
            };

        | None => ⟦ φ ⟧ˢ in u (* Should throw error *)
        };

      ⟦ l:f[[α]] { β } :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | [ _ ] := (l, Array [seq {- (⟦ β ++ merge_selection_sets (find_queries_with_label s l u.(ntype) φ) ⟧ˢ in v) -} | v <- neighbors_with_field g u (Field f α)])
                              :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
            | NamedType _
                with ohead (neighbors_with_field g u (Field f α)) :=
                {
                | Some v => (l, {- (⟦ β ++ merge_selection_sets (find_queries_with_label s l u.(ntype) φ) ⟧ˢ in v) -}) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
                
                | _ =>  (l, Leaf None) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u
                }
            };

        | None => ⟦ φ ⟧ˢ in u (* Should throw error *)
        };

       ⟦ on t { β } :: φ ⟧ˢ in u
        with does_fragment_type_apply s u.(ntype) t :=
        {
        | true := ⟦ β ++ φ ⟧ˢ in u;
        | _ := ⟦ φ ⟧ˢ in u
        }

    }
  where "⟦ queries ⟧ˢ 'in' u" := (execute_selection_set u queries).
  Proof.
    all: do [leq_queries_size].
  Qed.

  



  

  Reserved Notation "≪ queries ≫ 'in' u" (at level 50).

  (** * Simplified Semantics *)
  (** ---- *)
  (**
     #<strong>execute_selection_set2</strong># : Node → List Selection → List (Name * ResponseNode)

     Evaluates a list of queries and returns a GraphQL Response. 

     This function assumes the queries are in normal form (grounded and non-redundant).

     The definition corresponds to the one given by P&H.
   *)
  (* TODO : Rename ! *)
  Equations? execute_selection_set2 u queries :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      ≪ [::] ≫ in _ := [::];

      ≪ f[[α]] :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fdef
            with field_seq_value u.(nprops) (Field f α) :=
            {
            | Some value => let coerced_value := coerce value in
                           if is_valid_response_value fdef.(return_type) coerced_value then
                             (f, coerced_value) :: ≪ φ ≫ in u
                           else
                             (f, Leaf None) :: ≪ φ ≫ in u;
            
            | None => (f, Leaf None) :: ≪ φ ≫ in u
            };
        | _ := ≪ φ ≫ in u (* Error *)
        };
      
      ≪ l:f[[α]] :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fdef
            with field_seq_value u.(nprops) (Field f α) :=
            {
            | Some value => let coerced_value := coerce value in
                           if is_valid_response_value fdef.(return_type) coerced_value then
                             (l, coerced_value) :: ≪ φ ≫ in u
                           else
                             (l, Leaf None) :: ≪ φ ≫ in u;
            
            | None => (l, Leaf None) :: ≪ φ ≫ in u
            };
        | _ := ≪ φ ≫ in u (* Error *)
        };

      
      ≪ f[[α]] { β } :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | ListType _ => (f, Array [seq {- ≪ β ≫ in v -} | v <- neighbors_with_field g u (Field f α)]) :: ≪ φ ≫ in u;
        
            | NamedType ty
                with ohead (neighbors_with_field g u (Field f α)) :=
                {
                | Some v => (f, {- ≪ β ≫ in v -}) :: ≪ φ ≫ in u;
                
                | _ =>  (f, Leaf None) :: ≪ φ ≫ in u
                }
            };

        | None => ≪ φ ≫ in u (* Error *)
        };
    ≪ l:f[[α]] { β } :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | ListType _ => (l, Array [seq {- ≪ β ≫ in v -} | v <- neighbors_with_field g u (Field f α)]) :: ≪ φ ≫ in u;
        
            | NamedType ty
                with ohead (neighbors_with_field g u (Field f α)) :=
                {
                | Some v => (l, {- ≪ β ≫ in v -}) :: ≪ φ ≫ in u;
                
                | _ =>  (l, Leaf None) :: ≪ φ ≫ in u
                }
            };

        | None => ≪ φ ≫ in u (* Error *)
        };

       
        ≪ on t { β } :: φ ≫ in u
        with does_fragment_type_apply s u.(ntype) t :=
        {
        | true := ≪ β ++ φ ≫ in u;
        | _ := ≪ φ ≫ in u
        }

    }
  where "≪ queries ≫ 'in' u" := (execute_selection_set2 u queries).
  Proof.
    all: do [leq_queries_size].
  Qed.

  
 


  
  

  (** * Spec's Semantics 

      The spec's semantics should be here :)
   *) 
  (** ---- *)
  (**
     #<strong>resolve_field_value</strong># : Node → Name → List (Name * Vals) ↪ Vals + List Vals 

     Attempt at replicating the specification's definition of _ResolveFieldValue_ 
     instantiated to the graph setting.

     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** See also
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##ResolveFieldValue()'>ResolveFieldValue()</a># 
   *)
  Equations resolve_field_value u (field_name : Name) (argument_values : seq (Name * Vals)) : option (Vals + (@node Vals) + seq (@node Vals)) :=
    {
      resolve_field_value u f α
        with field_seq_value u.(nprops) (Field f α) :=
        {
        | Some value := Some (inl (inl value));
        | _ with neighbors_with_field g u (Field f α) :=
            {
            | [::] := None;
            | [:: v] => Some (inl (inr v));
            | vs := Some (inr vs)
            }
        }
    }.


  (* begin hide *)
  (* Equations' bug ? *)
  (* Equations? execute_selection_set3 u (queries : seq (@Selection Vals)) : *)
  (*   seq (Name * ResponseNode) by wf (queries_size queries) := *)
  (*   { *)
  (*     execute_selection_set3 _ [::] := [::]; *)
      
  (*     execute_selection_set3 u (InlineFragment t φ :: qs) *)
  (*       with does_fragment_type_apply s u.(ntype) t := *)
  (*       { *)
  (*       | true := execute_selection_set u (φ ++ qs); *)
  (*       | _ := execute_selection_set u qs *)
  (*       }; *)

  (*     execute_selection_set3 u (q :: qs) *)
  (*       with lookup_field_type s u.(ntype) (qname q _) := *)
  (*       { *)
  (*       | Some (ListType ty) := ((qresponse_name q _), complete_value (resolve_field_value u (qname q _) (qargs q _))) *)
  (*                        :: execute_selection_set3 u (filter_queries_with_label (qresponse_name q _) qs) *)

  (*          where complete_value (result : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals))) : ResponseNode := *)
  (*                  { *)
  (*                    complete_value None := Leaf None; *)

  (*                    complete_value (Some (inr vs)) := Array *)
  (*                                                       [seq Object *)
  (*                                                            (execute_selection_set v (q.(qsubqueries) ++ merge_selection_sets (find_queries_with_label s v.(type) (qresponse_name q _) qs))) | v <- vs]; *)

  (*                    complete_value _ := Leaf None *)
  (*                  }; *)

  (*       | Some (NamedType ty) := ((qresponse_name q _), complete_value (resolve_field_value u (qname q _) (qargs q _))) *)
  (*                        :: execute_selection_set3 u (filter_queries_with_label (qresponse_name q _) qs) *)

  (*          where complete_value (result : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals))) : ResponseNode := *)
  (*                  { *)
  (*                    complete_value None := Leaf None; *)

  (*                    complete_value (Some (inl (inl value))) *)
  (*                      with value := *)
  (*                      { *)
  (*                      | inl v := Leaf (Some v); *)
  (*                      | inr vs := Array (map (fun value => Leaf (Some value)) vs) *)
  (*                      }; *)

  (*                    complete_value (Some (inl (inr v))) := Object (execute_selection_set v (q.(qsubqueries) ++ merge_selection_sets (find_queries_with_label s v.(type) (qresponse_name q _) qs))); *)

  (*                    complete_value _ := Leaf None *)
  (*                  }; *)

  (*       | _ := ((qresponse_name q _), Leaf None) :: execute_selection_set3 u (filter_queries_with_label (qresponse_name q _) qs) *)
  (*       } *)
  (*   }. *)
  (* Proof. *)
  (*   all: do [leq_queries_size]. *)
    
  (* Qed. *)

  
  

   
  (* Leaving it commented for the moment

  Reserved Notation "ty '⊢' φ '≡' φ'" (at level 80). 
         
  Equations? Equiv  (ty : Name) (φ1 φ2 : seq (@Selection Vals)) : bool by wf (queries_size φ1 + queries_size φ2) :=
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

  (* end hide *)

  (** ---- *)
End QuerySemantic.

Arguments is_valid_response_value [Vals].
Arguments execute_selection_set [Vals].
Arguments execute_selection_set2 [Vals].

Delimit Scope query_eval with QEVAL.
Open Scope query_eval.

(* This notation collides with the pairs notation (_ , _) ...  *)
Notation "s , g ⊢ ⟦ φ ⟧ˢ 'in' u 'with' coerce" := (execute_selection_set s g coerce u φ) (at level 30, g at next level, φ at next level) : query_eval.
Notation "s , g ⊢ ≪ φ ≫ 'in' u 'with' coerce" := (execute_selection_set2 s g coerce u φ) (at level 30, g at next level, φ at next level) : query_eval.


(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.Response.html' class="btn btn-light" role='button'> Previous ← GraphQL Response </a>
        <a href='GraphCoQL.theory.SelectionSemanticsLemmas.html' class="btn btn-info" role='button'>Continue Reading → Semantics Proofs</a>
    </div>#
*)
