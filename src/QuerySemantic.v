(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.


From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Value.

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

  Variables (Scalar : eqType)
            (s : wfGraphQLSchema)
            (is_valid_scalar_value : graphQLSchema -> Name -> Scalar -> bool)
            (g : conformedGraph s is_valid_scalar_value)
            (coerce : Scalar -> Scalar).

  (* (** ---- *) *)
  (* (** *** Coercion *)
      
  (*     The semantics require an unspecified coercion function.  *)
  (*     We define it as a function from Value (scalar values) to  *)
  (*     a JSON value. Since this transformation can introduce  *)
  (*     redundancy, we include a proof that the coerced result is  *)
  (*     non-redundant. *)
  (*  *) *)
  (* Record wfCoercion := *)
  (*   WFCoercion { *)
  (*       fn :> Value -> @ResponseValue Value; *)
  (*       _ : forall (value : Value), Response.is_non_redundant (fn value) *)
  (*     }. *)
  
  
  (* Variable (coerce : wfCoercion). *)

  (** ---- *)
  
  Implicit Type u : @node Scalar.
  Implicit Type query : @Selection Scalar.
  Implicit Type queries : seq (@Selection Scalar).

 
  (* Fixpoint is_valid_response_value (ty : type) (response : @ResponseValue Value) : bool := *)
  (*   match ty, response with *)
  (*   | NamedType _, (Leaf (Some v)) => s.(is_valid_value) ty v *)
  (*   | ListType ty, Array rs => all (is_valid_response_value ty) rs *)
  (*   | _, _ => false  *)
  (*   end. *)

 
  Equations complete_value (ftype : type) (value : option (@Value Scalar)) : @ResponseValue Scalar :=
    {
      complete_value (NamedType n) (Some (SValue svalue))
        with is_valid_scalar_value s n (coerce svalue) :=
        {
        | true := Leaf (Some (coerce svalue));
        | _ := Leaf None
        };

      complete_value (ListType wty) (Some (LValue lvalue)) :=
        Array (map (complete_value wty) (map Some lvalue));

      complete_value _ _ := Leaf None
    }.
      
                                                                       
  
  
  Reserved Notation "⟦ φ ⟧ˢ 'in' u" (at level 40).
  
  (** * Semantics in a Graph setting *)
  (** ---- *)
  (**
     #<strong>execute_selection_set</strong># : Node → List Selection → List (Name * ResponseValue)

     Evaluates the list of queries and returns a GraphQL Response.

   *)
  Equations? execute_selection_set u (queries : seq (@Selection Scalar)) :
    @GraphQLResponse Scalar by wf (queries_size queries) :=
    {
      ⟦ [::] ⟧ˢ in _ := [::];
      
      ⟦ f[[α]] :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fdef := (f, complete_value fdef.(return_type) (field_seq_value u.(nprops) (Label f α)))
                        :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;

        | _ := ⟦ φ ⟧ˢ in u (* Should throw error *)
        };
      
      ⟦ l:f[[α]] :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fdef := (l, complete_value fdef.(return_type) (field_seq_value u.(nprops) (Label f α)))
                        :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;

        | _ := ⟦ φ ⟧ˢ in u (* Should throw error *)
        };

      
      ⟦ f[[α]] { β } :: φ ⟧ˢ in u 
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | [ _ ] := (f, Array [seq {- (⟦ β ++ merge_selection_sets (find_queries_with_label s f u.(ntype) φ) ⟧ˢ in v) -} | v <- neighbors_with_field g u (Label f α)])
                              :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
            | NamedType _
                with ohead (neighbors_with_field g u (Label f α)) :=
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
            | [ _ ] := (l, Array [seq {- (⟦ β ++ merge_selection_sets (find_queries_with_label s l u.(ntype) φ) ⟧ˢ in v) -} | v <- neighbors_with_field g u (Label f α)])
                              :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
            | NamedType _
                with ohead (neighbors_with_field g u (Label f α)) :=
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

  

  Definition execute_query (q : query) :=
    execute_selection_set g.(root) q.(selection_set).
  

  

  Reserved Notation "≪ queries ≫ 'in' u" (at level 50).

  (** * Simplified Semantics *)
  (** ---- *)
  (**
     #<strong>execute_selection_set2</strong># : Node → List Selection → List (Name * ResponseValue)

     Evaluates a list of queries and returns a GraphQL Response. 

     This function assumes the queries are in normal form (grounded and non-redundant).

     The definition corresponds to the one given by P&H.
   *)
  Equations? simpl_execute_selection_set u queries :
    @GraphQLResponse Scalar by wf (queries_size queries) :=
    {
      ≪ [::] ≫ in _ := [::];

      ≪ f[[α]] :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
          | Some fdef := (f, complete_value fdef.(return_type) (field_seq_value u.(nprops) (Label f α)))
                          :: ≪ φ ≫ in u;
          
          | _ := ≪ φ ≫ in u (* Should throw error *)
        };
      
      ≪ l:f[[α]] :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
            {
            | Some fdef := (l, complete_value fdef.(return_type) (field_seq_value u.(nprops) (Label f α)))
                            :: ≪ φ ≫ in u;
            
            | _ := ≪ φ ≫ in u (* Should throw error *)
            };

      
      ≪ f[[α]] { β } :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | ListType _ => (f, Array [seq {- ≪ β ≫ in v -} | v <- neighbors_with_field g u (Label f α)]) :: ≪ φ ≫ in u;
        
            | NamedType ty
                with ohead (neighbors_with_field g u (Label f α)) :=
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
            | ListType _ => (l, Array [seq {- ≪ β ≫ in v -} | v <- neighbors_with_field g u (Label f α)]) :: ≪ φ ≫ in u;
        
            | NamedType ty
                with ohead (neighbors_with_field g u (Label f α)) :=
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
  where "≪ queries ≫ 'in' u" := (simpl_execute_selection_set u queries).
  Proof.
    all: do [leq_queries_size].
  Qed.


  Definition simpl_execute_query (q : @query Scalar) :=
    ≪ q.(selection_set) ≫ in g.(root).
  
 


  
  

  (** ---- *)
End QuerySemantic.

Arguments complete_value [Scalar].
Arguments execute_selection_set [Scalar].
Arguments execute_query [Scalar].
Arguments simpl_execute_selection_set [Scalar].
Arguments simpl_execute_query [Scalar].

Delimit Scope query_eval with QEVAL.
Open Scope query_eval.

(* This notation collides with the pairs notation (_ , _) ...  *)
(* Notation "s , g ⊢ ⟦ φ ⟧ˢ 'in' u 'with' coerce" := (execute_selection_set s g coerce u φ) (at level 30, g at next level, φ at next level) : query_eval. *)
(* Notation "s , g ⊢ ≪ φ ≫ 'in' u 'with' coerce" := (simpl_execute_selection_set s g coerce u φ) (at level 30, g at next level, φ at next level) : query_eval. *)


(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.Response.html' class="btn btn-light" role='button'> Previous ← GraphQL Response </a>
        <a href='GraphCoQL.theory.SelectionSemanticsLemmas.html' class="btn btn-info" role='button'>Continue Reading → Semantics Proofs</a>
    </div>#
*)
