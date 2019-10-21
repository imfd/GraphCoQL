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
         for normalized queries.
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


  
  Implicit Type u : @node Scalar.
  Implicit Type query : @Selection Scalar.
  Implicit Type queries : seq (@Selection Scalar).


  (** *** Complete values (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##CompleteValue()'><span>&#167;</span>6.4.3</a>#)
      ----

     Transform invalid values into null responses and coerces valid ones into 
     proper values, respecting the expected type by the schema.     
   *)
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
  (** ** Execute Selections 
      (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Executing-Selection-Sets'><span>&#167;</span>6.3</a>#)
      ---- 
   
      Evaluates the list of selections from a node, using a coercion function and a predicate to 
      validate the generated values, and returns a GraphQL Response.

   *)
  Equations? execute_selection_set u (queries : seq (@Selection Scalar)) :
    @GraphQLResponse Scalar by wf (selections_size queries) :=
    {
      ⟦ [::] ⟧ˢ in _ := [::];
      
      ⟦ f[[α]] :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fdef := (f, complete_value fdef.(ftype) (property u (Label f α)))
                        :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;

        | _ := ⟦ φ ⟧ˢ in u (* Should throw error *)
        };
      
      ⟦ l:f[[α]] :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fdef := (l, complete_value fdef.(ftype) (property u (Label f α)))
                        :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;

        | _ := ⟦ φ ⟧ˢ in u (* Should throw error *)
        };

      
      ⟦ f[[α]] { β } :: φ ⟧ˢ in u 
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fld
            with fld.(ftype) :=
            {
            | [ _ ] := (f, Array [seq {- (⟦ β ++ merge_selection_sets (find_valid_fields_with_response_name s f u.(ntype) φ) ⟧ˢ in v) -} | v <- neighbors_with_label g u (Label f α)])
                              :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
            | NamedType _
                with ohead (neighbors_with_label g u (Label f α)) :=
                {
                | Some v => (f, {- (⟦ β ++ merge_selection_sets (find_valid_fields_with_response_name s f u.(ntype) φ) ⟧ˢ in v) -}) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
                
                | _ =>  (f, Leaf None) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u
                }
            };

        | None => ⟦ φ ⟧ˢ in u (* Should throw error *)
        };

      ⟦ l:f[[α]] { β } :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fld
            with fld.(ftype) :=
            {
            | [ _ ] := (l, Array [seq {- (⟦ β ++ merge_selection_sets (find_valid_fields_with_response_name s l u.(ntype) φ) ⟧ˢ in v) -} | v <- neighbors_with_label g u (Label f α)])
                              :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
            | NamedType _
                with ohead (neighbors_with_label g u (Label f α)) :=
                {
                | Some v => (l, {- (⟦ β ++ merge_selection_sets (find_valid_fields_with_response_name s l u.(ntype) φ) ⟧ˢ in v) -}) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
                
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
    all: do [leq_selections_size].
  Qed.

  
  (** ** Execute Query
      (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Query'><span>&#167;</span>6.2.1</a>#)
      ----

      Evaluates the query, starting from the graph's root node.
      
  *)
  Definition execute_query (q : query) :=
    execute_selection_set g.(root) q.(selection_set).
  

  


  (** * Simplified Semantics *)
  (** ---- *)
  Reserved Notation "≪ queries ≫ 'in' u" (at level 50).
  
  (** *** Simplified evaluation of selections 
      ---- 
      
      Evaluates a list of selections and returns a GraphQL Response. 

      The definition is partially based on H&P's simplified semantics.
   *)
  Equations? simpl_execute_selection_set u queries :
    @GraphQLResponse Scalar by wf (selections_size queries) :=
    {
      ≪ [::] ≫ in _ := [::];

      ≪ f[[α]] :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
          | Some fdef := (f, complete_value fdef.(ftype) (property u (Label f α)))
                          :: ≪ φ ≫ in u;
          
          | _ := ≪ φ ≫ in u (* Should throw error *)
        };
      
      ≪ l:f[[α]] :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
            {
            | Some fdef := (l, complete_value fdef.(ftype) (property u (Label f α)))
                            :: ≪ φ ≫ in u;
            
            | _ := ≪ φ ≫ in u (* Should throw error *)
            };

      
      ≪ f[[α]] { β } :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some fld
            with fld.(ftype) :=
            {
            | ListType _ => (f, Array [seq {- ≪ β ≫ in v -} | v <- neighbors_with_label g u (Label f α)]) :: ≪ φ ≫ in u;
        
            | NamedType ty
                with ohead (neighbors_with_label g u (Label f α)) :=
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
            with fld.(ftype) :=
            {
            | ListType _ => (l, Array [seq {- ≪ β ≫ in v -} | v <- neighbors_with_label g u (Label f α)]) :: ≪ φ ≫ in u;
        
            | NamedType ty
                with ohead (neighbors_with_label g u (Label f α)) :=
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
    all: do [leq_selections_size].
  Qed.

  (** Simplified evaluation of queries
      ----
      
      Evaluates a query, starting from the graph's root node.
   *)
  Definition simpl_execute_query (q : @query Scalar) :=
    ≪ q.(selection_set) ≫ in g.(root).
  

End QuerySemantic.

(* begin hide *)
Arguments complete_value [Scalar].
Arguments execute_selection_set [Scalar].
Arguments execute_query [Scalar].
Arguments simpl_execute_selection_set [Scalar].
Arguments simpl_execute_query [Scalar].
(* end hide *)

Delimit Scope query_eval with QEVAL.
Open Scope query_eval.



(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.NormalFormLemmas.html' class="btn btn-light" role='button'>Previous ← Normal Form Proofs</a>
        <a href='GraphCoQL.theory.QuerySemanticsLemmas.html' class="btn btn-info" role='button'>Continue Reading → Semantics Proofs</a>
    </div>#
*)
