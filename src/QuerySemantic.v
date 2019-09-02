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
Require Import GraphAux.
Require Import GraphConformance.


Require Import QueryTactics.

(* end hide *)


Section QuerySemantic.

  Variables Vals : eqType.
  
  
  Variable s : @wfGraphQLSchema Vals.
  Variable g : @conformedGraph Vals s.
  
  Implicit Type u : @node Vals.
  Implicit Type query : @Query Vals.
  Implicit Type queries : seq (@Query Vals).

 

  Reserved Notation "⟦ φ ⟧ˢ 'in' u" (at level 40).

  (**
     execute_selection_set : Node → List Query → List (Name * ResponseNode)

     Evaluates the list of queries and returns a list of named response nodes.
     
     This definition follows closely what is defined in the semantics of J&O, 
     particularly regarding the use of the underlying graph model. What this 
     means in concrete is :
     
     1. Simple field selection : Simple fields represent accessing a node's
        properties.

     2. Nested field selection : Nested fields represent traversals from one 
        node to a neighbouring node. 

       
     The main difference with their semantics is that the field collection is 
     carried at the queries level, instead of collecting the responses. This
     field collection attempts to be the closest possible to how it is defined 
     in the specification.
     
     One of the main difference with the specification is that they collect fields at 
     the beginning of the process, generating a mapping between response names 
     and every query that has that name. Over that list they proceed to evaluate 
     and later evaluate subqueries when it is appropriate.
    
     In our approach, we perform everything in a single pass, without the pre-grouping
     step. When a field is going to be evaluated, we may collect similar fields
     in the tail of the list (to extract their subqueries) and then filter them, 
     in order to not reevaluate them.

     Another important difference, which relates to the use of the graph model, 
     is that list types with more than one level of nesting are taken as if 
     they had only one level of nesting.
     
     Example: 
              my_nested_field : [[[MyType]]]
             
             is taken as if it were simply:
             
             my_nested_field : [MyType]

     
     The reason behind this is that in the setting of J&O and their graph model, 
     it is not clear what a nested list type represent in the graph. A one-level 
     nesting represents a traversal to all neighbouring nodes with an edge labeled 
     with the current field. It is not clear what a n-nested list would represent;
     is the first step a traversal to a blank node ? Is each edge labeled as well ?
     etc.
     
     We chose to implement this semantics which partially satisfies both the specification and 
     J&O work, knowing that it is not the actual semantics. One can understand this 
     approach as a particular instance of a GraphQL system, where we are restricted 
     to list types having only one level of nesting.

     Finally, another difference is that we are not currently handling errors.



     ⟦ [] ⟧ᵘ := [] 
                                ⎧
     ⟦ f[α] :: φ_1 ... φ_n ⟧ᵘ = ⎨   (f : u.fields (f[α])) :: ⟦ filter f (φ_1 ... φ_n) ⟧ᵘ
                                |      if (lookup (f) =  f (Args) : rty) ∧ u.fields (f[α]) = value (value ∈ Vals + List Vals)
                                |
                                |   (f : null) :: ⟦ filter f (φ_1 ... φ_n) ⟧ᵘ
                                |      if (lookup (f) =  f (Args) : rty) ∧ u.fields (f[α]) = ⊥
                                |
                                |   ⟦ φ_1 ... φ_n ⟧ᵘ 
                                |      if (lookup (f) = ⊥)
                                ⎩

                                
                                                ⎧
     ⟦ f[α] { β_1 ... β_k } :: φ_1 ... φ_n ⟧ᵘ = ⎨   (f : [ { ⟦ merge (collect f (φ_1 ... φ_n)) ⟧ᵛ¹ } ... { ⟦ merge (collect f (φ_1 ... φ_n)) ⟧ᵛʲ} ]) :: ⟦ filter f (φ_1 ... φ_n) ⟧ᵘ
                                                |      if (lookup (f) =  f (Args) : rty) ∧ rty ∈ Lt ∧ (v_1 ... v_j) = {v_i | (u, f[α], v_i) ∈ graph.edges}
                                                |
                                                |   (f : { ⟦ merge (collect f (φ_1 ... φ_n)) ⟧ᵛ }) :: ⟦ filter f (φ_1 ... φ_n) ⟧ᵘ
                                                |      if (lookup (f) = f (Args) : rty) ∧ rty ∉ Lt ∧ (u, f[α], v) ∈ graph.edges
                                                |
                                                |   (f : null) :: ⟦ filter f (φ_1 ... φ_n) ⟧ᵘ
                                                |      if (lookup (f) =  f (Args) : rty) ∧ rty ∉ Lt ∧ ∄ v, (u, f[α], v) ∈ graph.edges
                                                |
                                                |   ⟦ φ_1 ... φ_n ⟧ᵘ 
                                                |      if (lookup (f) = ⊥)
                                                ⎩

                                                
                                                ⎧
     ⟦ on t { β_1 ... β_k } :: φ_1 ... φ_n ⟧ᵘ = ⎨    ⟦ β_1 ... β_k ++ φ_1 ... φ_n ⟧ᵘ             if (does_fragment_type_apply u.type t)
                                                |
                                                |
                                                |    ⟦ φ_1 ... φ_n ⟧ᵘ                            ~
                                                ⎩
     ---- 
     See also:

     https://graphql.github.io/graphql-spec/June2018/#sec-Executing-Selection-Sets

     https://graphql.github.io/graphql-spec/June2018/#CollectFields()

     https://graphql.github.io/graphql-spec/June2018/#ExecuteField()

     https://graphql.github.io/graphql-spec/June2018/#sec-Value-Resolution

     https://graphql.github.io/graphql-spec/June2018/#ResolveFieldValue()
   *)
  Equations? execute_selection_set u (queries : seq (@Query Vals)) :
    
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      ⟦ [::] ⟧ˢ in _ := [::];
      
      ⟦ f[[α]] :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some _
            with field_seq_value u.(nfields) (Field f α) :=
            {
            | Some (inl value) => (f, Leaf (Some value)) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
            | Some (inr values) => (f, Array (map (fun value => Leaf (Some value)) values)) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
            | None => (f, Leaf None) :: ⟦ filter_queries_with_label f φ ⟧ˢ in u  (* Should throw error? *)
            };
        | _ := ⟦ φ ⟧ˢ in u (* Should throw error *)
        };
      
      ⟦ l:f[[α]] :: φ ⟧ˢ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some _
            with field_seq_value u.(nfields) (Field f α) :=
            {
            | Some (inl value) => (l, Leaf (Some value)) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
            | Some (inr values) => (l, Array (map (fun value => Leaf (Some value)) values)) :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
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
            | [ _ ] := (f, Array [seq {- (⟦ β ++ merge_selection_sets (find_queries_with_label s f u.(ntype) φ) ⟧ˢ in v) -} | v <- neighbours_with_field g u (Field f α)])
                              :: ⟦ filter_queries_with_label f φ ⟧ˢ in u;
            | NamedType _
                with ohead (neighbours_with_field g u (Field f α)) :=
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
            | [ _ ] := (l, Array [seq {- (⟦ β ++ merge_selection_sets (find_queries_with_label s l u.(ntype) φ) ⟧ˢ in v) -} | v <- neighbours_with_field g u (Field f α)])
                              :: ⟦ filter_queries_with_label l φ ⟧ˢ in u;
            | NamedType _
                with ohead (neighbours_with_field g u (Field f α)) :=
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

  (**
     execute_selection_set2 : Node → List Query → List (Name * ResponseNode)

     Evaluates a list of queries, assuming they are in normal form (grounded and non-redundant).

     This corresponds to the definition given by J&O.
   *)
  (* TODO : Rename ! *)
  Equations? execute_selection_set2 u queries :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      ≪ [::] ≫ in _ := [::];

      ≪ f[[α]] :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some _ 
            with field_seq_value u.(nfields) (Field f α) :=
            {
            | Some (inl value) => (f, Leaf (Some value)) :: ≪ φ ≫ in u;
            | Some (inr values) => (f, Array (map (fun value => Leaf (Some value)) values)) :: ≪ φ ≫ in u;
            | None => (f, Leaf None) :: ≪ φ ≫ in u
            };
        | _ := ≪ φ ≫ in u (* Error *)
        };
      
      ≪ l:f[[α]] :: φ ≫ in u
        with lookup_field_in_type s u.(ntype) f :=
        {
        | Some _ 
            with field_seq_value u.(nfields) (Field f α) :=
            {
            | Some (inl value) => (l, Leaf (Some value)) :: ≪ φ ≫ in u;
            | Some (inr values) => (l, Array (map (fun value => Leaf (Some value)) values)) :: ≪ φ ≫ in u;
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
            | ListType _ => (f, Array [seq {- ≪ β ≫ in v -} | v <- neighbours_with_field g u (Field f α)]) :: ≪ φ ≫ in u;
        
            | NamedType ty
                with ohead (neighbours_with_field g u (Field f α)) :=
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
            | ListType _ => (l, Array [seq {- ≪ β ≫ in v -} | v <- neighbours_with_field g u (Field f α)]) :: ≪ φ ≫ in u;
        
            | NamedType ty
                with ohead (neighbours_with_field g u (Field f α)) :=
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

  
 


  
  

        
  
  (**
     resolve_field_value : Node → Name → List (Name * Vals) ↪ Vals + List Vals 

     Attempt at replicating the specification's definition of _ResolveFieldValue_ 
     instantiated to the graph setting.

     ---- 
     See also:

     https://graphql.github.io/graphql-spec/June2018/#ResolveFieldValue()
   *)
  Equations resolve_field_value u (field_name : Name) (argument_values : seq (Name * Vals)) : option ((Vals + seq Vals) + (@node Vals) + seq (@node Vals)) :=
    {
      resolve_field_value u f α
        with field_seq_value u.(nfields) (Field f α) :=
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
  (* Equations? execute_selection_set3 u (queries : seq (@Query Vals)) : *)
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
         
  Equations? Equiv  (ty : Name) (φ1 φ2 : seq (@Query Vals)) : bool by wf (queries_size φ1 + queries_size φ2) :=
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

Arguments execute_selection_set [Vals].
Arguments execute_selection_set2 [Vals].

Delimit Scope query_eval with QEVAL.
Open Scope query_eval.

(* This notation collides with the pairs notation (_ , _) ...  *)
Notation "s , g ⊢ ⟦ φ ⟧ˢ 'in' u" := (execute_selection_set s g u φ) (at level 30, g at next level, φ at next level) : query_eval.
Notation "s , g ⊢ ≪ φ ≫ 'in' u" := (execute_selection_set2 s g u φ) (at level 30, g at next level, φ at next level) : query_eval.