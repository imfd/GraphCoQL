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
  
  
  Notation "'ϵ'" := Empty.
  Notation "l <- 'null'" := (Null l) (at level 50).
  Notation "l <- v" := (SingleResult l v) (at level 50).
  Notation "l <<- vals" := (ListResult l vals) (at level 50).
  Notation "l <- {{ ρ }}" := (NestedResult l ρ) (at level 40). 
  Notation "l <<- [{ ρ }]" := (NestedListResult l ρ) (at level 40).


  
  Section Map.
    
    Variables (T1 T2 : Type) (x2 : T2) (f : nat -> T1 -> T2) (s : seq T1).
    Definition indexed_map s :=
      let fix imap (f : nat -> T1 -> T2) (s : seq T1) i {struct s} : seq T2 :=
          if s is hd :: tl then (f i hd) :: imap f tl (i + 1) else [::]
      in
      imap f s 0.

  End Map.
  
  (**
     indexed_β_filter : seq ResponseObject -> ResponseObject -> nat -> seq ResponseObject
     
     Extracts the i-th nested result from the response objects that match with the filter
     response object.

   **)
  Fixpoint indexed_β_filter (responses : seq (@ResponseObject Name Vals)) (filter :  @ResponseObject Name Vals) (index : nat) : seq ResponseObject :=
    let indexed_β result filter index : seq ResponseObject :=
        match result, filter with
        | NestedListResult l rs, NestedListResult l' rs' =>
          if l == l' then
            let: Results σ := nth (Results [::]) rs index in
            σ
          else
            [::]
        | _, _ => [::]
        end
    in
    flatten [seq (indexed_β r filter index) | r <- responses].
    
  

  

  (**
     β_filter : ResponseObject -> seq ResponseObject -> seq ResponseObject
     
     Extracts nested results from results matching the filter response object.
   **)
  Fixpoint β_filter (filter : @ResponseObject Name Vals) (responses : seq (@ResponseObject Name Vals)) : seq ResponseObject :=
    let  β filter result : seq ResponseObject :=
         match result, filter with
         | NestedResult l (Results χ), NestedResult l' _ => if l == l' then χ  else [::]
         | _, _ => [::]
         end
    in
    flatten [seq (β filter r) | r <- responses].
  
  Fixpoint γ_filter (flt : @ResponseObject Name Vals) (responses : seq (@ResponseObject Name Vals)) : seq (@ResponseObject Name Vals) :=
    let γ flt result : bool :=
        match result, flt with
        | SingleResult l v, SingleResult l' v' => (l == l') && (v == v') 
        | ListResult l v, ListResult l' v' => (l == l') && (v == v') 
        | NestedResult l _, NestedResult l' _ => l == l' 
        | NestedListResult l _, NestedListResult l' _ => l == l'
        | _, _ => true
        end
    in
    filter (fun r => ~~(γ flt r)) responses.
  

  Program Fixpoint collect (responses : seq ResponseObject) {measure (responses_size responses)} : seq ResponseObject :=
    match responses with
    | [::] => [::]
    | hd :: tl =>
      match hd with
      | NestedResult l (Results σ) => (NestedResult l (Results (collect (σ ++ (β_filter hd tl)))))
                                       :: (collect (γ_filter hd tl))
      | NestedListResult l rs =>
        (NestedListResult l
           (indexed_map
              (fun i r =>
                 let: Results r := r in
                 Results (collect (r ++ (indexed_β_filter tl hd i))))
              rs))
          :: (collect (γ_filter hd tl))
      | _  => hd :: (collect (γ_filter hd tl))
      end
    end.     
  Admit Obligations.

  Lemma collect_eq : forall r, collect r =
                          match r with
                          | SingleResponse _ => r
                          | MultipleResponses hd tl =>
                            match hd with
                            | NestedResult l σ => MultipleResponses
                                                   (NestedResult l (collect (app_responses σ (β_filter hd tl))))
                                                   (collect (γ_filter hd tl))
                            | NestedListResult l rs => MultipleResponses
                                                        (NestedListResult l
                                                                          (indexed_map
                                                                             (fun i r => collect (app_responses r (indexed_β_filter tl hd i)))
                                                                             rs))
                                                        (collect (γ_filter hd tl))
                            | _ => MultipleResponses hd (collect (γ_filter hd tl))
                            end
                          end.
    Proof. Admitted.
    
    Implicit Type schema : @wfSchema Name Vals.
    Implicit Type graph : @graphQLGraph N Name Vals.
    Implicit Type u : @node N Name Vals.
    Implicit Type query_set : @QuerySet Name Vals.
    Implicit Type query : @Query Name Vals.
    
    Fixpoint eval schema graph u query_set : @Result Name Vals :=
      let: SelectionSet queries := query_set in
      let fix loop rs :=
          match rs with
          | [::] => [::]
          | hd :: tl =>
            let res := eval_query schema graph u hd in
            match res with
            | inl r => r :: (loop tl)
            | inr (Results r) => r ++ (loop tl)
            end
          end
      in
      Results (collect (loop queries))
               
    with eval_query schema graph u query : (@ResponseObject Name Vals) + @Result Name Vals :=
           match query with
           | SingleField name args => match u.(fields) (Field name args) with
                                     | Some (inl value) => SingleResponse (SingleResult name value)
                                     | _ => SingleResponse (Null name)
                                     end
           | LabeledField label name args =>  match u.(fields) (Field name args) with
                                             | Some (inl value) => SingleResponse (SingleResult label value)
                                             | _ => SingleResponse (Null name)
                                             end
           | NestedField name args ϕ => let target_nodes := get_target_nodes_with_field graph u (Field name args) in
                                       match lookup_field_type schema (NamedType u.(type)) name with
                                       | Some (ListType _) =>
                                         SingleResponse (NestedListResult name (map (fun v => eval schema graph v ϕ) target_nodes))
                                       | Some (NamedType _) =>
                                         match ohead target_nodes with
                                         | Some v => SingleResponse (NestedResult name (eval schema graph v ϕ))
                                         | _ => SingleResponse (Null name)
                                         end
                                       | _ => SingleResponse (Null name)         (* If the field ∉ fields(u) then it's null, right? *)
                                       end
                                         
           | NestedLabeledField label name args ϕ =>  let target_nodes := get_target_nodes_with_field graph u (Field name args) in
                                                      match lookup_field_type schema (NamedType u.(type)) name with
                                                      | Some (ListType _) =>
                                                        SingleResponse (NestedListResult label (map (fun v => eval schema graph v ϕ) target_nodes))
                                                      | Some (NamedType _) =>
                                                        match ohead target_nodes with
                                                        | Some v => SingleResponse (NestedResult label (eval schema graph v ϕ))
                                                        | _ => SingleResponse (Null name)
                                                        end
                                                      | _ => SingleResponse (Null name)         
                                                      end
           | InlineFragment t ϕ => match lookup_type schema (NamedType t) with
                                   | Some (ObjectTypeDefinition _ _ _) => if t == u.(type) then
                                                                            eval schema graph u ϕ
                                                                          else
                                                                            (SingleResponse Empty)
                                   | Some (InterfaceTypeDefinition _ _) => if declares_implementation schema (NamedType u.(type)) (NamedType t) then
                                                                             eval schema graph u ϕ
                                                                           else
                                                                             (SingleResponse Empty)
                                   | Some (UnionTypeDefinition _ mbs) => if (NamedType u.(type)) \in mbs then
                                                                           eval schema graph u ϕ
                                                                         else
                                                                           (SingleResponse Empty)
                                   | _ => SingleResponse Empty
                                   end
           end.


    Definition eval_query_set schema  (g : @conformedGraph N Name Vals schema) (selection : @conformedQuery Name Vals schema) : @ResponseObject Name Vals :=
      let: ConformedQuery selection _ := selection in
      eval schema g.(graph) g.(graph).(root) selection.

    
    

End QuerySemantic.