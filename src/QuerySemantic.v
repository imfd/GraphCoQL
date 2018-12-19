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
Require Import NRGTNF.

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
  


  Fixpoint indexed_β (results : seq (@Result Name Vals)) (filter : @Result Name Vals) (index : nat) : seq (@Result Name Vals) :=
    match results with
    | [::] => [::]
    | hd :: tl =>
      match hd, filter with
      | NestedListResult l rs, NestedListResult l' _ =>
        if l == l' then
          let: Response χ := (nth (Response [::]) rs index) in
          χ ++ (indexed_β tl filter index)
        else
          indexed_β tl filter index
        | _, _ => (indexed_β tl filter index)
      end 
    end.
  

  Fixpoint β (results : seq (@Result Name Vals)) (filter : @Result Name Vals) : seq (@Result Name Vals) :=
    match results with
    | [::] => [::]
    | hd :: tl =>
      match hd, filter with
      | NestedResult l r, NestedResult l' _ => if l == l' then
                                                let: Response χ := r in
                                                χ ++ (β tl filter)
                                              else
                                                β tl filter
      | _, _ => β tl filter
      end
    end.
  

  Definition γ (results : seq (@Result Name Vals)) (f : @Result Name Vals) : seq (@Result Name Vals) :=
    let partially_equal (result filter : @Result Name Vals) : bool :=
        match result, filter with
        | SingleResult l v, SingleResult l' v' => (l == l') && (v == v')
        | ListResult l v, ListResult l' v' => (l == l') && (v == v')
        | NestedResult l _, NestedResult l' _ => l == l' 
        | NestedListResult l _, NestedListResult l' _ => l == l'
        | _, _ => false
        end
    in
    filter (fun r => ~~(partially_equal r f)) results.
      

  Program Fixpoint collect (results : seq (@Result Name Vals)) {measure (results_size results)} : seq (@Result Name Vals) :=
    match results with
    | [::] => [::]
    | hd :: tl =>
      match hd with
      | NestedResult l (Response σ) => (NestedResult l (Response (collect (σ ++ (β tl hd)))))
                                        :: (collect (γ tl hd))
      | NestedListResult l rs => (NestedListResult l
                                   (indexed_map
                                      (fun (i : nat) (r : ResponseObject) =>
                                         let: Response r := r in
                                         Response (collect (r ++ (indexed_β tl hd i))))
                                      rs))
                                  :: (collect (γ tl hd))
      | _ => hd :: (collect (γ tl hd))
      end
    end.
  Admit Obligations.

  Lemma collect_eq : forall r, collect r =
                          match r with
    | [::] => [::]
    | hd :: tl =>
      match hd with
      | NestedResult l (Response σ) => (NestedResult l (Response (collect (σ ++ (β tl hd)))))
                                        :: (collect (γ tl hd))
      | NestedListResult l rs => (NestedListResult l
                                   (indexed_map
                                      (fun (i : nat) (r : ResponseObject) =>
                                         let: Response r := r in
                                         Response (collect (r ++ (indexed_β tl hd i))))
                                      rs))
                                  :: (collect (γ tl hd))
      | _ => hd :: (collect (γ tl hd))
      end
    end.
    Proof. Admitted.
    
    Implicit Type schema : @wfSchema Name Vals.
    Implicit Type graph : @graphQLGraph N Name Vals.
    Implicit Type u : @node N Name Vals.
    Implicit Type selection : @SelectionSet Name Vals.
    Implicit Type query : @Query Name Vals.
    
    Fixpoint eval schema graph u selection : @ResponseObject Name Vals :=
      match selection with
      | Selection queries  =>
        let fix loop rs :=
            match rs with
            | [::] => [::]
            | hd :: tl =>
              let res := eval_query schema graph u hd in
              match res with
              | inl r => r :: (loop tl)
              | inr (Response r) => r ++ (loop tl)
              end
            end
        in
         Response (collect (loop queries))
      end
    with eval_query schema graph u query : (@Result Name Vals) + @ResponseObject Name Vals :=
           match query with
           | SingleField name args => match u.(fields) (Field name args) with
                                     | Some (inl value) => inl (SingleResult name value)
                                     | _ => inl (Null name)
                                     end
           | LabeledField label name args =>  match u.(fields) (Field name args) with
                                             | Some (inl value) => inl (SingleResult label value)
                                             | _ => inl (Null name)
                                             end
           | NestedField name args ϕ => let target_nodes := get_target_nodes_with_field graph u (Field name args) in
                                       match lookup_field_type schema (NamedType u.(type)) name with
                                       | Some (ListType _) =>
                                         inl (NestedListResult name (map (fun v => eval schema graph v ϕ) target_nodes))
                                       | Some (NamedType _) =>
                                         match ohead target_nodes with
                                         | Some v => inl (NestedResult name (eval schema graph v ϕ))
                                         | _ => inl (Null name)
                                         end
                                       | _ => inl (Null name)         (* If the field ∉ fields(u) then it's null, right? *)
                                       end
                                         
           | NestedLabeledField label name args ϕ =>  let target_nodes := get_target_nodes_with_field graph u (Field name args) in
                                                      match lookup_field_type schema (NamedType u.(type)) name with
                                                      | Some (ListType _) =>
                                                        inl (NestedListResult label (map (fun v => eval schema graph v ϕ) target_nodes))
                                                      | Some (NamedType _) =>
                                                        match ohead target_nodes with
                                                        | Some v => inl (NestedResult label (eval schema graph v ϕ))
                                                        | _ => inl (Null name)
                                                        end
                                                      | _ => inl (Null name)       
                                                      end
           | InlineFragment t ϕ => match lookup_type schema (NamedType t) with
                                   | Some (ObjectTypeDefinition _ _ _) => if t == u.(type) then
                                                                            inr (eval schema graph u ϕ)
                                                                          else
                                                                            inl Empty
                                   | Some (InterfaceTypeDefinition _ _) => if declares_implementation schema (NamedType u.(type)) (NamedType t) then
                                                                             inr (eval schema graph u ϕ)
                                                                           else
                                                                             inl Empty
                                   | Some (UnionTypeDefinition _ mbs) => if (NamedType u.(type)) \in mbs then
                                                                           inr (eval schema graph u ϕ)
                                                                         else
                                                                           inl Empty
                                   | _ =>  inl Empty
                                   end
           end.


    Definition eval_selection schema  (g : @conformedGraph N Name Vals schema) (selection : @conformedQuery Name Vals schema) : @ResponseObject Name Vals :=
      let: ConformedQuery selection _ := selection in
      eval schema g.(graph) g.(graph).(root) selection.



    Fixpoint eval'  schema graph u selection : @ResponseObject Name Vals :=
      match selection with
      | Selection queries  =>
        let fix loop rs :=
            match rs with
            | [::] => [::]
            | hd :: tl =>
              let res := eval_query' schema graph u hd in
              match res with
              | inl r => r :: (loop tl)
              | inr (Response r) => r ++ (loop tl)
              end
            end
        in
         Response (loop queries)
      end
    with eval_query' schema graph u query : (@Result Name Vals) + @ResponseObject Name Vals :=
           match query with
           | SingleField name args => match u.(fields) (Field name args) with
                                     | Some (inl value) => inl (SingleResult name value)
                                     | _ => inl (Null name)
                                     end
           | LabeledField label name args =>  match u.(fields) (Field name args) with
                                             | Some (inl value) => inl (SingleResult label value)
                                             | _ => inl (Null name)
                                             end
           | NestedField name args ϕ => let target_nodes := get_target_nodes_with_field graph u (Field name args) in
                                       match lookup_field_type schema (NamedType u.(type)) name with
                                       | Some (ListType _) =>
                                         inl (NestedListResult name (map (fun v => eval' schema graph v ϕ) target_nodes))
                                       | Some (NamedType _) =>
                                         match ohead target_nodes with
                                         | Some v => inl (NestedResult name (eval' schema graph v ϕ))
                                         | _ => inl (Null name)
                                         end
                                       | _ => inl (Null name)         (* If the field ∉ fields(u) then it's null, right? *)
                                       end
                                         
           | NestedLabeledField label name args ϕ =>  let target_nodes := get_target_nodes_with_field graph u (Field name args) in
                                                      match lookup_field_type schema (NamedType u.(type)) name with
                                                      | Some (ListType _) =>
                                                        inl (NestedListResult label (map (fun v => eval' schema graph v ϕ) target_nodes))
                                                      | Some (NamedType _) =>
                                                        match ohead target_nodes with
                                                        | Some v => inl (NestedResult label (eval' schema graph v ϕ))
                                                        | _ => inl (Null name)
                                                        end
                                                      | _ => inl (Null name)       
                                                      end
           | InlineFragment t ϕ => match lookup_type schema (NamedType t) with
                                   | Some (ObjectTypeDefinition _ _ _) => if t == u.(type) then
                                                                            inr (eval' schema graph u ϕ)
                                                                          else
                                                                            inl Empty
                                   | Some (InterfaceTypeDefinition _ _) => if declares_implementation schema (NamedType u.(type)) (NamedType t) then
                                                                             inr (eval' schema graph u ϕ)
                                                                           else
                                                                             inl Empty
                                   | Some (UnionTypeDefinition _ mbs) => if (NamedType u.(type)) \in mbs then
                                                                           inr (eval' schema graph u ϕ)
                                                                         else
                                                                           inl Empty
                                   | _ =>  inl Empty
                                   end
           end.


    Definition eval_nrgtnf schema  (g : @conformedGraph N Name Vals schema) (selection : @normalizedConformedQuery Name Vals schema) : @ResponseObject Name Vals :=
      let: NCQuery (NormalizedSelection s _ _) _ := selection in
        eval' schema g.(graph) g.(graph).(root) s.
     
        

End QuerySemantic.