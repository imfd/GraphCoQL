From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fmap.

Require Import SchemaWellFormedness.
Require Import Conformance.
Require Import QueryConformance.
Require Import SchemaAux.
Require Import GraphAux.

Require Import Schema.
Require Import Query.
Require Import Graph.



Section QuerySemantic.

  Variables N Name Vals : ordType.


  Fixpoint eval (schema : @wfSchema Name Vals)  (g : graphQLGraph) (u : @node N Name Vals) (query : Query) : @ResponseObject Name Vals :=
    match query with
    | SingleField name args => match u.(fields) (Field name args) with
                              | Some (inl value) => SingleResult name value
                              | _ => Null name
                              end
    | LabeledField label name args =>  match u.(fields) (Field name args) with
                                      | Some (inl value) => SingleResult label value
                                      | _ => Null name
                                      end
    | NestedField name args ϕ => let target_nodes := get_target_nodes_with_field g u (Field name args) in
                                match lookupFieldType schema u.(type) name with
                                | Some (ListType _) =>
                                  NestedListResult name (map (fun v => eval schema g v ϕ) target_nodes)
                                | Some (NamedType _) =>
                                  match ohead target_nodes with
                                  | Some v => (NestedResult name (eval schema g v ϕ))
                                  | _ => Null name
                                  end
                                | _ => Null name         (* If the field ∉ fields(u) then it's null, right? *)
                                end
                                    
    | NestedLabeledField label name args ϕ =>  let target_nodes := get_target_nodes_with_field g u (Field name args) in
                                match lookupFieldType schema u.(type) name with
                                | Some (ListType _) =>
                                  NestedListResult label (map (fun v => eval schema g v ϕ) target_nodes)
                                | Some (NamedType _) =>
                                  match ohead target_nodes with
                                  | Some v => (NestedResult label (eval schema g v ϕ))
                                  | _ => Null name
                                  end
                                | _ => Null name         
                                end
    | InlineFragment t ϕ => match lookupName schema t with
                           | Some (ObjectTypeDefinition _ _ _) => if t == u.(type) then
                                                                   eval schema g u ϕ
                                                                 else
                                                                   Empty
                           | Some (InterfaceTypeDefinition _ _) => if declaresImplementation schema (NamedType u.(type)) t then
                                                                    eval schema g u ϕ
                                                                  else
                                                                    Empty
                           | Some (UnionTypeDefinition _ mbs) => if (NamedType u.(type)) \in mbs then
                                                                  eval schema g u ϕ
                                                                else
                                                                  Empty
                           | _ => Empty
                           end
    | SelectionSet ϕ ϕ' => ResponseList (eval schema g u ϕ) (eval schema g u ϕ')
    end.


  Definition eval_query (schema : @wfSchema Name Vals)  (g : @conformedGraph N Name Vals schema) (query : @wfQuery Name Vals schema) : @ResponseObject Name Vals :=
    let: WFQuery query _ := query in
    eval schema g.(graph) g.(graph).(root) query.

    
      

End QuerySemantic.