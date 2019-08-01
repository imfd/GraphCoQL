From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.


Require Import Schema.
Require Import SchemaWellFormedness.
Require Import SchemaAux.
Require Import Graph.
Require Import GraphAux.

Require Import SeqExtra.

Section Conformance.


  Variables (N Name Vals: ordType).

  
  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type graph : @graphQLGraph Name Vals. 


  (** 
      It states that a Graph's root must have the same type as the Schema's root
   **)
  Definition root_type_conforms schema graph : bool := graph.(root).(type) == schema.(query_type).
  


  (** 
      It states whether a given field's argument conforms to 
      what the Schema requires of it.

      Given a node's type 'ty', one of the nodes' field name 'f' and an argument (argname, value).
     
     1. argname ∈ args (src, f) : The argument must be declared in the given type for that given field.
     2. value ∈ values (type (arg)) : The value must be of the type declared for that argument in the schema.  
 
   **)     
  Definition argument_conforms schema (ty fname : Name) (arg : Name * Vals) : bool :=
    let: (argname, value) := arg in
    match lookup_argument_in_type_and_field schema ty fname argname with
    | Some field_arg => (hasType schema) field_arg.(argtype) value    (* If the argument is declared then check its value's type *)
    | _ => false
    end.


  (** Checks whether all of the field's arguments conform to the schema **)
  Definition arguments_conform schema ty (f : fld) : bool :=
    all (argument_conforms schema ty f.(label)) f.(args).
 

  Lemma argument_conformsP schema ty fname arg :
    reflect (exists2 fld_arg, lookup_argument_in_type_and_field schema ty fname arg.1 = Some fld_arg & schema.(hasType) fld_arg.(argtype) arg.2)
            (argument_conforms schema ty fname arg).
  Proof.
    apply: (iffP idP); rewrite /argument_conforms; case: arg => argname value.
    - case Hlook : lookup_argument_in_type_and_field => [arg|] // Hty.
        by exists arg.
    - by case=> fld_arg Hlook Hty; rewrite Hlook.
  Qed.
    
    


  
  (** 
      It checks whether a field's unwrapped type (if it's List type) and a type 
      conform.

      This is used when checking that an edge conforms to a Schema (see next definition).
   **)
  Definition field_type_conforms schema (field_type target_type : Name) : bool :=
    is_subtype schema (NT target_type) (NT field_type).


  
  (**
     It states whether an edge conforms to the Schema.
     An edge corresponds to a type's field whose type is another Object, Interface or Union type.

     ∀ u v ∈ N, f[α] ∈ fld, (u, f[α], v) ∈ E:

     1. f ∈ fields (τ(u)) :
          field 'f' has to be a field of that node's type in the Schema.

     2. type (f) = τ(v) ∨ τ(v) ∈ implementation (type (f)) ∨ τ(v) ∈ union (type (f)) , ie, is a subtype :
          The type associated to 'f' in the schema has to be the same type associated to node 'v'
       OR the type of 'f' is an Interface type therefore the type of 'v' has to be of an 
            object which implements this interface
       OR the type of 'f' is a Union type, therefore the type of 'v' has to be an Object type
            which is included in that union type.

     3. type (f) ∉ Lt → ∀ w ∈ N, (u, f[α], w) ∈ E → w = v : 
          If the type associated to field 'f' is not of List type,
          then node 'v' is the only node associated to 'u' via an edge with 'f'.

     4. The arguments of 'f' must conform to what the Schema requires of them, for
        that given field.

   **)
  Definition edge_conforms schema graph (edge : node * fld * (@node Name Vals)) : bool :=
    let: (src, fld, target) := edge in
    match lookup_field_in_type schema src.(type) fld.(label) with
    | Some fdef => [&& (* is_subtype schema (NT target.(type)) fdef.(return_type), *) (* wrong... right? *)
                     target.(type) \in get_possible_types schema fdef.(return_type),
                   (is_list_type fdef.(return_type) || is_field_unique_for_src_node graph src fld) &
                   arguments_conform schema src.(type) fld]
    | _ => false
    end.

  
  Definition edges_conform schema graph :=
    uniq graph.(E) && all (edge_conforms schema graph) graph.(E).

  
  (**
     It states whether a field conforms to the Schema.

     ∀ u ∈ N, f ∈ fld, v ∈ Vals ⋃ [Vals], λ (u, f[α]) = v 
     then it must be that:
     1. f ∈ fields (τ(u)) : 
          Field 'f' must be declared in the type associated to node 'u' in the Schema.

     2. v ∈ values (type (f)) :
          The value must be of the type declared for that field in the Schema.
    
     3. The arguments of 'f' must conform to what the Schema requires of them.

   **)

  Definition field_conforms schema ty (fd : fld * (Vals + seq Vals)) : bool :=
    match lookup_field_in_type schema ty fd.1.(label) with
    | Some fdef =>
      arguments_conform schema ty fd.1 &&
      match fd.2 with
      | (inl value) => hasType schema fdef.(return_type) value
      | (inr values) => all (hasType schema fdef.(return_type)) values
      end
    | _ => false
    end.
  
  Definition node_fields_conform schema (u : node) :=
    all (field_conforms schema u.(type)) u.(fields).

  
  Definition fields_conform schema graph :=
    all (node_fields_conform schema) graph.(nodes).

  
  Definition nodes_have_object_type schema graph : bool :=
    all (fun node : node => is_object_type schema node.(type)) graph.(nodes).

  
  Lemma nodes_have_object_typeP schema graph :
    reflect (forall node, node \in graph.(nodes) -> is_object_type schema node.(type))
            (nodes_have_object_type schema graph).
  Proof. by apply: (iffP allP). Qed.

  (**
     A GraphQL graph conforms to a given Schema if:
     1. Its root conforms to the Schema.
     2. Its edges conform to the Schema.
     3. Its fields conform to the Schema.
     4. Its nodes conform to the Schema.

   **)
  Record conformedGraph schema := ConformedGraph {
                                                graph;
                                                _ : root_type_conforms schema graph;
                                                _ : edges_conform schema graph;
                                                _ : fields_conform schema graph;
                                                _ : nodes_have_object_type schema graph
                                      }.

  Coercion graph_of_conformed_graph schema (g : conformedGraph schema) := let: ConformedGraph g _ _ _ _ := g in g.


  Lemma aux_root_query_type schema graph :
    root_type_conforms schema graph -> graph.(root).(type) = schema.(query_type).
  Proof. by rewrite /root_type_conforms; move/eqP. Qed.
  
  Lemma root_query_type schema (graph : conformedGraph schema) :
    graph.(root).(type) = schema.(query_type).
  Proof.
    case: graph => g H *.
      by move: (aux_root_query_type H).
  Qed.

  Lemma node_in_graph_has_object_type schema (graph : conformedGraph schema) :
    forall u, u \in graph.(nodes) -> is_object_type schema u.(type).
  Proof.
    apply/nodes_have_object_typeP.
    by case: graph.
  Qed.

  Lemma neighbours_are_subtype_of_field schema (graph : conformedGraph schema) u fld fdef  :
    lookup_field_in_type schema u.(type) fld.(label) = Some fdef ->
    forall v, v \in neighbours_with_field graph u fld ->
               v.(type) \in get_possible_types schema fdef.(return_type).
  Proof.
    move=> Hlook.
    case: graph => g Hroot Hedges.
    
    have Hedge : forall e, e \in g.(E) -> edge_conforms schema g e.
      by apply/allP; move: Hedges; rewrite /edges_conform; case/andP.

    move=> Hflds Hobjs v.
    rewrite /neighbours_with_field -in_undup => /mapP [v'].
    rewrite mem_filter => /andP [/andP [/eqP Hsrc /eqP Hfld] Hin] Htrgt.    
    move: (Hedge v' Hin).
    rewrite /edge_conforms /=.
    case: v' Hsrc Hfld Hin Htrgt => //=.
    case=> //= src fld' v' -> -> Hin ->.
      by rewrite Hlook /=; case/and3P.
  Qed.
    
               
    

End Conformance.

Arguments conformedGraph [Name Vals]. 