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

Section Conformance.


  Variables (N Name Vals: ordType).

  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type graph : @graphQLGraph N Name Vals. 


  (** 
      It states that a Graph's root must have the same type as the Schema's root
   **)
  Definition root_type_conforms schema graph := graph.(root).(type) = SchemaAux.query_root(schema).
  


  (** 
      It states whether a given field's arguments conform to 
      what the Schema requires of them.

      Given a schema type 'src', a graph field 'f' with a partial mapping α.
      ∀ v ∈ Vals, arg ∈ dom(α) st. α(arg) = v
      
      1. arg ∈ args (src, f) : The argument must be declared in the given type for that given field.
      2. v ∈ values (type (arg)) : The value must be of the type declared for that argument in the schema.  
 
   **)
  Definition arguments_conform schema (srcNode : @node N Name Vals) (f : fld) :=
    let argumentConforms arg :=
        let: (argname, value) := arg in
        match lookup_argument_in_type_and_field schema (NamedType srcNode.(type)) f argname with
        | Some (FieldArgument _ ty) => (hasType schema) ty value    (* If the argument is declared then check its value's type *)
        | _ => false
        end
    in
    all argumentConforms f.(args).
  
    


  
  (** 
      It checks whether a field's unwrapped type (if its List type) and a type 
      conform.

      This is used when checking that an edge conforms to a Schema (see next definition).
   **)
  Definition field_type_conforms schema (fieldType targetType : Name) : bool :=
    (fieldType == targetType) ||
    (declares_implementation schema (NamedType targetType) (NamedType fieldType)) ||
    ((NamedType targetType) \in (union_members schema (NamedType fieldType))).


  
  (**
     It states whether an edge conforms to the Schema.
     An edge corresponds to a type's field whose type is another Object, Interface or Union type.

     ∀ u v ∈ N, f[α] ∈ fld, (u, f[α], v) ∈ E:

     1. f ∈ fields (τ(u)) :
          field 'f' has to be a field of that node's type in the Schema.

     2. type (f) = τ(v) ∨ τ(v) ∈ implementation (type (f)) ∨ τ(v) ∈ union (type (f)) : 
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
  Definition edges_conform schema (E : {fset node * fld * node}) :=
    let edgeConforms edge :=
        let: (u, f, v) := edge in
        match lookup_field_type schema (NamedType u.(type)) f.(label) with    (* Check if field is declared in type *)
        | Some fieldType => (field_type_conforms schema fieldType v.(type)) &&
                           (is_list_type fieldType || is_label_unique_for_src_node E u f) &&
                           arguments_conform schema u f
        | _ => false
        end
    in
    all edgeConforms E.

  
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
  Definition node_fields_conform schema (u : node) :=
    let fieldConforms f :=
        let: (f', vals) := f in
        match lookup_field_type schema (NamedType u.(type)) f'.(label) with
        | Some fieldType =>                (* Field is declared in the node's type *)
          arguments_conform schema  u f' &&    
                           match vals with
                           | (inl value) => hasType schema fieldType value
                           | (inr values) => all (hasType schema fieldType) values
                           end
        | _ => false
        end
    in
    all fieldConforms u.(fields).

  
  Definition fields_conform schema graph :=
    all (node_fields_conform schema) (graph_s_nodes graph).


  
  Definition has_object_type schema (n : @node N Name Vals) :=
    let: Node _ t _ := n in is_object_type schema (NamedType t).



  Definition nodes_have_object_type schema graph :=
    all (has_object_type schema) (graph_s_nodes graph).

                                                                     

  (**
     A GraphQL graph conforms to a given Schema if:
     1. Its root conforms to the Schema.
     2. Its edges conform to the Schema.
     3. Its fields conform to the Schema.
     4. Its nodes conform to the Schema.

   **)
  Structure conformedGraph schema := ConformedGraph {
                                                graph;
                                                _ : root_type_conforms schema graph;
                                                _ : edges_conform schema graph.(E);
                                                _ : fields_conform schema graph;
                                                _ : nodes_have_object_type schema graph
                                      }.

  Coercion graph_of_conformed_graph schema (g : conformedGraph schema) := let: ConformedGraph g _ _ _ _ := g in g.


End Conformance.

Arguments conformedGraph [N Name Vals]. 