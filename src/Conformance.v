From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.

Require Import List.
Import ListNotations.

Require Import Schema.
Require Import SchemaWellFormedness.
Require Import SchemaAux.
Require Import Graph.

Section Conformance.


  Variables (N  Name Vals: ordType).

  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type graph : @graphQLGraph N Name Name Name Vals. 


  (** 
      It states that a Graph's root must have the same type as the Schema's root
   **)
  Definition rootTypeConforms schema graph := forall t, (graph.(τ) graph.(r)) = Some t -> t = root(schema).
  (*
    match (graph.(τ) graph.(r)) with
    | Some t => t == unwrapTypeName (root(schema))
    | _ => false
    end. *)


  (** 
      It states whether a given field's arguments conform to 
      what the Schema requires of them.

      Given a schema type 'src', a graph field 'f' with a partial mapping α.
      ∀ v ∈ Vals, arg ∈ dom(α) st. α(arg) = v
      
      1. arg ∈ args (src, f) : The argument must be declared in the given type for that given field.
      2. v ∈ values (type (arg)) : The value must be of the type declared for that argument in the schema.  
 
   **)
  Definition argumentsConform schema (src : Name) (f : fld) : Prop :=
    forall arg value ty,
      (f arg) = Some value ->
      lookupArgument schema src arg f = Some (FieldArgument arg ty) ->
      (hasType schema) ty value.
    


  
  (** 
      It checks whether a field's unwrapped type (if its List type) and a type 
      conform.

      This is used when checking that an edge conforms to a Schema (see next definition).
   **)
  Definition fieldTypeConforms schema (fieldType targetType : Name) : bool :=
    (fieldType == targetType) ||
    (declaresImplementation schema targetType fieldType) ||
    (targetType \in (union schema fieldType)).


  
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
  Definition edgeConforms schema (E : {fset N * fld * N}) (t : {fmap N -> Name})   :=
    forall (u v : N) (f : fld) (fieldType : type) (ty ty': Name),
      (u, f, v) \in E ->
                    (t u) = Some ty ->
                    lookupFieldType schema ty (label f) = Some fieldType ->    (* This covers the field \in fields (t(u)) *)
                    (t v) = Some ty' ->
      (fieldTypeConforms schema (unwrapTypeName fieldType) ty') ->
      (~~isListType fieldType ->
       forall w, (u, f, w) \in E -> w == v) ->
      argumentsConform schema ty f.

  
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
  Definition fieldConforms schema (τ : {fmap N -> Name}) (λ : {fmap N * fld -> Vals + seq.seq Vals}) :=
    forall (u : N) (f : fld) (ty : type) (value : Vals) (lvalue : list Vals) (name : Name),
      (λ (u,f) = Some (inl value)) \/ (λ (u, f) = Some (inr lvalue)) ->
      (τ u) = Some name ->
      lookupFieldType schema name f = Some ty ->
      (hasType schema) ty value || all (hasType schema ty) lvalue ->
      argumentsConform schema ty f.


  (**
     It states whether τ conforms to the Schema.
     
     ∀ n ∈ N, τ(n) ∈ ObjectType(Schema) 

     In the paper this is directly encoded in τ's signature (N → Ot), 
     where they assume three distinct sets for type names: Ot, It and Ut.

   **)
  Definition tauConforms schema (τ : {fmap N -> Name}) : bool :=
    all (fun nt => let: (n, t) := nt in isObjectType schema (NamedType t)) τ.
 


  (**
     A GraphQL graph conforms to a given Schema if:
     1. Its root conforms to the Schema.
     2. Its edges conform to the Schema.
     3. Its fields conform to the Schema.
     4. Its τ conforms to the Schema.

   **)
  Record conformedGraph schema := ConformedGraph {
                                                graph;
                                                _ : rootTypeConforms schema graph;
                                                _ : edgeConforms schema (E graph) graph.(τ);
                                                _ : fieldConforms schema graph.(τ) graph.(λ);
                                                _ : tauConforms schema graph.(τ)
                                   }.


End Conformance.