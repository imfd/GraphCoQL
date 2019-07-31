From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.

Require Import treeordtype.


Delimit Scope schema_scope with SCHEMA.
Open Scope schema_scope.

Section Schema.

  (**
     Names for everything, from operations, fields, arguments, types, etc.

     https://facebook.github.io/graphql/June2018/#sec-Names **)
  Variable Name : ordType.

  
  (**
     Same as names, except that it can't be true, false or null. 
     Right now it is just the same as Name.

     https://facebook.github.io/graphql/June2018/#EnumValue **)
  Definition EnumValue := Name.


  
  Section Types.

    (** 
        Basically the same as a name.    
    
        https://facebook.github.io/graphql/June2018/#NamedType **)
    Definition NamedType := Name.

    
    (** Types of data expected by query variables.

        NonNull types are omitted in this current version.

        https://facebook.github.io/graphql/June2018/#sec-Type-References **)
    Inductive type : Type :=
    | NT : NamedType -> type
    | ListType : type -> type.



  
    (** Get a type's wrapped name.
        Corresponds to a named type's actual name or the name used in a list type

        https://facebook.github.io/graphql/June2018/#sec-Type-References
        https://facebook.github.io/graphql/June2018/#sec-Wrapping-Types **)
    Fixpoint tname (ty : type) : NamedType :=
      match ty with
      | NT name => name
      | ListType ty' => tname ty'
      end.

    Coercion tname : type >-> Ord.sort.

    (** Packing and unpacking of a type, needed for canonical instances **)
    Fixpoint tree_of_type (ty : type) : GenTree.tree Name :=
      match ty with
      | NT n => GenTree.Node 0 [:: GenTree.Leaf n]
      | ListType ty' => GenTree.Node 1 [:: tree_of_type ty']
      end.
      
    Fixpoint type_of_tree (t : GenTree.tree Name) : option type :=
      match t with
      | GenTree.Node 0 [:: GenTree.Leaf n] => Some (NT n)
      | GenTree.Node 1 [:: t'] => if (type_of_tree t') is Some ty then
                                   Some (ListType ty)
                                 else
                                   None
      | _ => None
      end.


    (** Cancelation lemma for types **)
    Lemma pcan_tree_of_type : pcancel tree_of_type type_of_tree.
    Proof. by elim=> [| t /= ->]. Qed.
    
    Canonical type_eqType := EqType type (PcanEqMixin pcan_tree_of_type).
    Canonical type_choiceType := ChoiceType type (PcanChoiceMixin pcan_tree_of_type).
    Canonical type_ordType := OrdType type (PcanOrdMixin pcan_tree_of_type).
    
  End Types.



  Section TypeSystem.

    
    (** Argument for a field.

        In the specification it is named "InputValue" (InputValueDefinition) but 
        it is not very descriptive of what it is. Besides, it is constantly refered 
        as "argument", therefore it is here named as FieldArgument (only fields can have
        arguments so it may sound redundant to name it like this but I feel like it is
        more descriptive and reinforces this notion). 

        https://facebook.github.io/graphql/June2018/#sec-Field-Arguments **)
    Inductive FieldArgumentDefinition := FieldArgument (argname : Name) (argtype : type).

     

    (** Packing and unpacking of a field argument, needed for canonical instances **)
    Definition prod_of_arg (arg : FieldArgumentDefinition) := let: FieldArgument n t := arg in (n, t).
    Definition arg_of_prod (p : prod Name type) := let: (n, t) := p in FieldArgument n t.

    (** Cancelation lemma for field arguments **)
    Lemma prod_of_argK : cancel prod_of_arg arg_of_prod.  Proof. by case. Qed.
  
    Canonical arg_eqType := EqType FieldArgumentDefinition (CanEqMixin prod_of_argK).
    Canonical arg_choiceType := ChoiceType FieldArgumentDefinition (CanChoiceMixin prod_of_argK).
    Canonical arg_ordType := OrdType FieldArgumentDefinition (CanOrdMixin prod_of_argK).


    
    (** Field of an object or interface in the schema. 
        Represents a leaf or an edge between nodes of the underlying tree structure.

        https://facebook.github.io/graphql/June2018/#FieldDefinition **)
    Inductive FieldDefinition := Field (field_name : Name)
                                      (args : {fset FieldArgumentDefinition})
                                      (return_type : type).

   
    (** Packing and unpacking of a field, needed for canonical instances **)
    Definition prod_of_field (f : FieldDefinition) := let: Field n args t := f in (n, args, t).
    Definition field_of_prod (p : Name * {fset FieldArgumentDefinition} * type)  := let: (n, args, t) := p in Field n args t.

    (** Cancelation lemma for a field **)
    Lemma prod_of_fieldK : cancel prod_of_field field_of_prod. Proof. by case. Qed.

    
    Canonical field_eqType := EqType FieldDefinition (CanEqMixin prod_of_fieldK).
    Canonical field_choiceType := ChoiceType FieldDefinition (CanChoiceMixin prod_of_fieldK).
    Canonical field_ordType := OrdType FieldDefinition (CanOrdMixin prod_of_fieldK).


    
  
    (** Possible type definitions one can make in a GraphQL service. Some observations:

        1. Objects' interfaces: Objects *may* declare one or more implemented interfaces. This is 
        is implemented as a list of <type>, which can be empty or not. As it is, an
        object may declare an interface as a list type (eg. "type A implements [B]"), therefore
        in the wf property there is a check that restricts this declaration to a 
        named type.

        2. Fields: Objects and interfaces must declare at least one field but the current
        definition allows an empty list of fields. In the wf property it is checked that
        this list is not empty.

        3. InputObjects: Currently not included to simplify the formalization.


        https://facebook.github.io/graphql/June2018/#TypeDefinition
     **)

    Inductive TypeDefinition : Type :=
    | ScalarTypeDefinition : Name -> TypeDefinition
    | ObjectTypeDefinition : Name -> {fset NamedType} -> seq FieldDefinition -> TypeDefinition
    | InterfaceTypeDefinition : Name -> seq FieldDefinition -> TypeDefinition
    | UnionTypeDefinition : Name -> {fset NamedType} -> TypeDefinition
    | EnumTypeDefinition : Name -> {fset EnumValue} -> TypeDefinition.
    

  


    
    (** Packing and unpacking of a type definition, needed for canonical instances **)
    Notation tdefRep := (Name + (Name * {fset NamedType} * seq FieldDefinition) + (Name * seq FieldDefinition) +
                        (Name * {fset NamedType}) + (Name * {fset EnumValue}))%type.

    
    Definition tdef_rep tdef : tdefRep :=
      match tdef with 
      | ScalarTypeDefinition name => inl (inl (inl (inl name)))
      | ObjectTypeDefinition name intfs flds => inl (inl (inl (inr (name, intfs, flds))))
      | InterfaceTypeDefinition name flds => inl (inl (inr (name, flds)))
      | UnionTypeDefinition name mbs => inl (inr (name, mbs))
      | EnumTypeDefinition name enums => inr (name, enums)
      end.

    Definition tdef_con (trep : tdefRep) : TypeDefinition :=
      match trep with
      | inl (inl (inl (inl name))) => ScalarTypeDefinition name
      | inl (inl (inl (inr (name, intfs, flds)))) => ObjectTypeDefinition name intfs flds
      | inl (inl (inr (name, flds))) => InterfaceTypeDefinition name flds
      | inl (inr (name, mbs)) => UnionTypeDefinition name mbs
      | inr (name, enums) => EnumTypeDefinition name enums
      end.

    (** Cancelation lemma for a type definition **)
    Lemma tdef_repK : cancel tdef_rep tdef_con.
    Proof. by case. Qed.

    
    Canonical tdef_eqType := EqType TypeDefinition (CanEqMixin tdef_repK).
    Canonical tdef_choiceType := ChoiceType TypeDefinition (CanChoiceMixin tdef_repK).
    Canonical tdef_ordType := OrdType TypeDefinition (CanOrdMixin tdef_repK).
    
    
      
    (** 
        The Schema corresponds to the type system - the collective types defined and a
        reference to the Query type (the entry point for queries).

        This differs from the Schema mentioned in the specification. I believe there is
        some naming clashes when they refer to a Schema:
 
        A GraphQL service’s collective type system capabilities are referred to as
        that service’s “schema”. A schema is defined in terms of the types and 
        directives it supports as well as the root operation types for each kind of
        operation: query, mutation, and subscription [...]

        This description matches the definition given in this file, but one can also define 
        a "schema", which only describes the types for the operations: query, mutation and suscription.
   **)
    Inductive schema := Schema (query_type : NamedType)
                              (type_definitions : {fmap Name -> TypeDefinition}).

    (** Extractors for a schema **)
    Definition query_type sch := let: Schema q _ := sch in q.
    Definition type_definitions sch := let: Schema _ tdefs := sch in tdefs.

    Definition fun_of_schema sch := fun p => p \in sch.(type_definitions).

    Coercion fun_of_schema : schema >-> Funclass.

    (** Packing and unpacking of a schema **)
    Definition prod_of_schema (s : schema) := let: Schema q tdefs := s in (q, tdefs).
    Definition schema_of_prod p := let: (q, tdefs) := p in Schema q tdefs.

    (** Cancelation lemma for a schema **)
    Lemma prod_of_schemaK : cancel prod_of_schema schema_of_prod.  Proof. by case. Qed.
 
    Canonical schema_eqType := EqType schema (CanEqMixin prod_of_schemaK).
    Canonical schema_choiceType := ChoiceType schema (CanChoiceMixin prod_of_schemaK).
    Canonical schema_ordType := OrdType schema (CanOrdMixin prod_of_schemaK).

    
  End TypeSystem.
    
    
End Schema.

(*

Notation "[ name ]" := (ListType name).
Notation "argname : ty" := (FieldArgument argname ty) : schema_scope.
Notation "fname '(' args ')' ':' ty" := (Field fname args ty) (at level 50) : schema_scope.
Notation "'scalar' S" := (ScalarTypeDefinition S) (at level 0) : schema_scope.
Notation "'object' O '{' flds '}'" := (ObjectTypeDefinition O [::] flds) : schema_scope.
Notation "'object' O 'implements' I '{' flds '}'" := (ObjectTypeDefinition O I flds) : schema_scope.
Notation "'interface' I '{' flds '}'" := (InterfaceTypeDefinition I flds) : schema_scope.
Notation "'union' U '{' mbs '}'" := (UnionTypeDefinition U mbs) : schema_scope.
Notation "'enum' E '{' evs '}'" := (EnumTypeDefinition E evs) : schema_scope.

 *)
Arguments NamedType [Name].
Arguments type [Name].
Arguments FieldArgumentDefinition [Name].
Arguments FieldDefinition [Name].
Arguments TypeDefinition [Name].
Arguments Schema [Name].

Arguments tname [Name].

