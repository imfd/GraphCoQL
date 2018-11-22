From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord.



Section Schema.

  (** Names for everything, from operations, fields, arguments, types, etc.

      https://facebook.github.io/graphql/June2018/#sec-Names **)
  Variable Name : ordType.


  (** Same as names, except that it can't be true, false or null. 
      Right now it is just the same as Name.

      https://facebook.github.io/graphql/June2018/#EnumValue **)
  Definition EnumValue := Name.


  (** Types of data expected by query variables.

      https://facebook.github.io/graphql/June2018/#sec-Type-References **)
  Inductive type : Type :=
  | NamedType : Name -> type
  | ListType : type -> type.


  
  (** Get a type's wrapped name.
      Corresponds to a named type's actual name or the name used in a list type

      https://facebook.github.io/graphql/June2018/#sec-Type-References
      https://facebook.github.io/graphql/June2018/#sec-Wrapping-Types
   **)
  Fixpoint name_of_type (ty : type) : Name :=
    match ty with
    | NamedType name => name
    | ListType ty' => name_of_type ty'
    end.

  Coercion name_of_type : type >-> Ord.sort.
  
  (** Argument for a field.

      In the specification it is named "InputValue" (InputValueDefinition) but 
      it is not very descriptive of what it is. Besides, it is constantly refered 
      as "argument", therefore it is named as FieldArgument (only fields can have
      arguments so it may sound redundant to name it like this but I feel it is
      more descriptive and reinforces this notion). 

      https://facebook.github.io/graphql/June2018/#sec-Field-Arguments **)
  Inductive FieldArgumentDefinition : Type :=
  | FieldArgument : Name -> type -> FieldArgumentDefinition.


  Definition name_of_argument (arg : FieldArgumentDefinition) := let: FieldArgument n _ := arg in n.
  Definition type_of_argument (arg : FieldArgumentDefinition) := let: FieldArgument _ ty := arg in ty.
 
  
  (** https://facebook.github.io/graphql/June2018/#FieldDefinition **)
  Inductive FieldDefinition : Type :=
  | Field : Name -> seq FieldArgumentDefinition -> type -> FieldDefinition.


  Definition name_of_field (fld : FieldDefinition) : Name :=
    let: Field n _ _ := fld in n.
  Definition type_of_field (fld : FieldDefinition) : type :=
    let: Field _ _ ty := fld in ty.

  Coercion type_of_field : FieldDefinition >-> type.

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
  | ObjectTypeDefinition : Name -> seq type -> list FieldDefinition -> TypeDefinition
  | InterfaceTypeDefinition : Name -> seq FieldDefinition -> TypeDefinition
  | UnionTypeDefinition : Name -> seq type -> TypeDefinition
  | EnumTypeDefinition : Name -> seq EnumValue -> TypeDefinition.
  

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
  Structure schema := Schema {
                      query_type : type;
                      typeDefinitions : seq TypeDefinition
                    }.


  
 
    (** Establishing eqType for different structures: type, arguments, fields **)

    
    (** Get a tree out of a type **)
    Fixpoint tree_of_type (ty : type) : GenTree.tree Name :=
      match ty with
      | NamedType n => GenTree.Leaf n
      | ListType ty' => GenTree.Node 0 [:: tree_of_type ty']
      end.

    (** Get a type out of a tree or none **)
    Fixpoint type_of_tree (t : GenTree.tree Name) : option type :=
      match t with
      | GenTree.Leaf n => Some (NamedType n)
      | GenTree.Node 0 [:: t'] => if (type_of_tree t') is Some ty then
                                   Some (ListType ty)
                                 else
                                   None
      | _ => None
      end.

    Lemma pcan_tree_of_type : pcancel tree_of_type type_of_tree.
    Proof.
        by elim=> [| t /= ->].
    Qed.

    Definition type_eqMixin := PcanEqMixin pcan_tree_of_type.
    Canonical type_eqType := EqType type type_eqMixin.
    Definition type_choiceMixin := PcanChoiceMixin pcan_tree_of_type.
    Canonical type_choiceType := ChoiceType type type_choiceMixin.

    (*Definition type_ordMixin := PcanOrdMixin pcan_tree_of_type.
    Canonical type_ordType := OrdType type type_ordMixin.*)
    


    Definition prod_of_arg (arg : FieldArgumentDefinition) := let: FieldArgument n t := arg in (n, t).
    Definition arg_of_prod (p : prod Name type) := let: (n, t) := p in FieldArgument n t.

    Lemma prod_of_argK : cancel prod_of_arg arg_of_prod.
    Proof. by case. Qed.

    Definition arg_eqMixin := CanEqMixin prod_of_argK.
    Canonical arg_eqType := EqType FieldArgumentDefinition arg_eqMixin.



    Definition prod_of_field (f : FieldDefinition) := let: Field n args t := f in (n, args, t).
    Definition field_of_prod (p : Name * (seq.seq FieldArgumentDefinition) * type)  := let: (n, args, t) := p in Field n args t.

    Lemma prod_of_fieldK : cancel prod_of_field field_of_prod.
    Proof. by case. Qed.

    Definition field_eqMixin := CanEqMixin prod_of_fieldK.
    Canonical field_eqType := EqType FieldDefinition field_eqMixin.


End Schema.

Arguments type [Name].
Arguments FieldArgumentDefinition [Name].
Arguments FieldDefinition [Name].
Arguments TypeDefinition [Name].
Arguments Schema [Name].

Arguments name_of_type [Name].

Arguments name_of_argument [Name].
Arguments type_of_argument [Name].

Arguments name_of_field [Name].
Arguments type_of_field [Name].