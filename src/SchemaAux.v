From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fset fmap.


Require Import Schema.
Require Import SeqExtra.


Section SchemaAux.


  Variable Name : ordType.

  Section ArgDefExtractors.

    Implicit Type (arg : @FieldArgumentDefinition Name).
    
    (** Extractors for a FieldArgument **)
    Definition argname arg := let: FieldArgument n _ := arg in n.
    Definition argtype arg := let: FieldArgument _ t := arg in t.

  End ArgDefExtractors.

  Section FieldDefExtractors.

    Implicit Type fld : @FieldDefinition Name.
    
    (** Extractors for a Field **)
    Definition fname fld := let: Field f _ _ := fld in f.
    Definition fargs fld := let: Field _ args _ := fld in args.
    Definition return_type fld := let: Field _ _ ty := fld in ty.


    (** Get all unduplicated argument names from a field **)
    Definition field_arg_names (fld : FieldDefinition) : {fset Name} := fset [seq arg.(argname) | arg <- fld.(fargs)].
    

  End FieldDefExtractors.

  Section TypeDefExtractors.

    Implicit Type tdef : @TypeDefinition Name.
    
    (** Extractors for a type definition **)
    Definition tdname tdef : Name :=
      match tdef with
      | Scalar name
      | Object name implements _ {{ _ }}
      | Interface name {{ _ }}
      | Union name {{ _ }}
      | Enum name {{ _ }} => name
      end.


    Definition tfields tdef : seq FieldDefinition :=
      match tdef with 
      | Object _ implements _ {{ flds }}
      | Interface _ {{ flds }} => flds
      | _ => [::]
      end.

    Definition tintfs tdef : {fset NamedType} :=
      match tdef with
      | Object _ implements intfs {{ _ }} => intfs
      | _ => fset0
      end.

    Definition tmbs tdef : {fset NamedType} :=
      match tdef with
      | Union _ {{ mbs }}=> mbs
      | _ => fset0
      end.

    Definition tenums tdef : {fset (@EnumValue Name)} :=
      match tdef with
      | Enum _ {{ enums }} => enums
      | _ => fset0
      end.

    
    (** Get all field names from a type definition **)
    Definition tdef_field_names (tdef : @TypeDefinition Name) : {fset Name} := fset [seq fld.(fname) | fld <- tdef.(tfields)].


  End TypeDefExtractors.
  

  Variable schema : @schema Name.



  (** Checks whether the given type definition has the given name **)
  Definition has_name (name : @NamedType Name) (tdef : TypeDefinition) : bool :=
    name == tdef.(tdname).
  

  
  Definition lookup_type (ty : Name) := schema.(type_definitions) ty.

  
  
  Section TypePredicates.
    
    (** Checks whether the given type is defined as a Scalar in the Schema **)
    Definition is_scalar_type (ty : NamedType) : bool :=
      match (lookup_type ty) with
      | Some (Scalar _) => true
      | _ => false
      end.


    
    (** Checks whether the given type is defined as an Object in the Schema **)
    Equations is_object_type (ty : @NamedType Name) : bool :=
      is_object_type ty with lookup_type ty :=
        {
        | Some (Object _ implements _ {{ _ }}) := true;
        | _ := false
        }.



    (** Checks whether the given type is defined as an Interface in the Schema **)
    Equations is_interface_type (ty : @NamedType Name) : bool :=
      is_interface_type ty with lookup_type ty :=
        {
        | Some (Interface _ {{ _ }}) := true;
        | _ := false
        }.

    
    
    (** Checks whether the given type is defined as a Union in the Schema **)
    Equations is_union_type (ty : @NamedType Name) : bool :=
      is_union_type ty with lookup_type ty :=
        {
        | Some (Union _ {{ _ }}) := true;
        | _ := false
        }.

    
    (** Checks whether the given type is defined as an Enum in the Schema **)
    Definition is_enum_type (ty : NamedType) : bool :=
      match (lookup_type ty) with
      | Some (Enum _ {{ _ }}) => true
      | _ => false
      end.

    (** Checks whether the given type is a list type (does not care for the wrapped type) **)
    Definition is_list_type (ty : @type Name) : bool :=
      match ty with
      | [ ty' ] => true
      | _ => false
      end.

    Definition is_abstract_type (ty : NamedType) : bool :=
      is_interface_type ty ||  is_union_type ty.

    Definition is_composite_type (ty : NamedType) : bool :=
      [|| is_object_type ty, is_interface_type ty | is_union_type ty].

    Definition is_leaf_type (ty : NamedType) : bool :=
      is_scalar_type ty || is_enum_type ty.
    
  End TypePredicates.
  

  

  (** Get all type definitions' names from a schema **)
  Definition schema_names : {fset Name} := fset [seq tdef.(tdname) | tdef <- codomm (schema.(type_definitions))]. 


  (** Check whether a given name is declared in the schema, as a type definition **)
  Definition is_declared (name : Name) : bool := name \in schema_names.


  (** Checks whether the field has the given name **)
  Definition has_field_name (name : Name) (fld : FieldDefinition) :=
    name == fld.(fname).



  Section Lookup.
    
    (**
     Gets the first field definition from a given type that matches the given field name. 
     If the type is not declared in the Schema or the field does not belong to the type, then it returns None.
     **)
    Definition lookup_field_in_type (ty : NamedType) (fname : Name) : option FieldDefinition :=
      if lookup_type ty is Some tdef then
        get_first (has_field_name fname) tdef.(tfields)
      else
        None.


    
    (** 
      Gets the type of the first field definition from a given type that matches the given field name. 
      If the type is not declared in the Schema or the field does not belong to the type, then it returns None.

     **)
    Definition lookup_field_type (ty : NamedType) (fname : Name)  : option type :=
      match lookup_field_in_type ty fname with
      | Some fld => Some fld.(return_type)
      | None => None
      end.

    (**
     Gets the first argument definition that matches the given argument name, from the
     given type and field. If the argument is not defined then it returns None.
     If the field is not declared in that type, then it returns None.
     **)
    Definition lookup_argument_in_type_and_field (ty : NamedType) (fname aname : Name) : option FieldArgumentDefinition :=
      match lookup_field_in_type ty fname with
      | Some (Field fname args _) => get_first (fun arg => arg.(argname) == aname) args
      | _ => None
      end.

    (** Get list of fields declared in an Object or Interface type definition **)
    Definition fields (ty : NamedType) : seq FieldDefinition :=
      match lookup_type ty with
      | Some (Object _ implements _ {{ flds }})
      | Some (Interface _ {{ flds }}) => flds
      | _ => [::]
      end.
    
  End Lookup.


  Section Subtypes.
    
    (**
     Get the union's types' names.
     If the type is not declared as Union in the Schema, then returns None.
     **)
    Definition union_members (ty : NamedType) : {fset NamedType} :=
      match lookup_type ty with
      | Some (Union _ {{ mbs }}) => mbs
      | _ => fset0
      end.

    
    (**
     Checks whether the given type declares implementation of another type.
     **)
    Definition declares_implementation (ty ty' : NamedType) : bool :=
      match lookup_type ty with
      | Some (Object _ implements intfs {{ _ }}) => ty' \in intfs
      | _ => false
      end.


    
    Definition implements_interface (iname : NamedType) (tdef : @TypeDefinition Name) : bool :=
      iname \in tdef.(tintfs).



    
    

    Definition implementation (ty : NamedType) : seq NamedType :=
      undup [seq tdef.(tdname) | tdef <- codomm schema.(type_definitions) & implements_interface ty tdef].

    
    (**
     Gets "possible" types from a given type, as defined in the GraphQL Spec
     (https://facebook.github.io/graphql/June2018/#GetPossibleTypes())

     If the type is:
     1. Object : Possible types are only the type itself.
     2. Interface : Possible types are all types that declare implementation of this interface.
     3. Union : Possible types are all members of the union.

     **)
    Equations get_possible_types (ty : @NamedType Name) : seq (@NamedType Name) :=
      {
        get_possible_types ty with lookup_type ty :=
          {
          | Some (Object _ implements _ {{ _ }}) => [:: ty];
          | Some (Interface iname {{ _ }}) => implementation iname;
          | Some (Union _ {{ mbs }}) => mbs;
          | _ => [::]
          }
      }.


  End Subtypes.
  

  
  
  
End SchemaAux.


Arguments lookup_type [Name].
Arguments is_enum_type [Name].


Arguments lookup_field_in_type [Name].
Arguments lookup_field_type [Name].
Arguments union_members [Name].
