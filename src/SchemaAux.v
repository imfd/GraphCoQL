Require Import List.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fset.


Require Import Schema.
Require Import treeordtype.

Set Implicit Arguments.

Section SchemaAux.


  Variable Name : ordType.

  
  (* Schema used as parameter in later functions *) 
  Variable schema : @schema Name.

  Notation type := (@type Name).

  Fixpoint get_first {A} p (lst : seq A) :=
    if lst is hd :: tl then
      if p hd then
        Some hd
      else
        get_first p tl
    else
      None.

  
  (**
   Looks up a name in the given document, returning the type definition if it
   was declared in the document.
   **)
  Definition lookup_type (ty : NamedType)  : option TypeDefinition :=
    let n_eq nt tdef := match tdef with
                       | ScalarTypeDefinition name =>  nt == name 
                       | ObjectTypeDefinition name _  _ =>  nt == name
                       | InterfaceTypeDefinition name _ => nt == name
                       | UnionTypeDefinition name _ => nt == name
                       | EnumTypeDefinition name _ =>  nt == name
                       end
    in
    get_first (n_eq ty) schema.
    


  (** Checks whether the given type is defined as a Scalar in the Schema **)
  Definition is_scalar_type (ty : NamedType) : bool :=
    match (lookup_type ty) with
    | Some (ScalarTypeDefinition _) => true
    | _ => false
    end.

  (** Checks whether the given type is defined as an Object in the Schema **)
  Equations is_object_type (ty : @NamedType Name) : bool :=
    is_object_type ty with (lookup_type ty) =>
    {
      | Some (ObjectTypeDefinition _ _ _) := true;
      | _ => false
    }.

  Lemma is_object_type_E ty :
    is_object_type ty ->
    exists (t : @NamedType Name) intfs flds, lookup_type ty = Some (ObjectTypeDefinition t intfs flds).
  Proof.
    funelim (is_object_type ty) => // _.
      by exists s0, f, l.
  Qed.

  (** Checks whether the given type is defined as an Interface in the Schema **)
  Equations is_interface_type (ty : @NamedType Name) : bool :=
    is_interface_type ty with (lookup_type ty) =>
    {
      | Some (InterfaceTypeDefinition _ _) := true;
      | _ => false
    }.

  Lemma is_interface_type_E ty :
    is_interface_type ty <->
    exists i flds, lookup_type ty = Some (InterfaceTypeDefinition i flds).
  Proof.
    split.
    funelim (is_interface_type ty) => // _.
      by exists s1, l0.
    case=> i; case=> flds Hlook.
      by rewrite is_interface_type_equation_1 Hlook.
  Qed.
  
  (** Checks whether the given type is defined as a Union in the Schema **)
  Equations is_union_type (ty : @NamedType Name) : bool :=
    is_union_type ty with (lookup_type ty) =>
    {
      | Some (UnionTypeDefinition _ _) := true;
      | _ => false
    }.

    Lemma is_union_type_E ty:
      is_union_type ty <->
      exists u mbs, lookup_type ty = Some (UnionTypeDefinition u mbs).
    Proof.
      split.
      funelim (is_union_type ty) => // _.
        by exists s2, f0.
      case=> u; case=> mbs Hlook.
      by rewrite is_union_type_equation_1 Hlook.  
  Qed.
  
  (** Checks whether the given type is defined as an Enum in the Schema **)
  Definition is_enum_type (ty : NamedType) : bool :=
    match (lookup_type ty) with
    | Some (EnumTypeDefinition _ _) => true
    | _ => false
    end.

  (** Checks whether the given type is a list type (does not care for the wrapped type) **)
  Definition is_list_type (ty : type) : bool :=
    match ty with
    | (ListType ty') => true
    | _ => false
    end.


  
  (** Get all unduplicated argument names from a field **)
  Definition field_arg_names (fld : FieldDefinition) : {fset Name} := fset [seq arg.(argname) | arg <- fld.(field_args)].


  (** Get all field names from a type definition **)
  Definition tdef_field_names (tdef : @TypeDefinition Name) : {fset Name} := fset [seq fld.(field_name) | fld <- tdef.(tdef_fields)].

  
  (** Get list of fields declared in an Object or Interface type definition **)
  Definition fields (ty : NamedType) : seq FieldDefinition :=
    match lookup_type ty with
    | Some (ObjectTypeDefinition _ _ flds) => flds
    | Some (InterfaceTypeDefinition _ flds) => flds
    | _ => [::]
    end.


  (** Get all type definitions' names from a schema **)
  Definition schema_names : {fset Name} := fset [seq tdef.(tdef_name) | tdef <- schema]. 


  (** Check whether a given name is declared in the schema, as a type definition **)
  Definition is_declared (name : Name) : bool := name \in schema_names.
  
  (**
     Gets the first field definition from a given type that matches the given field name. 
     If the type is not declared in the Schema or the field does not belong to the type, then it returns None.
   **)
  Definition lookup_field_in_type (ty : NamedType) (fname : Name) : option FieldDefinition :=
    if lookup_type ty is Some tdef then
      get_first (fun fld => fld.(field_name) == fname) tdef.(tdef_fields)
    else
      None.

  (** 
      Gets the type of the first field definition from a given type that matches the given field name. 
      If the type is not declared in the Schema or the field does not belong to the type, then it returns None.

   **)
  Definition lookup_field_type (ty : NamedType) (fname : Name)  : option type :=
    match lookup_field_in_type ty fname with
    | Some fieldDef => Some (return_type fieldDef) 
    | None => None
    end.


    (**
     Get the union's types' names.
     If the type is not declared as Union in the Schema, then returns None.
   **)
  Definition union_members (ty : NamedType) : {fset NamedType} :=
    match lookup_type ty with
    | Some (UnionTypeDefinition name mbs) => mbs
    | _ => fset0
    end.


  (**
     Checks whether the given type declares implementation of another type.
   **)
  Definition declares_implementation (ty ty' : NamedType) : bool :=
    match lookup_type ty with
    | Some (ObjectTypeDefinition _ intfs _) => ty' \in intfs
    | _ => false
    end.


  Definition implements_interface (iname : NamedType) (tdef : @TypeDefinition Name) : bool :=
    iname \in tdef.(tdef_intfs).
  
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

  (**
     Gets "possible" types from a given type, as defined in the GraphQL Spec
     (https://facebook.github.io/graphql/June2018/#GetPossibleTypes())

     If the type is:
     1. Object : Possible types are only the type itself.
     2. Interface : Possible types are all types that declare implementation of this interface.
     3. Union : Possible types are all members of the union.

   **)
  Definition get_possible_types (ty : NamedType) : {fset NamedType} :=
    match lookup_type ty with
    | Some (ObjectTypeDefinition _ _ _) => fset1 ty
    | Some (InterfaceTypeDefinition iname _) =>
      let filtered := [seq tdef <- schema | implements_interface iname tdef]
      in
      fset [seq tdef.(tdef_name) | tdef <- filtered]
    | Some (UnionTypeDefinition _ mbs) => fset mbs
    | _ => fset0
    end.
  
  Definition implementation (ty : NamedType) : seq NamedType :=
    match lookup_type ty with
    | Some (InterfaceTypeDefinition iname _) =>
      let filtered := [seq tdef <- schema | implements_interface iname tdef]
      in
      fset [seq tdef.(tdef_name) | tdef <- filtered]
    | _ => [::]
    end.

  Lemma declares_in_implementation t ty :
    (declares_implementation t ty) <-> (t \in implementation ty).
  Proof.
  Admitted.
  
  (*
  Lemma in_possible_types_E schema t ty :
    reflect
      ([\/ t = ty,
        t \in implementation schema ty |
        t \in union_members schema ty])
      (t \in get_possible_types schema ty).
  Proof.
    apply: (iffP idP).
    * rewrite /get_possible_types.
      case Hlook : lookup_type => [tdef|] //.
      case: tdef Hlook => //.
      - move=> obj intfs flds Hlook.
          by rewrite in_fset1; move/eqP; constructor 1.
      - move=> intf flds Hlook.
          by rewrite in_fset /implementation Hlook; constructor 2.
      - move=> un mbs Hlook.
          by rewrite in_fset /union_members Hlook; constructor 3.
    * move=> [Heq | Hintfs | Hunion].
      rewrite /get_possible_types.
  Qed. *)

  Lemma in_possible_types_E t ty :
    t \in get_possible_types ty ->
          [\/ t = ty,
           t \in implementation ty |
           t \in union_members ty].
  Proof.
    rewrite /get_possible_types.
    case Hlook : lookup_type => [tdef|] //.
    case: tdef Hlook => //.
    - move=> obj intfs flds Hlook.
        by rewrite in_fset1; move/eqP; constructor 1.
    - move=> intf flds Hlook.
        by rewrite in_fset /implementation Hlook; constructor 2; rewrite in_fset.
    - move=> un mbs Hlook.
        by rewrite in_fset /union_members Hlook; constructor 3.
  Qed.


 
  
End SchemaAux.


Arguments lookup_type [Name].
Arguments is_enum_type [Name].

Arguments lookup_field_in_type [Name].
Arguments lookup_field_type [Name].
Arguments union_members [Name].
