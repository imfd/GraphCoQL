From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord.

Require Import List.
Import ListNotations.

Require Import Schema.

Set Implicit Arguments.

Section SchemaAux.


  Variable Name : ordType.

  
  Fixpoint typeEq (ty ty' : @type Name) : bool :=
    match ty, ty' with
    | NamedType n, NamedType n' => n == n'
    | ListType ty, ListType ty' => typeEq ty ty'
    | _, _ => false
    end.

  
  
  Lemma typeEqP : Equality.axiom typeEq.
  Proof.
    rewrite /Equality.axiom.
    move => ty ty'; apply: (iffP idP).
    elim:  ty ty' => [n | t IHt] [n' | t' IHt'] //=.
      by move/eqP => ->.
      simpl in IHt'.
      move : (IHt _ IHt').
        by move => H ; rewrite H.
        move => H ; rewrite H.
          elim ty' => [//=|//=].
  Qed.

  Definition type_eqMixin := Equality.Mixin typeEqP.
  Canonical type_eqType := EqType type type_eqMixin.
        


  Definition prod_of_arg (arg : @FieldArgumentDefinition Name) := let: FieldArgument n t := arg in (n, t).
  Definition arg_of_prod (p : prod Name type) := let: (n, t) := p in FieldArgument n t.

  Lemma prod_of_argK : cancel prod_of_arg arg_of_prod.
  Proof. by case. Qed.

   Definition arg_eqMixin := CanEqMixin prod_of_argK.
   Canonical arg_eqType := EqType FieldArgumentDefinition arg_eqMixin.



   Definition prod_of_field (f : @FieldDefinition Name) := let: Field n args t := f in (n, args, t).
   Definition field_of_prod (p : Name * (seq.seq FieldArgumentDefinition) * type)  := let: (n, args, t) := p in Field n args t.

   Lemma prod_of_fieldK : cancel prod_of_field field_of_prod.
   Proof. by case. Qed.

   Definition field_eqMixin := CanEqMixin prod_of_fieldK.
   Canonical field_eqType := EqType FieldDefinition field_eqMixin.

   
  Implicit Type schema : @schema Name.
  
  Definition root schema : type := query schema.
  
  (**
   Looks up a name in the given document, returning the type definition if it
   was declared in the document.
   **)
  Definition lookupName schema (name : Name)  : option TypeDefinition :=
    match schema with
    | (Schema _ tdefs) =>
      let n_eq nt tdef := match tdef with
                         | ScalarTypeDefinition name =>  nt == name
                         | ObjectTypeDefinition name _  _ =>  nt == name
                         | InterfaceTypeDefinition name _ => nt == name
                         | UnionTypeDefinition name _ => nt == name
                         | EnumTypeDefinition name _ =>  nt == name
                         end
      in
      find (n_eq name) tdefs
    end.


  Definition isScalarType schema (ty : type) : bool :=
    match ty with
    | (NamedType name) =>
      match (lookupName schema name) with
      | Some (ScalarTypeDefinition name) => true
      | _ => false
      end
    | _ => false
    end.

  Definition isObjectType schema (ty : type) : bool :=
    match ty with
    | (NamedType name) =>
      match (lookupName schema name) with
      | Some (ObjectTypeDefinition name _ _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition isInterfaceType schema (ty : type) : bool :=
    match ty with
    | (NamedType name) =>
      match (lookupName schema name) with
      | Some (InterfaceTypeDefinition name _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition isUnionType schema (ty : type) : bool :=
    match ty with
    | (NamedType name) =>
      match (lookupName schema name) with
      | Some (UnionTypeDefinition name _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition isEnumType schema (ty : type) : bool :=
    match ty with
    | (NamedType name) =>
      match (lookupName schema name) with
      | Some (EnumTypeDefinition name _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition isListType (ty : @type Name) : bool :=
    match ty with
    | (ListType ty') => true
    | _ => false
    end.



  (** Get a type definition's name.
 Corresponds to the name one gives to an object, interface, etc. **)
  Definition typeDefName (tdef : TypeDefinition) : Name :=
    match tdef with 
    | ScalarTypeDefinition name => name
    | ObjectTypeDefinition name _ _ => name
    | InterfaceTypeDefinition name _ => name
    | UnionTypeDefinition name _ => name
    | EnumTypeDefinition name _ => name
    end.

  (** Get type definitions' names *)
  Definition typeDefsNames (tdefs : list TypeDefinition) := map typeDefName tdefs.


  (** Get a type's name.
    Corresponds to named type actual name or the name used in a list type **)
  Fixpoint unwrapTypeName (ty : type) : Name :=
    match ty with
    | NamedType name => name
    | ListType ty' => unwrapTypeName ty'
    end.

  Coercion unwrapTypeName : type >-> Ord.sort.

  (** Get types' names **)
  Definition typesNames (tys : list type) : list Name := map unwrapTypeName tys.

  (** Get arguments' names **)
  Definition argNames (args : list FieldArgumentDefinition) : list Name :=
    let extract arg := match arg with
                      | FieldArgument name _ => name
                      end
    in
    map extract args.

  (** Get a field's name **)
  Definition fieldName (fld : FieldDefinition) : Name :=
    let: Field name _ _ := fld in name.

  (** Get fields' names **)
  Definition fieldNames (flds : list FieldDefinition) : list Name := map fieldName flds.


  (** Get list of fields declared in an Object or Interface type definition **)
  Definition fieldDefinitions schema (name : Name) : list FieldDefinition :=
    match lookupName schema name with
    | Some (ObjectTypeDefinition _ _ flds) => flds
    | Some (InterfaceTypeDefinition _ flds) => flds
    | _ => []
    end.


  Definition fields schema (name : Name) : list Name :=
    match lookupName schema name with
    | Some (ObjectTypeDefinition _ _ flds) => fieldNames flds
    | Some (InterfaceTypeDefinition _ flds) => fieldNames flds
    | _ => []
    end.

  Definition fieldType (fld : FieldDefinition) : @type Name :=
    let: Field _ _ ty := fld in ty.

  Definition lookupField schema (tname fname : Name) : option FieldDefinition :=
    let n_eq nt fld := let: Field name _ _ := fld in nt == name
    in
    find (n_eq fname) (fieldDefinitions schema tname).

  Definition lookupFieldType schema (tname fname : Name)  : option type :=
    match lookupField schema fname tname with
    | Some fieldDef => Some (fieldType fieldDef)
    | None => None
    end.


  Definition union schema (tname : Name) :=
    match lookupName schema tname with
    | Some (EnumTypeDefinition name mbs) => mbs
    | _ => []
    end.


  
  Definition declaresImplementation schema (name iname : Name) : bool :=
    match lookupName schema name with
    | Some (ObjectTypeDefinition _ intfs _) => existsb (fun el => ((unwrapTypeName el) == iname) && isInterfaceType schema el) intfs
    | _ => false
    end.


  Definition lookupArgument schema (tname fname argname : Name) : option FieldArgumentDefinition :=
    match lookupField schema tname fname with
    | Some (Field fname args _) => let n_eq n arg := let: FieldArgument name _ := arg in n == name
                                  in
                                  find (n_eq argname) args
    | _ => None
    end.

End SchemaAux.


Arguments root [Name].
Arguments lookupName [Name].
Arguments isEnumType [Name].
Arguments fields [Name].
Arguments fieldType [Name].
Arguments unwrapTypeName [Name].
Arguments lookupField [Name].
Arguments lookupFieldType [Name].
Arguments union [Name].
