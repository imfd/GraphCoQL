Require Import List.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fset fmap.


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

  Lemma get_firstP {A : eqType} (p : pred A) (s : seq A) : reflect (exists2 x, x \in s & p x) (get_first p s).
  Proof.
    apply: (iffP idP).
    - elim: s => // hd tl IH.
      rewrite /get_first.
      case: ifP => //.
        * by exists hd => //; apply mem_head.
        * by move=> _ /IH; case=> [x Hin Hp]; exists x => //; rewrite in_cons; apply/orP; right.     
    - case=> x Hin Hp.
      rewrite /get_first.
      elim: s Hin => // hd tl IH.
      rewrite in_cons => /orP [/eqP <- | Htl].
      by rewrite Hp.
      case: ifP => // _.
      by apply: IH.
  Qed.

  Lemma mem_tail {A : eqType} (tl : seq A) (x hd : A) : x \in tl -> x \in (hd :: tl).
  Proof.
      by rewrite in_cons => Hin; apply/orP; right.
  Qed.
  

      
 Lemma get_first_E A (p : pred A) s tdef : (get_first p s = Some tdef) -> get_first p s.
  Proof.
    by move=> ->. Qed.
  
  (** Checks whether the given type definition has the given name **)
  Definition has_name (name : @NamedType Name) (tdef : TypeDefinition) : bool :=
    name == tdef.(tdname).

  
  Lemma has_nameP name tdef : reflect (name = tdef.(tdname)) (has_name name tdef).
  Proof. by apply: (iffP eqP). Qed.
  

  Definition lookup_type (ty : Name) := schema.(type_definitions) ty.

  

  Lemma lookup_in_schemaP (ty : Name) tdef :
    reflect (lookup_type ty = Some tdef)
            ((ty, tdef) \in schema.(type_definitions)).
  Proof.
    apply: (iffP idP).
    - by move/getmP.
    - by rewrite /lookup_type; move/getmP.
  Qed.

  
  (** Checks whether the given type is defined as a Scalar in the Schema **)
  Definition is_scalar_type (ty : NamedType) : bool :=
    match (lookup_type ty) with
    | Some (ScalarTypeDefinition _) => true
    | _ => false
    end.


      
  (** Checks whether the given type is defined as an Object in the Schema **)
  Equations is_object_type (ty : @NamedType Name) : bool :=
    is_object_type ty with lookup_type ty :=
    {
      | Some (ObjectTypeDefinition _ _ _) := true;
      | _ := false
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
    is_interface_type ty with lookup_type ty :=
    {
      | Some (InterfaceTypeDefinition _ _) := true;
      | _ := false
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
    is_union_type ty with lookup_type ty :=
    {
      | Some (UnionTypeDefinition _ _) := true;
      | _ := false
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

  Definition is_abstract_type (ty : NamedType) : bool :=
    is_interface_type ty ||  is_union_type ty.
  

  Lemma is_object_type_interfaceN ty :
    is_object_type ty ->
    is_interface_type ty = false.
  Proof.
    funelim (is_object_type ty) => //.
    by rewrite is_interface_type_equation_1 Heq /=.
  Qed.

  Lemma is_object_type_unionN ty :
    is_object_type ty ->
    is_union_type ty = false.
  Proof.
    by funelim (is_object_type ty); rewrite is_union_type_equation_1 Heq /=.
  Qed.

  Lemma is_interface_type_objectN ty :
    is_interface_type ty ->
    is_object_type ty = false.
  Proof.
    by funelim (is_interface_type ty); simp is_object_type; rewrite Heq.
  Qed.
  
  Lemma is_interface_type_unionN ty :
    is_interface_type ty ->
    is_union_type ty = false.
  Proof.
      by funelim (is_interface_type ty); rewrite is_union_type_equation_1 Heq /=.
  Qed.

  Lemma is_interface_is_abstract ty :
    is_interface_type ty ->
    is_abstract_type ty.
  Proof.
    by intros; rewrite /is_abstract_type; apply/orP; left.
  Qed.

  Lemma is_union_is_abstract ty :
    is_union_type ty  ->
    is_abstract_type ty.
  Proof.
    by intros; rewrite /is_abstract_type; apply/orP; right.
  Qed.

  Lemma is_union_type_objectN ty :
    is_union_type ty ->
    is_object_type ty = false.
  Proof.
    by funelim (is_union_type ty); simp is_object_type; rewrite Heq.
  Qed.
  

  Lemma is_object_ifT {A : Type} ty (Tb Fb : A) :
    is_object_type ty -> (if is_object_type ty then Tb else Fb) = Tb.
  Proof.
      by case is_object_type.
  Qed.

  Lemma is_object_ifinterfaceF {A : Type} ty (Tb Fb : A) :
    is_object_type ty -> (if is_interface_type ty then Tb else Fb) = Fb.
  Proof.
    by move=> Hobj; move: (is_object_type_interfaceN Hobj) => ->. 
  Qed.

  Lemma is_object_ifunionF {A : Type} ty (Tb Fb : A) :
    is_object_type ty -> (if is_union_type ty then Tb else Fb) = Fb.
  Proof.
    by move=> Hobj; move: (is_object_type_unionN Hobj) => ->.
  Qed.

  
  Lemma abstract_type_N_obj ty :
    is_abstract_type ty -> is_object_type ty = false.
  Proof.
    by rewrite /is_abstract_type => /orP [/is_interface_type_objectN -> | /is_union_type_objectN ->].
  Qed.

  
  (** Get all unduplicated argument names from a field **)
  Definition field_arg_names (fld : FieldDefinition) : {fset Name} := fset [seq arg.(argname) | arg <- fld.(fargs)].


  (** Get all field names from a type definition **)
  Definition tdef_field_names (tdef : @TypeDefinition Name) : {fset Name} := fset [seq fld.(fname) | fld <- tdef.(tfields)].

  
  (** Get list of fields declared in an Object or Interface type definition **)
  Definition fields (ty : NamedType) : seq FieldDefinition :=
    match lookup_type ty with
    | Some (ObjectTypeDefinition _ _ flds) => flds
    | Some (InterfaceTypeDefinition _ flds) => flds
    | _ => [::]
    end.

  Lemma fields_E (tdef : @TypeDefinition Name) :
    (tdef.(tdname), tdef) \in schema.(type_definitions) ->
    fields tdef.(tdname) = tdef.(tfields).
  Proof.
    move/lookup_in_schemaP => Hlook.
    rewrite /fields /tfields Hlook.
    by case: tdef Hlook. 
  Qed.

  (** Get all type definitions' names from a schema **)
  Definition schema_names : {fset Name} := fset [seq tdef.(tdname) | tdef <- codomm (schema.(type_definitions))]. 


  (** Check whether a given name is declared in the schema, as a type definition **)
  Definition is_declared (name : Name) : bool := name \in schema_names.


  (** Checks whether the field has the given name **)
  Definition has_field_name (name : Name) (fld : FieldDefinition) :=
    name == fld.(fname).

  Lemma has_field_nameP (name : Name) (fld : FieldDefinition) :
    reflect (name = fld.(fname)) (has_field_name name fld).
  Proof.
    by apply: (iffP eqP). Qed.
    
  
  (**
     Gets the first field definition from a given type that matches the given field name. 
     If the type is not declared in the Schema or the field does not belong to the type, then it returns None.
   **)
  Definition lookup_field_in_type (ty : NamedType) (fname : Name) : option FieldDefinition :=
    if lookup_type ty is Some tdef then
      get_first (has_field_name fname) tdef.(tfields)
    else
      None.


  Lemma lookup_field_in_typeP ty name :
    reflect (exists tdef fld, [/\ lookup_type ty = Some tdef,
                          fld \in tdef.(tfields) &
                                  fld.(fname) = name]) (lookup_field_in_type ty name).
  Proof.
    apply: (iffP idP).
    - rewrite /lookup_field_in_type.
      case Hlook: lookup_type => [tdef|] //.
      move/get_firstP=> [fld Hin /has_field_nameP ->].
      by exists tdef, fld.
    - case=> [tdef [fld [Hlook Hin <-]]].
      rewrite /lookup_field_in_type Hlook /=.
      apply/get_firstP.
      by exists fld => //; rewrite /has_field_name.
  Qed.

  Lemma lookup_field_in_type_is_obj_or_intf ty fname :
    lookup_field_in_type ty fname ->
    is_object_type ty \/ is_interface_type ty.
  Proof.
    move/lookup_field_in_typeP=> [tdef [fld [Hlook Hin Heq]]].
    rewrite /tfields in Hin.
    case: tdef Hlook Hin => //.
    - move=> o intfs flds Hlook _.
      by left; rewrite is_object_type_equation_1 Hlook.
    - move=> i flds Hlook _.
        by right; rewrite is_interface_type_equation_1 Hlook.
  Qed.

  Lemma lookup_field_in_union_empty ty fname :
    is_union_type ty ->
    lookup_field_in_type ty fname = None.
  Proof.
    funelim (is_union_type ty) => //.
    by rewrite /lookup_field_in_type Heq /=.
  Qed.

  
(** 
      Gets the type of the first field definition from a given type that matches the given field name. 
      If the type is not declared in the Schema or the field does not belong to the type, then it returns None.

   **)
  Definition lookup_field_type (ty : NamedType) (fname : Name)  : option type :=
    match lookup_field_in_type ty fname with
    | Some fld => Some fld.(return_type)
    | None => None
    end.


  Lemma lookup_field_typeP ty ty' fname :
    reflect (exists2 fld, lookup_field_in_type ty fname = Some fld & fld.(return_type) = ty')
            (lookup_field_type ty fname == Some ty').
  Proof.
    apply: (iffP eqP).
    - rewrite /lookup_field_type.
      case lookup_field_in_type => // fld.
      by case=> <-; exists fld.
    - move=> [fld Hlook <-].
      by rewrite /lookup_field_type Hlook.
  Qed.

    
  Lemma lookup_field_or_type lookup_type ty name fld :
    lookup_field_in_type lookup_type name = Some fld ->
    lookup_field_type lookup_type name = Some ty ->
    ty = fld.(return_type).
  Proof.
    by rewrite /lookup_field_type; move=> ->; case. Qed.


  Lemma lookup_field_type_is_obj_or_intf ty fname :
    lookup_field_type ty fname ->
    is_object_type ty \/ is_interface_type ty.
  Proof.
    rewrite /lookup_field_type.
    case Hlook: lookup_field_in_type => [tdef|] // _.
    have H: isSome (lookup_field_in_type ty fname) by rewrite /isSome Hlook.
    apply: (lookup_field_in_type_is_obj_or_intf H).
  Qed.

  Lemma lookup_field_in_type_has_type ty fname fld :
    lookup_field_in_type ty fname = Some fld ->
    lookup_field_type ty fname. 
  Proof.
      by rewrite /lookup_field_type => ->.
  Qed.

  
    (**
     Get the union's types' names.
     If the type is not declared as Union in the Schema, then returns None.
   **)
  Definition union_members (ty : NamedType) : {fset NamedType} :=
    match lookup_type ty with
    | Some (UnionTypeDefinition name mbs) => mbs
    | _ => fset0
    end.


  Lemma union_members_E tdef :
    (tdef.(tdname), tdef) \in schema.(type_definitions) ->
    union_members tdef.(tdname) = tdef.(tmbs).
  Proof.
    move/lookup_in_schemaP => Hlook.
    rewrite /union_members /tmbs {}Hlook .
      by case: tdef.
  Qed.

  Lemma in_union (t ty : Name) :
    t \in union_members ty ->
    is_union_type ty.      
  Proof.
    rewrite /union_members is_union_type_equation_1.
      by case lookup_type => //; case=> //.
  Qed.
  
  (**
     Checks whether the given type declares implementation of another type.
   **)
  Definition declares_implementation (ty ty' : NamedType) : bool :=
    match lookup_type ty with
    | Some (ObjectTypeDefinition _ intfs _) => ty' \in intfs
    | _ => false
    end.


  Lemma in_intfs ty (tdef : @TypeDefinition Name):
    ty \in tdef.(tintfs) ->
           exists n flds, tdef = ObjectTypeDefinition n tdef.(tintfs) flds.
  Proof.
    rewrite /tintfs.
    case: tdef => // o i flds Hin.
    by exists o, flds.
  Qed.
  
 
  Lemma declares_implementationP ty ity :
    reflect (exists2 tdef, lookup_type ty = Some tdef & ity \in tdef.(tintfs))
            (declares_implementation ty ity).
  Proof.
    apply: (iffP idP).
    - rewrite /declares_implementation.
      case Hlook : lookup_type => [tdef|] //.
        by exists tdef => // {Hlook}; case: tdef H => //.
    - move=> [tdef Hlook Hin].
      rewrite /declares_implementation Hlook.
      by move: (in_intfs Hin) => [n [flds ->]].
  Qed.
  
  Definition implements_interface (iname : NamedType) (tdef : @TypeDefinition Name) : bool :=
    iname \in tdef.(tintfs).



    
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

  Definition implementation (ty : NamedType) : {fset NamedType} :=
    fset [seq tdef.(tdname) | tdef <- codomm schema.(type_definitions) & implements_interface ty tdef].

  
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
        | Some (ObjectTypeDefinition _ _ _) => [:: ty];
        | Some (InterfaceTypeDefinition iname _) => implementation iname;
        | Some (UnionTypeDefinition _ mbs) => mbs;
        | _ => [::]
        }
    }.

  Lemma uniq_get_possible_types ty :
    uniq (get_possible_types ty).
  Proof.
    by funelim (get_possible_types ty) => //; apply: uniq_fset.
  Qed.
  
  

  Lemma seq0Pn (A : eqType) (s : seq A) : reflect (exists x, x \in s) (s != [::]).
  Proof.
    apply: (iffP idP) => //.
    - by case: s => // hd tl _; exists hd; apply: mem_head.
    - by case: s => //; case=> [x]; rewrite in_nil.
  Qed.
  
  Lemma fset_N_fset0 (A : ordType) (s : seq A) :
    fset s != fset0 <->
    s != [::].
  Proof. split.
    - by case: s => //; move/fset0Pn=> [x]; rewrite in_fset.
    - by move/seq0Pn=> [x Hin]; apply/fset0Pn; exists x; rewrite in_fset.
  Qed.


  Lemma in_N_nilP {A : eqType} (s : seq A) : reflect (exists x, x \in s) (s != [::]).
  Proof.
    apply: (iffP idP) => //.
    by case: s => // a *; exists a; rewrite inE; apply/orP; left. 
    by case: s => //; case=> [x]; rewrite in_nil.
  Qed.

  
  Lemma implementationP ty :
    reflect (exists2 x, x \in codomm schema.(type_definitions) & x.(implements_interface ty)) (implementation ty != fset0).
  Proof.
    apply: (iffP idP).
    - rewrite /implementation.
      move/fset_N_fset0/in_N_nilP => [x /mapP [x']].
      by rewrite mem_filter => /andP [Himpl Hin] _; exists x'.
     
    - case=> [x Hin Himpl].
      rewrite /implementation fset_N_fset0.
      apply/seq0Pn.
      exists (x.(tdname)).
      by apply/mapP; exists x => //;rewrite mem_filter; apply/andP; split.
  Qed.

  (*
  Lemma implementation_has ty :
    implementation ty != fset0 <-> has (implements_interface ty) schema.
  Proof.
    split.
    - by move/implementationP=> H; apply/hasP.
    - by move/hasP=> H; apply/implementationP.
  Qed.
    *)

  Lemma declares_in_implementation t ty :
    (declares_implementation t ty) <-> (t \in implementation ty).
  Proof.
  Admitted.

  Lemma implements_interface_is_object (ity : Name) tdef :
    (tdef.(tdname), tdef) \in schema.(type_definitions) ->
    implements_interface ity tdef ->
    is_object_type tdef.(tdname).
  Proof.
    move/lookup_in_schemaP => Hlook.
    rewrite /implements_interface.
    move/in_intfs=> [n [flds Heq]].
    rewrite Heq in Hlook * => /=.
    rewrite is_object_type_equation_1.
      by rewrite Hlook.
  Qed.

  Lemma declares_implementation_is_object (ity oty : Name) :
    declares_implementation oty ity ->
    is_object_type oty.
  Proof.
    rewrite /declares_implementation.
    case Hlook: lookup_type => [tdef|] //.
    case: tdef Hlook => // o intfs flds Hlook Hin.
    by rewrite is_object_type_equation_1 Hlook.
  Qed.
  
  Lemma in_implementation_is_object ity ty :
    ty \in implementation ity ->
           is_object_type ty.
  Proof.
    move/declares_in_implementation.
    apply: declares_implementation_is_object.
  Qed.
       
  Lemma implements_declares_implementation (ity : Name) (tdef : TypeDefinition) :
    (tdef.(tdname), tdef) \in schema.(type_definitions) ->
    declares_implementation tdef.(tdname) ity <-> implements_interface ity tdef.
  Proof.
    move/lookup_in_schemaP=> Htdef.
    split.
    - rewrite /declares_implementation.
      rewrite Htdef.
      case: tdef Htdef => // o i f Hin.
    - rewrite /implements_interface /declares_implementation Htdef.
      by case: tdef Htdef.
  Qed.

  Lemma get_possible_types_objectE ty :
    is_object_type ty ->
    get_possible_types ty = fset1 ty.
  Proof.
    move/is_object_type_E=> [o [intfs [flds Hlook]]].
    by simp get_possible_types; rewrite Hlook.
  Qed.

  Lemma in_object_possible_types t ty :
    is_object_type ty ->
    t \in get_possible_types ty ->
          t = ty.
  Proof.
    move/get_possible_types_objectE => ->.
    by rewrite in_fset1 => /eqP.
  Qed.
  
  Lemma get_possible_types_unionE ty :
    is_union_type ty ->
    get_possible_types ty = union_members ty.
  Proof.
    move/is_union_type_E => [u [mbs Hlook]].
      by simp get_possible_types; rewrite /union_members Hlook.
  Qed.
(*
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
      move: Hlook => -> /=.
      by rewrite /implementation in_fset; constructor 2.
    - move=> un mbs Hlook.
        by rewrite in_fset /union_members Hlook; constructor 3.
  Qed.

*)
 
  
End SchemaAux.


Arguments lookup_type [Name].
Arguments is_enum_type [Name].


Arguments lookup_field_in_type [Name].
Arguments lookup_field_type [Name].
Arguments union_members [Name].
