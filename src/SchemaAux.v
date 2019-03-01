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
  
  (**
   Looks up a name in the given document, returning the type definition if it
   was declared in the document.
   **)
  Definition lookup_type (ty : NamedType)  : option TypeDefinition :=
    get_first (has_name ty) schema.
    

  Lemma lookup_typeP ty :
    reflect (exists2 tdef, tdef \in schema.(type_definitions) & tdef.(tdname) = ty)
            (lookup_type ty).
  Proof.
    apply: (iffP idP).
    - rewrite /lookup_type.
      move/get_firstP => [x Hin].
      by rewrite /has_name => /eqP ->; exists x.
    - case=> tdef Hin <-.
      rewrite /lookup_type.
      apply/get_firstP.
      by exists tdef => //; rewrite /has_name.
  Qed.

  Lemma lookup_type_isSome ty tdef : lookup_type ty = Some tdef -> lookup_type ty.
  Proof. by move=> ->. Qed.


  Hint Resolve mem_head mem_tail.
  Lemma lookup_in_schema ty tdef :
    lookup_type ty = Some tdef ->
    tdef \in schema.(type_definitions).
  Proof.
    rewrite /lookup_type.
    elim: (schema.(type_definitions)) => // hd tl IH.
    rewrite /get_first.
    by case: has_name => //; [case=> -> | move/IH => //; apply: mem_tail].
  Qed.

  Lemma lookup_type_name ty tdef : lookup_type ty = Some tdef -> ty = tdef.(tdname).
  Proof.
    rewrite /lookup_type.
    elim: schema.(type_definitions) => // hd tl IH.
    rewrite /get_first.
      by case Hn : has_name => //; move/has_nameP: Hn => ->; case => ->.
  Qed.

  
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


  (** Get all type definitions' names from a schema **)
  Definition schema_names : {fset Name} := fset [seq tdef.(tdname) | tdef <- schema]. 


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
      
    (**
     Get the union's types' names.
     If the type is not declared as Union in the Schema, then returns None.
   **)
  Definition union_members (ty : NamedType) : {fset NamedType} :=
    match lookup_type ty with
    | Some (UnionTypeDefinition name mbs) => mbs
    | _ => fset0
    end.

  (* Valid for wf schema *)
  Lemma union_members_nfset0P ty : reflect (is_union_type ty) (union_members ty != fset0).
  Proof.
    apply: (iffP idP).
    - move/fset0Pn=> [x].
      rewrite /union_members.
      funelim (is_union_type ty) => //; rewrite Heq //.
    - funelim (is_union_type ty) => // _.
      rewrite /union_members Heq.
  Admitted.

      
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
      fset [seq tdef.(tdname) | tdef <- filtered]
    | Some (UnionTypeDefinition _ mbs) => fset mbs
    | _ => fset0
    end.
  
  Definition implementation (ty : NamedType) : {fset NamedType} :=
    fset [seq tdef.(tdname) | tdef <- schema & implements_interface ty tdef].



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
    reflect (exists2 x, x \in schema.(type_definitions) & implements_interface ty x) (implementation ty != fset0).
  Proof.
    apply: (iffP idP).
    - rewrite /implementation.
      move/fset_N_fset0/in_N_nilP => [x /mapP [x']].
      by rewrite mem_filter => /andP [Himpl Hin] _; exists x'.
    - case=> [x Hin Himpl].
      rewrite /implementation fset_N_fset0.
      apply/seq0Pn. exists (x.(tdname)).
      by apply/mapP; exists x => //;rewrite mem_filter; apply/andP.
  Qed.
      
  Lemma implementation_has ty :
    implementation ty != fset0 <-> has (implements_interface ty) schema.
  Proof.
    split.
    - by move/implementationP=> H; apply/hasP.
    - by move/hasP=> H; apply/implementationP.
  Qed.
    

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
      move/lookup_type_name: Hlook => -> /=.
      by rewrite /implementation in_fset; constructor 2.
    - move=> un mbs Hlook.
        by rewrite in_fset /union_members Hlook; constructor 3.
  Qed.


 
  
End SchemaAux.


Arguments lookup_type [Name].
Arguments is_enum_type [Name].

Arguments lookup_field_in_type [Name].
Arguments lookup_field_type [Name].
Arguments union_members [Name].
