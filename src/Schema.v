From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord.

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
    Fixpoint name_of_type (ty : type) : NamedType :=
      match ty with
      | NT name => name
      | ListType ty' => name_of_type ty'
      end.

    Coercion name_of_type : type >-> Ord.sort.


    (** Get a tree out of a type **)
    Fixpoint tree_of_type (ty : type) : GenTree.tree Name :=
      match ty with
      | NT n => GenTree.Node 0 [:: GenTree.Leaf n]
      | ListType ty' => GenTree.Node 1 [:: tree_of_type ty']
      end.
      
    (** Get a type out of a tree or none **)
    Fixpoint type_of_tree (t : GenTree.tree Name) : option type :=
      match t with
      | GenTree.Node 0 [:: GenTree.Leaf n] => Some (NT n)
      | GenTree.Node 1 [:: t'] => if (type_of_tree t') is Some ty then
                                   Some (ListType ty)
                                 else
                                   None
      | _ => None
      end.
      
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

    (** Extractors for a FieldArgument **)
    Definition argname arg := let: FieldArgument n _ := arg in n.
    Definition argtype arg := let: FieldArgument _ t := arg in t.
    

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
                                      (args : seq FieldArgumentDefinition)
                                      (return_type : type).

    (** Extractors for a Field **)
    Definition field_name fld := let: Field f _ _ := fld in f.
    Definition field_args fld := let: Field _ args _ := fld in args.
    Definition return_type fld := let: Field _ _ ty := fld in ty.

    (** Packing and unpacking of a field, needed for canonical instances **)
    Definition prod_of_field (f : FieldDefinition) := let: Field n args t := f in (n, args, t).
    Definition field_of_prod (p : Name * (seq.seq FieldArgumentDefinition) * type)  := let: (n, args, t) := p in Field n args t.

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
    | ObjectTypeDefinition : Name -> seq NamedType -> seq FieldDefinition -> TypeDefinition
    | InterfaceTypeDefinition : Name -> seq FieldDefinition -> TypeDefinition
    | UnionTypeDefinition : Name -> seq NamedType -> TypeDefinition
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
    Record schema := Schema {
                        query_type : NamedType;
                        typeDefinitions : seq TypeDefinition
                      }.


  End TypeSystem.

 
      



  
  



   
  Fixpoint name_of_type_definition tdef : Name :=
    match tdef with 
    | ScalarTypeDefinition name => name
    | ObjectTypeDefinition name _ _ => name
    | InterfaceTypeDefinition name _ => name
    | UnionTypeDefinition name _ => name
    | EnumTypeDefinition name _ => name
    end.
  
  Coercion name_of_type_definition : TypeDefinition >-> Ord.sort.

  
  Definition type_definition_eq tdef1 tdef2 :=
    match tdef1, tdef2 with
    | ScalarTypeDefinition n, ScalarTypeDefinition n' => n == n'
    | ObjectTypeDefinition n tys flds, ObjectTypeDefinition n' tys' flds' => [&& (n == n'), (tys == tys') & (flds == flds')]
    | InterfaceTypeDefinition n flds, InterfaceTypeDefinition n' flds' => (n == n') && (flds == flds')
    | UnionTypeDefinition n mbs, UnionTypeDefinition n' mbs' => (n == n') && (mbs == mbs')
    | EnumTypeDefinition n es, EnumTypeDefinition n' es' => (n == n') && (es == es')
    | _, _ => false
    end.
  

  Lemma type_definition_eqP : Equality.axiom type_definition_eq.
  Proof.
    move=> t1 t2; apply: (iffP idP) => [|<-].
    elim: t1; elim: t2 => //.
      by move=> n n' /= /eqP => ->.
      by move=> n tyzs flds n' tys' flds' /=; case/and3P=> /eqP -> /eqP -> /eqP ->.
      by move=> n flds n' flds' /= /andP [/eqP -> /eqP ->].  
      by move=> n mbs n' mbs' /andP [/eqP -> /eqP ->].
      by move=> n es n' es' /andP [/eqP -> /eqP ->].
    by elim: t1; move=> * /=; rewrite !eqxx.
  Qed.

    
  Definition type_definition_eqMixin := EqMixin type_definition_eqP.
  Canonical type_definition_eqType := EqType TypeDefinition type_definition_eqMixin.


  

  Definition prod_of_schema (s : schema) := let: Schema q tdefs := s in (q, tdefs).
  Definition schema_of_prod p := let: (q, tdefs) := p in Schema q tdefs.

  Lemma prod_of_schemaK : cancel prod_of_schema schema_of_prod.  Proof. by case. Qed.
  
  Definition schema_eqMixin := CanEqMixin prod_of_schemaK.
  Canonical schema_eqType := EqType schema schema_eqMixin.
  
      
  Definition fun_of_schema (s : schema) : TypeDefinition -> bool := fun tdef => tdef \in s.(typeDefinitions).
  Coercion fun_of_schema : schema >-> Funclass.
  Coercion typeDefinitions : schema >-> seq.


  Lemma in_schemaE (s : schema) tdef : s tdef = (tdef \in s.(typeDefinitions)).
  Proof. done. Qed.
    
  Definition is_named tdef name : bool :=
    match tdef with
    | ScalarTypeDefinition n => n == name
    | ObjectTypeDefinition n _ _ => n == name
    | InterfaceTypeDefinition n _ => n == name
    | UnionTypeDefinition n _ => n == name
    | EnumTypeDefinition n _ => n == name
    end.
  
  Definition pred_of_schema (s : schema) : collective_pred Name :=
    [pred ty : Name | has (fun tdef => is_named tdef ty) s.(typeDefinitions)].
  
  Canonical schema_predType := mkPredType pred_of_schema.
  
  Definition tdef_pred_of_schema (s : schema) :=
    [pred tdef : TypeDefinition | tdef \in s.(typeDefinitions)].
    
    
  Lemma name_in_schemaE (s : schema) (n : Name) : n \in s = has (fun tdef => is_named tdef n) s.
  Proof. done. Qed.
    
     
  Definition contains_field_name tdef (name : Name) : bool :=
    match tdef with
    | ScalarTypeDefinition _ => false
    | ObjectTypeDefinition n _ flds => has (fun fld => fld.(field_name) == name) flds
    | InterfaceTypeDefinition n flds => has (fun fld => fld.(field_name) == name) flds
    | UnionTypeDefinition n mbs => name \in mbs
    | EnumTypeDefinition n evs => name \in evs
    end.
    
    Definition pred_of_type_definition (tdef : TypeDefinition) : collective_pred Name :=
      [pred ty : Name | contains_field_name tdef ty].
  
    Canonical type_definition_predType := mkPredType pred_of_type_definition.
    
    Lemma in_typeDefinitionE (tdef : TypeDefinition) (n : Name) : n \in tdef = contains_field_name tdef n.
    Proof. done. Qed.
    
    
End Schema.



Notation "[ name ]" := (ListType name).
Notation "argname : ty" := (FieldArgument argname ty) : schema_scope.
Notation "fname '(' args ')' ':' ty" := (Field fname args ty) (at level 50) : schema_scope.
Notation "'scalar' S" := (ScalarTypeDefinition S) (at level 0) : schema_scope.
Notation "'object' O '{' flds '}'" := (ObjectTypeDefinition O [::] flds) : schema_scope.
Notation "'object' O 'implements' I '{' flds '}'" := (ObjectTypeDefinition O I flds) : schema_scope.
Notation "'interface' I '{' flds '}'" := (InterfaceTypeDefinition I flds) : schema_scope.
Notation "'union' U '{' mbs '}'" := (UnionTypeDefinition U mbs) : schema_scope.
Notation "'enum' E '{' evs '}'" := (EnumTypeDefinition E evs) : schema_scope.

Arguments NamedType [Name].
Arguments type [Name].
Arguments FieldArgumentDefinition [Name].
Arguments FieldDefinition [Name].
Arguments TypeDefinition [Name].
Arguments Schema [Name].

Arguments name_of_type [Name].