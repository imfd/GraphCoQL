(* begin hide *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String.
Require Import QString.

(* end hide *)


(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GraphQL Schema</h1>
        <p class="lead">
         This file contains the basic definitions necessary to build a GraphQL Schema. 
        </p>

        <p>
         Some of these are: Type definitions (Objects, Interfaces, etc.), Field definitions and its arguments, amongst others.
        </p>
        <p>
        These definitions allow building a Schema but they do not guarantee that the schema is well-formed.
        The notion of well-formedness is covered in the <a href='GraphCoQL.SchemaWellFormedness.html'>SchemaWellFormedness</a> file.
    
        </p>
  </div>
</div>#
 *)


(** **** Names (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Names'><span>&#167;</span>2.1.9</a>#) *)
Notation Name := string.

(** **** Enum values (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Enum-Value'><span>&#167;</span>2.9.6</a>#)
        
     Same as names, except that it can't be true, false or null. 
     Right now it is just the same as Name.
 *)
Notation EnumValue := string.



Section Schema.


  (** * Base types 
      ----
      This section includes the basic definition for base types.
   *)

  Section Base.
    
    (** *** Type (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Type-References'><span>&#167;</span>2.11</a>#)
        ---- 
     *)
    Inductive type : Type :=
    | NamedType : Name -> type
    | ListType : type -> type.


    (** ---- *)    
    (** Get a type's wrapped name. *)
    Fixpoint tname (ty : type) : Name :=
      match ty with
      | NamedType name => name
      | ListType ty' => tname ty'
      end.

    
    Coercion tname : type >-> Name.

  End Base.

  (** * Type System 
      (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Type-System'><span>&#167;</span>3</a>#)
      ---- 

      In this section we will define the necessary types and structures needed 
      to build a GraphQL Schema. These are:
      - Arguments
      - Fields 
      - Type definition 
      - Schema 
   *)
  Section TypeSystem.

    (** *** Argument Definition (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Arguments'><span>&#167;</span>3.6.1</a>#)
        ----
     *)
    Record FieldArgumentDefinition := FieldArgument {
                                            argname : Name;
                                            argtype : type
                                          }.


    (** *** Field Definition (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##FieldDefinition'><span>&#167;</span>3.6</a>#)
        ----
    *)
    Record FieldDefinition := Field {
                                    fname : Name;
                                    fargs : seq FieldArgumentDefinition;
                                    ftype : type
                                  }.


    (** *** Type Definition (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Types'><span>&#167;</span>3.4</a>#)
        ---- 

        Possible type definitions in a GraphQL service.

     *)

    Inductive TypeDefinition : Type :=
    | ScalarTypeDefinition (name : Name)
                           
    | ObjectTypeDefinition (name : Name)
                           (interfaces : seq Name)
                           (fields : seq FieldDefinition)
                           
    | InterfaceTypeDefinition (name : Name)
                              (fields : seq FieldDefinition)
                              
    | UnionTypeDefinition (name : Name)
                          (members : seq Name)
                          
    | EnumTypeDefinition (name : Name)
                         (members : seq EnumValue).
    

  

    (** *** Schema Definition (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/#sec-Schema'><span>&#167;</span>3.2</a>#)
        ----

        Here we define the actual structure of a GraphQL Schema, which consists of:
        - A root type operation for query.
        - A list of type definitions.        
    *)
    Record graphQLSchema := GraphQLSchema {
                                  query_type : Name;
                                  type_definitions : seq TypeDefinition
                                }.
    
    
  End TypeSystem.  
    
End Schema.


(** *** Notations
    ----

    Just some notations to make it easier to read (or at least closer to how it is in
    the Spec).
 *)


Delimit Scope schema_scope with SCHEMA.
Open Scope schema_scope.

Notation "[ name ]" := (ListType name).  

Notation "'scalar' scalar_name" := (ScalarTypeDefinition scalar_name) (at level 0) : schema_scope.

(* Using 'type', as in the spec, clashes with the actual type called 'type'... So I preferred object instead *)
Notation "'object' object_name 'implements' interfaces '{' fields '}'" :=
  (ObjectTypeDefinition object_name interfaces fields)
    (object_name at next level, interfaces at next level, fields at next level) : schema_scope.

Notation "'interface' interface_name '{' fields '}'" :=
  (InterfaceTypeDefinition interface_name fields)
  (interface_name at next level, fields at next level) : schema_scope.

Notation "'union' union_name '{' union_members '}'" :=
  (UnionTypeDefinition union_name union_members)
  (union_name at next level, union_members at next level) : schema_scope.

Notation "'enum' enum_name '{' enum_members '}'" :=
  (EnumTypeDefinition enum_name enum_members)
    (enum_name at next level, enum_members at next level) : schema_scope.



(** ---- *)

(**
   We also establish that all these structures have a decidable procedure for equality but 
   we omit them here to unclutter the doc (they may still be seen in the source code).
 *)

(** ---- *)

(** #<a href='GraphCoQL.SchemaWellFormedness.html' class="btn btn-info" role='button'>Continue Reading → Schema Well-Formedness </a># *)


(* begin hide *)
Section Equality.
  (** * Equality 
     This section deals with some SSReflect bureaucratic things, in particular 
     establishing that the different components in the schema (type, fields, type definitions, etc.)
     do have a decidable procedure to establish equality between them (they belong to the 
     SSReflect type - eqType).

     This is basically done by establishing isomorphisms between the different structures
     to others that already have a decidable procedure.
   *)

  
  (** 
      The two following functions serve to establish the ismorphism between [type]
      and a tree structure.
   *)
  Fixpoint tree_of_type (ty : type) : GenTree.tree Name :=
    match ty with
    | NamedType n => GenTree.Node 0 [:: GenTree.Leaf n]
    | ListType ty' => GenTree.Node 1 [:: tree_of_type ty']
    end.
  
  Fixpoint type_of_tree (t : GenTree.tree Name) : option type :=
    match t with
    | GenTree.Node 0 [:: GenTree.Leaf n] => Some (NamedType n)
    | GenTree.Node 1 [:: t'] => if (type_of_tree t') is Some ty then
                                 Some (ListType ty)
                               else
                                 None
    | _ => None
    end.


  (**
     This lemma states that effectively both functions establish 
     an isomorphism between [type] and a tree structure.
   *)
  Lemma pcan_tree_of_type : pcancel tree_of_type type_of_tree.
  Proof. by elim=> [| t /= ->]. Qed.


  
  Canonical type_eqType := EqType type (PcanEqMixin pcan_tree_of_type).
  Canonical type_choiceType := ChoiceType type (PcanChoiceMixin pcan_tree_of_type).



  (** Packing and unpacking of a field argument, needed for canonical instances **)
  Definition prod_of_arg (arg : FieldArgumentDefinition) := let: FieldArgument n t := arg in (n, t).
  Definition arg_of_prod (p : prod Name type) := let: (n, t) := p in FieldArgument n t.

  (** Cancelation lemma for field arguments **)
  Lemma prod_of_argK : cancel prod_of_arg arg_of_prod.  Proof. by case. Qed.
  
  Canonical arg_eqType := EqType FieldArgumentDefinition (CanEqMixin prod_of_argK).
  Canonical arg_choiceType := ChoiceType FieldArgumentDefinition (CanChoiceMixin prod_of_argK).


  
  (** Packing and unpacking of a field, needed for canonical instances **)
  Definition prod_of_field (f : FieldDefinition) := let: Field n args t := f in (n, args, t).
  Definition field_of_prod (p : Name * (seq FieldArgumentDefinition) * type)  := let: (n, args, t) := p in Field n args t.

  (** Cancelation lemma for a field **)
  Lemma prod_of_fieldK : cancel prod_of_field field_of_prod. Proof. by case. Qed.

  
  Canonical field_eqType := EqType FieldDefinition (CanEqMixin prod_of_fieldK).
  Canonical field_choiceType := ChoiceType FieldDefinition (CanChoiceMixin prod_of_fieldK).


  
  (** Packing and unpacking of a type definition, needed for canonical instances **)
  Notation tdefRep := (Name + (Name * (seq Name) * seq FieldDefinition) + (Name * seq FieldDefinition) +
                      (Name * (seq Name)) + (Name * (seq EnumValue)))%type.

  
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

  

  
  (** Packing and unpacking of a schema **)
  Definition prod_of_schema (s : graphQLSchema) := let: GraphQLSchema q tdefs := s in (q, tdefs).
  Definition schema_of_prod p := let: (q, tdefs) := p in GraphQLSchema q tdefs.

  (** Cancelation lemma for a schema **)
  Lemma prod_of_schemaK : cancel prod_of_schema schema_of_prod.  Proof. by case. Qed.
  
  Canonical schema_eqType := EqType graphQLSchema (CanEqMixin prod_of_schemaK).
  Canonical schema_choiceType := ChoiceType graphQLSchema (CanChoiceMixin prod_of_schemaK).

  
End Equality.
(* end hide *)