From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From CoqUtils Require Import string.



Delimit Scope gql_scope with GQL.
Open Scope gql_scope.

   Notation Name := string.
  
  (**
     Same as names, except that it can't be true, false or null. 
     Right now it is just the same as Name.

     https://facebook.github.io/graphql/June2018/#EnumValue 
   *)

  Notation EnumValue := string.

  
Section Base.

   
  Section Types.

    
    (** *** Types of data expected by query variables.
        
        - NonNull types are omitted in this current version.
        
        https://graphql.github.io/graphql-spec/June2018/#sec-Type-References

     *)
    Inductive type : Type :=
    | NamedType : Name -> type
    | ListType : type -> type.



  
    (** Get a type's wrapped name.
        Corresponds to a named type's actual name or the name used in a list type

        https://facebook.github.io/graphql/June2018/#sec-Type-References
        https://facebook.github.io/graphql/June2018/#sec-Wrapping-Types **)
    Fixpoint tname (ty : type) : Name :=
      match ty with
      | NamedType name => name
      | ListType ty' => tname ty'
      end.

    Coercion tname : type >-> Name.

    Section Equality.
      (* This section is only to establish that type belongs to eqType *)
      
      (** Packing and unpacking of a type, needed for canonical instances **)
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


      (** Cancelation lemma for types **)
      Lemma pcan_tree_of_type : pcancel tree_of_type type_of_tree.
      Proof. by elim=> [| t /= ->]. Qed.
      
      Canonical type_eqType := EqType type (PcanEqMixin pcan_tree_of_type).
      Canonical type_choiceType := ChoiceType type (PcanChoiceMixin pcan_tree_of_type).


    End Equality.
    
  End Types.


End Base.


Notation "[ name ]" := (ListType name).