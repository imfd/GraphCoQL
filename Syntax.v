Require Import List.
Import ListNotations.


Require Export Meta.



(*
======
Types
======
*)

Inductive ty : Type :=
| TScalar : scalar_id -> ty
| TEnum : enum_id -> ty
| TObject : object_id -> ty
| TInterface : interface_id -> ty
| TUnion : union_id -> ty                                 
| TList : ty -> ty.




(*
========
Program
========
*)

Inductive fieldDecl : Type :=
  | Field : field_id -> list (svar * ty) -> ty -> fieldDecl.


Inductive objectDecl : Type :=
  | Object : object_id -> interface_id -> list fieldDecl -> objectDecl.	(* Only one interface *)


Inductive interfaceDecl : Type :=
  | Interface : interface_id -> list fieldDecl -> interfaceDecl.	

Inductive scalarDecl : Type :=
  | Scalar : scalar_id -> scalarDecl.

Inductive enumDecl : Type :=
  | Enum : 


Definition schema := (list objectDecl * list interfaceDecl * expr)%type.	


Definition classLookup(P : program)(c : class_id) : option classDecl :=
  match P with
    | (cs, _, _) =>
      let c_eq c cls := match cls with
                          | Cls c' _ _ _ => beq_nat c c'
                        end
      in
      find (c_eq c) cs
  end.

Definition interfaceLookup(P : program)(i : interface_id) : option interfaceDecl :=
  match P with
    | (_, ids, _) =>
      let i_eq i intr := match intr with
                          | Interface i' _ => beq_nat i i'
                          | ExtInterface i' _ _ => beq_nat i i'
                        end
      in
      find (i_eq i) ids
  end.

Definition fieldLookup(fs : list fieldDecl)(f : field_id) :=
  let f_eq f fld := match fld with
                     | Field f' _ => beq_nat f f'
		(*   | FieldWithArgs f' _ _ => beq_nat f f' *)
                    end
  in
  find (f_eq f) fs.

Definition fields(P : program)(t : ty) :=
  match t with
    | TClass c => match classLookup P c with
                    | Some (Cls _ _ fs _) => Some fs
                    | None => None
                  end
    | _ => None
  end.

(*
Definition methodLookup(ms : list methodDecl)(m : method_id) :=
  let m_eq m mtd := match mtd with
                      | Method m' _ _ _ => beq_nat m m'
                    end
  in
  find (m_eq m) ms.

Definition methods(P : program)(t : ty) :=
  match t with
    | TClass c => match classLookup P c with
                    | Some (Cls _ _ _ ms) => Some ms
                    | None => None
                  end
    | _ => None
  end. 

Definition methodSigLookup(ms : list methodSig)(m : method_id) :=
  let m_eq m mtd := match mtd with
                      | MethodSig m' _ _ => beq_nat m m'
                    end
  in
  find (m_eq m) ms.

Definition extractSigs(ms : list methodDecl) :=
  let extract := fun mtd => match mtd with
                              | Method m param t e => MethodSig m param t
                            end
  in
  map extract ms.

Inductive methodSigs(P : program) : ty -> list methodSig -> Prop :=
  | MSigs_Class :
      forall c i fs ms,
        classLookup P c = Some (Cls c i fs ms) ->
        methodSigs P (TClass c) (extractSigs ms)
  | MSigs_Interface :
      forall i msigs,
        interfaceLookup P i = Some (Interface i msigs) ->
        methodSigs P (TInterface i) msigs
  | MSigs_ExtInterface :
      forall i i1 i2 msigs1 msigs2,
        interfaceLookup P i = Some (ExtInterface i i1 i2) ->
        methodSigs P (TInterface i1) msigs1 ->
        methodSigs P (TInterface i2) msigs2 ->
        methodSigs P (TInterface i) (msigs1 ++ msigs2)
  | MSigs_Unit :
      methodSigs P TUnit []. *)


Fixpoint declsToFields (l : list fieldDecl) :=
  match l with
    | nil => empty
    | fd :: fs =>
      match fd with
        | Field f _ =>
          extend (declsToFields fs) f VNull
      end
end.
