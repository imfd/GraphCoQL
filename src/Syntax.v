Require Import List.
Import ListNotations.

Require Import Coq.Arith.EqNat.


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
(*| TUnion : union_id -> ty    *)                             
| TList : ty -> ty.




(*
========
Program
========
*)

Inductive fieldDecl : Type :=
  | Field : field_id -> list (var * ty) -> ty -> fieldDecl.


Inductive objectDecl : Type :=
  | Object : object_id -> interface_id -> list fieldDecl -> objectDecl.	(* Only one interface *)


Inductive interfaceDecl : Type :=
  | Interface : interface_id -> list fieldDecl -> interfaceDecl.  (* Omitting interface implementing other interfaces *)	

Inductive scalarDecl : Type :=
  | Scalar : scalar_id -> scalarDecl.

Inductive enumDecl : Type :=
  | Enum : list var -> enumDecl.   (* How to represent each val in enum? just a nat? *)

(*Inductive unionDecl : Type :=
  | Union : *)

Definition schema := (list objectDecl * list interfaceDecl * list scalarDecl * list enumDecl)%type.	





Definition objectLookup (S : schema) (obj : object_id) : option objectDecl :=
  match S with
    | (objs, _, _, _) =>
      let o_eq o ob := match ob with
                          | Object o' _ _ => beq_nat o o'
                        end
      in
      find (o_eq obj) objs
  end.

Definition interfaceLookup (S : schema) (i : interface_id) : option interfaceDecl :=
  match S with
    | (_, ifs, _, _) =>
      let i_eq i intr := match intr with
                          | Interface i' _ => beq_nat i i'
                        end
      in
      find (i_eq i) ifs
  end.

Definition scalarLookup (S : schema) (s : scalar_id) : option scalarDecl :=
  match S with
  | (_, _, ss, _) =>
    let s_eq s sclr := match sclr with
                          | Scalar s' => beq_nat s s'
                        end
      in
    find (s_eq s) ss
  end.


Definition fieldLookup (fs : list fieldDecl) (f : field_id) :=
  let f_eq f fld := match fld with
                     | Field f' _ _ => beq_nat f f'
		(*   | FieldWithArgs f' _ _ => beq_nat f f' *)
                    end
  in
  find (f_eq f) fs.

Definition fields (S : schema) (t : ty) :=
  match t with
    | TObject o => match objectLookup S o with
                  | Some (Object _ _ fs) => Some fs
                  | None => None
                  end
    | TInterface i => match interfaceLookup S i with
                     | Some (Interface _ fs) => Some fs
                     | None => None
                      end
    (*| TList t' => fields S t'*)
    | _ => None
  end.




Inductive wfType (S : schema) : ty -> Prop :=
  | WF_TObject :
      forall o,
        objectLookup S o <> None ->
        wfType S (TObject o)
  | WF_TInterface :
      forall i,
        interfaceLookup S i <> None ->
        wfType S (TInterface i)
  | WF_TScalar :
      forall s,
        scalarLookup S s <> None ->
        wfType S (TScalar s).


Inductive subtypeOf (S : schema) : ty -> ty -> Prop :=
  | Sub_Class :
      forall o i fs,
        objectLookup S o = Some (Object o i fs) ->
        subtypeOf S (TObject o) (TInterface i)
 
  | Sub_Refl :
      forall t,
        wfType S t ->
        subtypeOf S t t
  | Sub_Trans :
      forall t1 t2 t3,
        subtypeOf S t1 t2 ->
        subtypeOf S t2 t3 ->
        subtypeOf S t1 t3.