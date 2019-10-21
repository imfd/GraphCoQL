(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Value.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.

Require Import Query.


Require Import SeqExtra.

Require Import Ssromega.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GraphQL Query Auxiliary</h1>
        <p class="lead">
         This file contains auxiliary definitions used with a GraphQL Query.
        </p>

        <p>
         Some of these are: query size, extractors for selections, general purpose predicates, etc.
        </p>
  </div>
</div>#
 *)

Section QueryAux.

  
  Variable (Scalar : eqType).

  Implicit Type σs : seq (@Selection Scalar).
  Implicit Type σ : @Selection Scalar.


  (** *** General purpose predicates *)
  (** ---- *)
  Section Base.


    (** 
        Checks whether the given selection is a field selection.
     *)
    Equations is_field σ : bool :=
      {
        is_field (on _ { _ }) := false;
        is_field _ := true
      }.

    
    (** ---- *)
    (**
       Checks whether the given selection is an inline fragment.
     *)
    Equations is_inline_fragment σ : bool :=
      {
        is_inline_fragment (on _ { _ }) := true;
        is_inline_fragment _ := false
      }.
    

    (** *** Extractors for selections *)
    (** ---- *)

    (**
       Gets the name of the given selection. 
       
       Inline fragments do not have a name, therefore 
       it is required that the given selection is a field.
     *)
    Equations qname σ (Hfield : σ.(is_field)) : Name :=
      {
        qname (name[[ _ ]]) _ := name;
        qname (_:name[[ _ ]]) _ := name;
        qname (name[[ _ ]] { _ }) _ := name;
        qname (_:name[[ _ ]] { _ }) _ := name;
        qname (on _ { _ }) Hfld := _
      }.
    (**
       Gets the response name of the given selection.
       
       For aliased fields this corresponds to their alias, while for 
       non-aliased fields it corresponds to their name.

       Inline fragment do not have a response name, therefore 
       it is required that the given selection is a field.
     *)   
    Equations qresponse_name σ (Hfld : σ.(is_field)) :  Name :=
      {
        qresponse_name (name [[ _ ]]) _ := name;
        qresponse_name (alias : _ [[ _ ]]) _ := alias;
        qresponse_name (name [[ _ ]] { _ }) _ := name;
        qresponse_name (alias : _ [[ _ ]] { _ }) _ := alias;
        qresponse_name (on _ { _ }) Hfld := _
      }.


    (** ---- *)
    (**
       Gets the given selection's subselections.

       For field selections without subselections, it returns an empty list.
     *)
    Definition subselections σ : seq Selection :=
      match σ with
      | _ [[ _ ]] { φ }
      | _ : _ [[ _ ]] { φ }
      | on _ { φ } => φ
      | _ => [::]
      end.


    (** ---- *)
    (**
       Gets the given selection's arguments.

       Inline fragment do not have arguments, therefore 
       it is required that the given selection is a field.
     *)
    Equations qargs σ (Hfld : σ.(is_field)) :  seq (Name * @Value Scalar) :=
      {
        qargs (_ [[ α ]]) _ := α;
        qargs (_ : _ [[ α ]]) _ := α;
        qargs (_ [[ α ]] { _ }) _ := α;
        qargs (_ : _ [[ α ]] { _ }) _ := α;
        qargs (on _ { _ }) Hfld := _
      }.


    
    (** ---- *)
    (**
       Checks whether two selections have the same field name.

       It is always false if either is an inline fragment.
     *)
    Equations have_same_name : @Selection Scalar -> @Selection Scalar -> bool :=
      {
        have_same_name (on _ { _ }) _ := false;
        have_same_name _ (on _ { _ }) := false;
        have_same_name σ1 σ2 := (qname σ1 _) == (qname σ2 _)
      }.


    (** ---- *)
    (**
       Checks whether two selections have the same arguments.

       It is always false if either is an inline fragment.
     *)
    Equations have_same_arguments : @Selection Scalar -> @Selection Scalar -> bool :=
      {
        have_same_arguments (on _ { _ }) _ := false;
        have_same_arguments _ (on _ { _ }) := false;
        have_same_arguments σ1 σ2 := (qargs σ1 _) == (qargs σ2 _)
      }.


    (** ---- *)
    (**
       Checks whether the given selection is either a [SingleField] or [SingleAliasedField].
     *)
    Equations is_simple_field_selection σ : bool :=
      {
        is_simple_field_selection (_ [[_]]) := true;
        is_simple_field_selection (_ : _ [[_]]) := true;
        is_simple_field_selection _ := false
      }.


    (** ---- *)
    (**
       Checks whether the given selection is either a [NestedField] or [NestedAliasedField].
     *)
    Equations is_nested_field_selection σ : bool :=
      {
        is_nested_field_selection (_ [[_]] { _ }) := true;
        is_nested_field_selection (_ : _ [[_]] { _ }) := true;
        is_nested_field_selection _ := false
      }.

    (** ---- *)
    (**
       Decides whether two selections are equal, considering possible permutation
       of arguments in field selections.
     *)
    Equations selection_perm_eq (σ1 σ2 : @Selection Scalar) : bool :=
      {
        selection_perm_eq (f1[[α1]]) (f2[[α2]]) := (f1 == f2) && perm_eq α1 α2;
        selection_perm_eq (a1:f1[[α1]]) (a2:f2[[α2]]) := [&& a1 == a2, f1 == f2 & perm_eq α1 α2];
        selection_perm_eq (f1[[α1]] { σs1 }) (f2[[α2]] { σs2 }) :=
          [&& f1 == f2, perm_eq α1 α2 & selections_perm_eq σs1 σs2];
        selection_perm_eq (a1:f1[[α1]] { σs1 }) (a2:f2[[α2]] { σs2 }) :=
          [&& a1 == a2, f1 == f2, perm_eq α1 α2 & selections_perm_eq σs1 σs2];
        selection_perm_eq (on t1 { σs1 }) (on t2 { σs2 }) :=
          (t1 == t2) && (selections_perm_eq σs1 σs2);
        selection_perm_eq _ _ := false
      }
    where selections_perm_eq (σs1 σs2 : seq (@Selection Scalar)) : bool :=
            {
              selections_perm_eq [::] [::] := true;
              selections_perm_eq (σ1 :: σs1) (σ2 :: σs2) := selection_perm_eq σ1 σ2 && selections_perm_eq σs1 σs2;
              selections_perm_eq _ _ := false
            }.
    
    (** ---- *)
    (**
       Checks whether two selections are equivalent.

       This equivalence refers to whether both selections will
       produce responses with the same name and if both 
       share the same arguments.

       
       **** See also
       - [is_field_merging_possible]
     *)
    (* FIXME : Rename *)
    Definition are_equivalent (σ1 σ2 : @Selection Scalar) : bool :=
      [&& (σ1.(is_simple_field_selection) && (σ2.(is_simple_field_selection)) ||
           σ1.(is_nested_field_selection) && σ2.(is_nested_field_selection)),
       have_same_name σ1 σ2 & have_same_arguments σ1 σ2].


   

    
  End Base.

  (** *** Size functions 
      ---- 

      In this section we define functions related to
      the size of queries.
   *)
  Section Size.

    (**
       Get the size of a selection and selection set, according to H&P's definition.
     *)
    Equations selection_size σ : nat :=
      {
        selection_size (_ [[_]] { σs }) := 1 + selections_size σs;
        selection_size (_ : _ [[_]] { σs }) := 1 + selections_size σs;
        selection_size (on _ { σs }) := 1 + (selections_size σs);
        selection_size _ := 1
      }
    where
    selections_size σs : nat :=
      {
        selections_size [::] := 0;
        selections_size (σ :: σs) := selection_size σ + selections_size σs
      }.

    (** ---- *)
    (**
       Get the size of a selection set paired with its type in scope.
     *)
    Definition selections_size_aux (scoped_σs : seq (Name * Selection)) :=
      selections_size [seq sσ.2 | sσ <- scoped_σs].

    (** ---- *)
    (**
       Get the size of a query.
     *)
    Definition query_size (φ : @query Scalar) :=
      selections_size φ.(selection_set).
      

  End Size.
  


  (** *** Other type of predicates *)
  (** ---- *)
    
  Section DefPreds.
    
    Variable s : wfGraphQLSchema.

    (**       
       This predicate checks whether a type condition is valid in 
       a given object type and is necessary to check if a fragment must be evaluated.
   
       This definition is similar to the one in the spec
       (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##DoesFragmentTypeApply()'><span>&#167;</span>6.3.2</a>#). 
       The difference is simply to facilitate reasoning over it.
     *)
    Definition does_fragment_type_apply object_type fragment_type :=
      match lookup_type s object_type, lookup_type s fragment_type with
      | Some (object oname implements _ { _ }), Some (object name implements _ { _ }) =>
        object_type == name
      | Some (object _ implements interfaces { _ }), Some (interface name { _ }) =>
        name \in interfaces
      | Some (object oname implements _ { _ }), Some (union name { members }) =>
        oname \in members
      | _, _ => false
      end.

    (** ---- *)
    (**
     Checks whether a given type can be used as an inline fragment's type condition 
     in a given context with another type in scope 
     (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/#sec-Fragment-spread-is-possible'><span>&#167;</span>5.5.2.3</a>#).

     It basically amounts to intersecting the possible subtypes of each
     and checking that the intersection is not empty.     
     *)
    (* The definition of seqI is a bit annoying, maybe we could change it to 
       has (fun ty => ty \in parent_possible_types) ty_possible_types, which is 
       much simpler to reason about *)
    Definition is_fragment_spread_possible parent_type fragment_type : bool :=
      let ty_possible_types := get_possible_types s fragment_type in
      let parent_possible_types := get_possible_types s parent_type in
      let applicable_types := (ty_possible_types :&: parent_possible_types)%SEQ in
      applicable_types != [::].
    
    
  End DefPreds.
  
  

  
  (** *** Functions related to finding selections that satisfy a predicate *)
  (** ---- *)
  Section Find.

    
    Variable (s : wfGraphQLSchema).

    (**
       Find selections with response name equal to a given name.
       In case there is a fragment, it first checks that the fragment's type condition 
       applies to the given object type, then it may proceed finding in its subselections.

     *)
    Equations? find_valid_fields_with_response_name (label : Name) (object_type : Name) (σs : seq (@Selection Scalar)) :
      seq (@Selection Scalar) by wf (selections_size σs) :=
      {
        find_valid_fields_with_response_name _ _ [::] := [::];

        find_valid_fields_with_response_name k O__t (on t { βs } :: σs)
          with does_fragment_type_apply s O__t t :=
          {
          | true := find_valid_fields_with_response_name k O__t βs ++ find_valid_fields_with_response_name k O__t σs;
          | _ := find_valid_fields_with_response_name k O__t σs
          };

        find_valid_fields_with_response_name k O__t (σ :: σs)
          with (qresponse_name σ _) == k :=
          {
          | true := σ :: find_valid_fields_with_response_name k O__t σs;
          | _ := find_valid_fields_with_response_name k O__t σs
          }
      }.
    all: do ?simp selection_size; ssromega.
    Qed.

    (** ---- *)
    (**
       Find selections with response name equal to a given name.
       In case there is a fragment, it first checks that the fragment's type condition 
       applies to the given object type, then it may proceed finding in its subselections.

     *)
    Equations? find_valid_pairs_with_response_name (ts : Name) (rname : Name) (σs : seq (Name * @Selection Scalar)) :
      seq (Name * @Selection Scalar) by wf (selections_size_aux σs) :=
      {
        find_valid_pairs_with_response_name _ _ [::] := [::];

        find_valid_pairs_with_response_name ts rname ((_, on t { βs }) :: σs)
          with does_fragment_type_apply s ts t :=
          {
          | true := find_valid_pairs_with_response_name rname ts [seq (t, β) | β <- βs] ++ find_valid_pairs_with_response_name ts rname σs;
          | _ := find_valid_pairs_with_response_name ts rname σs
          };

        find_valid_pairs_with_response_name ts rname ((t, σ) :: σs)
          with (qresponse_name σ _) == rname :=
          {
          | true := (t, σ) :: find_valid_pairs_with_response_name rname ts σs;
          | _ := find_valid_pairs_with_response_name rname ts σs
          }
      }.
    all: do ? [rewrite /selections_size_aux /=; simp selection_size; rewrite -/(selections_size_aux _); ssromega].
      by rewrite /selections_size_aux /=; simp selection_size; rewrite -map_comp /funcomp /= map_id; ssromega.
    Qed.
    
    (** ---- *)
    (** 
        Find all selections with response name equal to a given name.
        It collects every field, regardless of fragment's type condition. This differs 
        with [find_valid_fields_with_response_name], where the type condition _is_ important.
     *)
    (* FIXME : Rename considering previous def *)
    Equations? find_fields_with_response_name (rname : Name) (σs : seq (@Selection Scalar)) :
      seq (@Selection Scalar) by wf (selections_size σs) :=
      {
        find_fields_with_response_name _ [::] := [::];
        
        
        find_fields_with_response_name rname (f [[α]] :: σs)
          with f == rname :=
          {
          | true := f [[α]] :: find_fields_with_response_name rname σs;
          | _ := find_fields_with_response_name rname σs
          };
        
        find_fields_with_response_name rname (l : f [[α]] :: σs)
          with l == rname :=
          {
          | true := l : f [[α]] :: find_fields_with_response_name rname σs;
          | _ := find_fields_with_response_name rname σs
          };

        
        find_fields_with_response_name rname (f [[α]] { βs } :: σs)
          with f == rname :=
          {
          | true := f [[α]] { βs } :: find_fields_with_response_name rname σs;
          | _ := find_fields_with_response_name rname σs
          };
        
        find_fields_with_response_name rname (l : f [[α]] { βs }:: σs)
          with l == rname :=
          {
          | true := l : f [[α]] { βs } :: find_fields_with_response_name rname σs;
          | _ := find_fields_with_response_name rname σs
          };
        
        find_fields_with_response_name rname (on t { βs } :: σs) :=
          find_fields_with_response_name rname βs ++ find_fields_with_response_name rname σs
      }.
    Proof.
      all: do [by simp selection_size; ssromega].
    Qed.


    (** ---- *)
    (**
        Find all selections with response name equal to a given name.
        It collects every field, regardless of fragment's type condition. This differs 
        with [find_valid_fields_with_response_name], where the type condition _is_ important.
      
     *)
    Equations? find_pairs_with_response_name (rname : Name) (σs : seq (Name * @Selection Scalar)) :
      seq (Name * @Selection Scalar) by wf (selections_size_aux σs) :=
      {
        find_pairs_with_response_name _ [::] := [::];
        
        find_pairs_with_response_name rname ((ty, f[[α]]) :: σs)
          with f == rname :=
          {
          | true := (ty, f[[α]]) :: find_pairs_with_response_name rname σs;
          | _ := find_pairs_with_response_name rname σs
          };
        
        find_pairs_with_response_name rname ((ty, l:f[[α]]) :: σs)
          with l == rname :=
          {
          | true := (ty, l:f[[α]]) :: find_pairs_with_response_name rname σs;
          | _ := find_pairs_with_response_name rname σs
          };

        
        find_pairs_with_response_name rname ((ty, f[[α]] { βs }) :: σs)
          with f == rname :=
          {
          | true := (ty, f[[α]] { βs }) :: find_pairs_with_response_name rname σs;
          | _ := find_pairs_with_response_name rname σs
          };
        
        find_pairs_with_response_name rname ((ty, l:f[[α]] { βs }) :: σs)
          with l == rname :=
          {
          | true := (ty, l:f[[α]] { βs }) :: find_pairs_with_response_name rname σs;
          | _ := find_pairs_with_response_name rname σs
          };
        
        find_pairs_with_response_name rname ((_, on t { βs }) :: σs) :=
          find_pairs_with_response_name rname [seq (t, q) | q <- βs] ++ find_pairs_with_response_name rname σs
      }.
    Proof.
      all: do ? [by rewrite /selections_size_aux /=; simp selection_size; ssromega].
      rewrite /selections_size_aux /=; simp selection_size.
      have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs.
        by intros; elim: xs => //= x xs ->.
        by ssromega.
    Qed.

     


    (** ---- *)
    (**
       Find all fragments with type condition equal to a given type.
     *)
    Equations find_fragment_with_type_condition : Name -> seq (@Selection Scalar) -> seq (@Selection Scalar) :=
      {
        find_fragment_with_type_condition _ [::] := [::];

        find_fragment_with_type_condition t (on t' { β } :: σs)
          with t == t' :=
          {
          | true := on t { β } :: find_fragment_with_type_condition t σs;
          | _ := find_fragment_with_type_condition t σs
          };

        find_fragment_with_type_condition t (σ :: σs) := find_fragment_with_type_condition t σs
      }.


  End Find.
  
  (** *** Functions related to filtering queries according to some predicate *)
  (** ---- *)
  Section Filter.

    (** 
        Remove all fields with a given response name.
     *)
    Equations? filter_fields_with_response_name (label : Name) (σs : seq (@Selection Scalar)) :
      seq (@Selection Scalar) by wf (selections_size σs) :=
      {
        filter_fields_with_response_name _ [::] := [::];

        filter_fields_with_response_name l (on t { β } :: σs) :=
          on t { filter_fields_with_response_name l β } :: filter_fields_with_response_name l σs;

        filter_fields_with_response_name l (σ :: σs)
          with (qresponse_name σ _) != l :=
          {
          | true := σ :: filter_fields_with_response_name l σs;
          | _ := filter_fields_with_response_name l σs
          }     

      }.
    all: do ?[simp selection_size; ssromega].
    Qed.


    (** ---- *)
    (**
       Remove all fields with a given response name.
     *)
     Equations? filter_pairs_with_response_name (response_name : Name) (σs : seq (Name * @Selection Scalar)) :
      seq (Name * @Selection Scalar) by wf (selections_size_aux σs) :=
      {
        filter_pairs_with_response_name _ [::] := [::];

        filter_pairs_with_response_name l ((ty, on t { β }) :: σs) :=
          (ty, on t { filter_fields_with_response_name l β }) :: filter_pairs_with_response_name l σs;

        filter_pairs_with_response_name l ((ty, σ) :: σs)
          with (qresponse_name σ _) != l :=
          {
          | true := (ty, σ) :: filter_pairs_with_response_name l σs;
          | _ := filter_pairs_with_response_name l σs
          }     

      }.
     Proof.
       all: do ? [by rewrite /selections_size_aux /=; simp selection_size; ssromega].
    Qed.
    
    

    
  End Filter.

  (** *** Functions related to merging queries *)
  (** ---- *)
  Section Merging.

    (**
       Concatenates the subqueries of every selection in the given list.
     *)
    Definition merge_selection_sets σs := flatten [seq σ.(subselections) | σ <- σs].
    

    Variable (s : wfGraphQLSchema).

    (** ---- *)
    (**
       Concatenates the subqueries of every selection in the given list.
     *)
    Equations merge_pairs_selection_sets (scoped_σs : seq (Name * @Selection Scalar)) : seq (Name * @Selection Scalar) :=
      {
        merge_pairs_selection_sets [::] := [::];

        merge_pairs_selection_sets ((ty, f[[ _ ]] { βs }) :: σs)
          with lookup_field_in_type s ty f :=
          {
          | Some fld := [seq (fld.(ftype).(tname), σ) | σ <- βs] ++ merge_pairs_selection_sets σs;
          | _ := merge_pairs_selection_sets σs
          };

        merge_pairs_selection_sets ((ty, _:f[[ _ ]] { βs }) :: σs)
          with lookup_field_in_type s ty f :=
          {
          | Some fld := [seq (fld.(ftype).(tname), σ) | σ <- βs] ++ merge_pairs_selection_sets σs;
          | _ := merge_pairs_selection_sets σs
          };

        merge_pairs_selection_sets ((_, on t { βs }) :: σs) :=
          [seq (t, σ) | σ <- βs] ++ merge_pairs_selection_sets σs;
        
        merge_pairs_selection_sets (scoped_σs :: σs) := merge_pairs_selection_sets σs
      }.

    
  End Merging.


End QueryAux.




(** ---- *)

(** 
    #<div>
        <a href='GraphCoQL.Query.html' class="btn btn-light" role='button'> Previous ← Query  </a>
        <a href='GraphCoQL.QueryConformance.html' class="btn btn-info" role='button'>Next → Query Conformance</a>
    </div>#
 *)


(** ---- *)

(* begin hide *)
Arguments is_field [Scalar].
Arguments is_inline_fragment [Scalar].

Arguments is_simple_field_selection [Scalar].
Arguments is_nested_field_selection [Scalar].

Arguments qname [Scalar].
Arguments qargs [Scalar].

Arguments subselections [Scalar].
Arguments qresponse_name [Scalar].


Arguments selection_size [Scalar].
Arguments selections_size [Scalar].
Arguments selections_size_aux [Scalar].
Arguments query_size [Scalar].


Arguments have_same_name [Scalar].
Arguments have_same_arguments [Scalar].
Arguments are_equivalent [Scalar].

Arguments filter_fields_with_response_name [Scalar].
Arguments filter_pairs_with_response_name [Scalar].

Arguments find_valid_fields_with_response_name [Scalar].
Arguments find_valid_pairs_with_response_name [Scalar].
Arguments find_fields_with_response_name [Scalar].
Arguments find_pairs_with_response_name [Scalar].
Arguments find_fragment_with_type_condition [Scalar].

Arguments merge_selection_sets [Scalar].
Arguments merge_pairs_selection_sets [Scalar].

(* end hide *)
