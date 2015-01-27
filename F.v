(* Author: Harley Eades
 *
 * Coq Version: 8.3pl3 
 *
 * This is the full language definition of the Simply Typed
 * Lambda-Calculus (STLC). 
 *
 * I formulate STLC using the locally-nameless binder representation. 
 * 
 * See: B. Aydemir et al. Engineering formal metatheory. 2008,
 * for more information on the locally-nameless representation. *)
(** Recently, #<a
href="http://people.cs.umass.edu/~jaltidor/">John Altidor</a># a PhD student from
the #<a href="https://www.cs.umass.edu">University of
Massachusetts</a># has been visting UIowa.  His research as of right
now is concerned with subtyping.  While his work can be applied to a
wide range of programming languages he and his advisor have been
applying their work to Java. Lately, he and I have been talking a lot
about his work on subtyping.  As I said, he has been
applying his work to Java, and one thing I find interesting is thinking
about how much of OO can be done in a dependent type theory.  His work
sparked me to read a few papers on subtyping.  

One such paper is "#<a
href="http://www.hpl.hp.com/techreports/Compaq-DEC/SRC-RR-80.pdf">An
extension of system F with subtyping</a>#" by L. Cardelli et al.  In
this paper the authors claim something I was not aware of.  They state
that church-encoded pairs in system F do not correspond to actual
categorical constructs.  Now this is not saying that they are unsound,
but it is saying that they are not products.  The authors claim this
is well-known and do not give the details.  Curiosity has lead me to
filling in the details myself.  I plan to present the details of this
claim in a three part post.  First, I will set the stage by defining
system F and church-encoded pairs.  In the second post I will present
all the categorical notions we will need on the journey. Finally,
in the third post I will present the main results.  

The entirety of this series will be presented and formalized in Coq.
The actual blog content was produced by 
#<a href="http://coq.inria.fr/distrib/V8.4/refman/Reference-Manual018.html##@default838">coqdoc</a>#
and 
#<a href="http://hackage.haskell.org/package/BlogLiterately">BlogLiterally</a>#.

System F was invented independently by both J. Girard and J. Reynolds.
It is the extension of the simply typed \(\lambda\)-calculus with
second order universal quantification.  For a more in depth look at
system F see the amazing book "#<a
href="http://www.paultaylor.eu/stable/Proofs+Types.html">Proofs and
Types</a>#."  We start by defining the syntax.  The syntax for types
and terms are defined by the following inductive definitions.
Note that we will not be able to give every detail of the formalization,
however, in the final post we will provide a link to the entire
formalization.  *)

(* begin hide *)
Require Import Arith.
Require Export Arith.
Require String. Open Scope string_scope.
Require Import List.
Require Export List.

(* Copies a hypothesis in the context naming the copy M. 
 *
 * For example if we have the following goal:
 *   H : P x |- _ 
 * copy_hyp H M produces the goal
 *   x : A, H : P x, M : P x |- _. *)
Ltac copy_hyp H M := remember H as M; 
  match goal with
    [ H' : M = H |- _] => clear H'
  end. 

(* Applies one hyothesis to another. 
 *
 * For example, if we have the following goal:
 *   H : A -> B, x : A |- _ 
 * apply_hyp (H x) H' produces the goal
 *   H : A -> B, x : A, H' : B |- _. *)
Ltac apply_hyp H M := remember H as M;
  match goal with
    [HeqM : _ |- _] => clear HeqM
  end.

(* A simple tactic that combines 
 * inversion with substitution. *)
Ltac invert_typing H := inversion H; subst.
(* end hide *)
(* Simple Types. *)
Reserved Notation "A '-->' B" (at level 35, right associativity).

Inductive typ : Set := 
  | typ_base 
  | typ_fvar   (n:nat)
  | typ_bvar   (n:nat)
  | typ_forall (A:typ)
  | typ_arrow  (A1:typ) (A2:typ).

Notation "A '-->' B" := (typ_arrow A B).

(* Terms. *)
Inductive trm : Set :=
  | trm_bvar  (n:nat)
  | trm_fvar  (n:nat)
  | trm_lam   (A:typ) (b:trm)
  | trm_Lam   (b:trm)
  | trm_app   (a:trm) (b:trm)
  | trm_tapp  (a:trm) (T:typ)
  | trm_c.

(** There are a few things that must be said before moving on.  We are
    using the locally nameless representation for binders.  See #<a
    href="http://www.cis.upenn.edu/~bcpierce/papers/binders.pdf">this</a>#
    for more information on that. System F has the types, [typ_bvar _] bound variables,
    [typ_fvar _] free variables, [typ_base] a base type, 
    [typ_forall _] the universal type, and [typ_arrow _ _] implication (or the function type). 
    Now terms are made up of bound variables [trm_bvar _], free variables [trm_fvar _], 
    \(\lambda\)-abstractions [trm_lam _ _], type abstractions [trm_Lam _],
    applications [trm_app _ _], type applications [trm_tapp _ _], and a constant
    [trm_c].

    The syntax for terms and types allow for the definition of
    non-well-formed types and terms.  An example of a non-well-formed
    type is [typ_bvar 0].  This type contains an unbound bound
    variable.  Another example is [typ_arrow (typ_bvar 0) (typ_fvar
    0)] which also contains an unbound bound variable. We can play a
    similar game with terms.  We call a type or a term well-formed iff
    all bound variables are bound. To rule out non-well-formed types
    and terms we define two predicates [lc_T _] and [lc_t _] which
    when applied to a type or a term respectively are true iff the
    input is well-formed. *)

(* Variable opening. *)
(* begin hide *)
Fixpoint open_t (k:nat) (u:trm) (t:trm) : trm  :=
  match t with
    | trm_bvar n  => 
      match (nat_compare n k) with
        | Eq => u
        | _  => t
      end
    | trm_fvar n => t
    | trm_lam  T t  => trm_lam T (open_t (S k) u t)
    | trm_Lam  t    => trm_Lam (open_t k u t)
    | trm_app t1 t2 => trm_app (open_t k u t1) (open_t k u t2)
    | trm_tapp t T  => trm_tapp (open_t k u t) T
    | trm_c         => trm_c
  end.
Fixpoint open_T (k:nat) (u:typ) (t:typ) : typ :=
  match t with
    | typ_bvar n    => match (nat_compare n k) with
                         | Eq => u
                         | _  => t
                       end
    | typ_fvar n    => t
    | typ_arrow a b => typ_arrow (open_T k u a) (open_T k u b)
    | typ_forall a  => typ_forall (open_T (S k) u a)
    | typ_base      => typ_base
  end.
Fixpoint open_tT (k:nat) (u:typ) (t:trm) : trm :=
  match t with    
    | trm_fvar n | trm_bvar n => t
    | trm_lam T t   => trm_lam (open_T k u T) (open_tT k u t)
    | trm_Lam  t    => trm_Lam (open_tT (S k) u t)
    | trm_app t1 t2 => trm_app (open_tT k u t1) (open_tT k u t2)
    | trm_c         => trm_c
    | trm_tapp t T  => trm_tapp (open_tT k u t) (open_T k u T)      
  end.
(* Variable closing. *)
Fixpoint close_t (k:nat) (x:nat) (t:trm) : trm :=
  match t with
    | trm_bvar n    => t
    | trm_fvar n    => 
      match (nat_compare n x) with
        | Eq => trm_bvar k
        | _  => t
      end
    | trm_lam  T t  => trm_lam T (close_t (S k) x t)
    | trm_Lam t     => trm_Lam (close_t k x t)
    | trm_app t1 t2 => trm_app (close_t k x t1) (close_t k x t2)
    | trm_tapp t T  => trm_tapp (close_t k x t) T
    | trm_c         => trm_c
  end.
Fixpoint close_T (k:nat) (x:nat) (t:typ) : typ :=
  match t with
    | typ_base      => t
    | typ_bvar n    => t
    | typ_fvar n    => match (nat_compare n x) with
                         | Eq => typ_bvar k
                         | _  => t
                       end
    | typ_arrow a b => typ_arrow (close_T k x a) (close_T k x b)
    | typ_forall a  => typ_forall (close_T (S k) x a)
  end.
Fixpoint close_tT (k:nat) (x:nat) (t:trm) : trm :=
  match t with
    | trm_bvar n    => t
    | trm_fvar n    => match (nat_compare n x) with
                         | Eq => trm_bvar k
                         | _  => t
                       end
    | trm_lam  T t  => 
      match T with
        | typ_fvar n => 
          match (nat_compare n k) with
            | Eq => trm_lam (typ_bvar x) (close_tT k x t)
            | _ => trm_lam T (close_tT k x t) 
          end
        | _ => trm_lam T (close_tT k x t)
      end
    | trm_Lam t     => trm_Lam (close_tT k x t)
    | trm_app t1 t2 => trm_app (close_tT k x t1) (close_tT k x t2)
    | trm_tapp t T  => 
      match T with
        | typ_fvar n => 
          match (nat_compare n k) with
            | Eq => trm_tapp (close_tT k x t) (typ_bvar x)
            | _ => trm_tapp (close_tT k x t) T
          end
        | _ => trm_tapp (close_tT k x t) T
      end
    | trm_c         => trm_c
  end.
(* end hide *) 
(* Locally-closed normal forms. *)
(* Inductive nform : trm -> Prop := *)
(*   | nf_fvar : forall x, nform (trm_fvar x) *)
(*   | nf_lam : forall T n L,  *)
(*     (forall y, ~ In y L -> nform (open_t 0 (trm_fvar y) n)) -> nform (trm_lam T n) *)
(*   | nf_app : forall h n, h_nform h -> nform n -> nform (trm_app h n) *)
(*   | nf_c : nform trm_c *)
(* with h_nform : trm -> Prop := *)
(*   | h_nf_fvar : forall x, h_nform (trm_fvar x) *)
(*   | h_nf_app : forall h n, h_nform h -> nform n -> h_nform (trm_app h n) *)
(*   | h_nf_c : h_nform trm_c. *)
(* (* Normal-form mutual induction principle. *) *)
(* Scheme nform_mut := Induction for nform Sort Prop *)
(* with h_nform_mut := Induction for h_nform Sort Prop. *)
(* (* Definition of general normal forms *) *)
(* Definition ntrm (t:trm) := (h_nform t) \/ (nform t). *)
(* Free variables. *)
(* begin hide *)
Fixpoint FV_t (e:trm) : list nat :=
  match e with
    | trm_bvar x'   => nil
    | trm_fvar x'   => (x'::nil)
    | trm_lam  T t1 => FV_t t1
    | trm_Lam  t    => FV_t t
    | trm_app t1 t2 => (FV_t t1)++(FV_t t2)
    | trm_tapp t T  => FV_t t
    | trm_c         => nil
  end.
Fixpoint FV_tT (e:trm) : list nat :=
  match e with
    | trm_bvar x'   => nil
    | trm_fvar x'   => nil
    | trm_lam  T t1 => 
      match T with
        | typ_fvar n => (FV_tT t1)++(n::nil)
        | _ => FV_tT t1
      end
    | trm_Lam  t    => FV_tT t
    | trm_app t1 t2 => (FV_tT t1)++(FV_tT t2)
    | trm_tapp t T  => 
      match T with
        | typ_fvar n => (FV_tT t)++(n::nil)
        | _ => FV_tT t
      end
    | trm_c         => nil
  end.
Fixpoint FV_T (t:typ) : list nat :=
  match t with
    | typ_base => nil
    | typ_bvar n => nil
    | typ_fvar n => (n::nil)
    | typ_forall t => FV_T t
    | typ_arrow a b => (FV_T a)++(FV_T b)
  end.
Definition free_in_t  (x:nat) (t1:trm) : Prop :=
  In x (FV_t t1).
(* end hide *)
(* Locally closed terms. *)
Inductive lc_T : typ -> Prop :=
  | lcT_base : lc_T typ_base

  | lcT_fvar : forall n, lc_T (typ_fvar n)

  | lcT_arrow : forall a b,
    lc_T a ->
    lc_T b ->
    lc_T (typ_arrow a b)

  | lcT_forall : forall t L,
    (forall x, ~(In x L) -> lc_T (open_T 0 (typ_fvar x) t)) ->
    lc_T (typ_forall t).

Inductive lc : trm -> Prop :=
  | lc_fvar : forall n, lc (trm_fvar n)

  | lc_lam : forall L t A, 
    lc_T A ->
    (forall x, ~(In x L) -> lc (open_t 0 (trm_fvar x) t)) ->
    lc (trm_lam A t)

  | lc_Lam : forall t,
    lc t ->
    lc (trm_Lam t)

  | lc_app : forall t1 t2,
    lc t1 ->
    lc t2 ->
    lc (trm_app t1 t2)

  | lc_tapp : forall T t,
    lc_T T ->
    lc t ->
    lc (trm_tapp t T)

  | lc_c : lc trm_c.
(* begin hide *)
Hint Constructors trm lc lc_T.
(* end hide *)

(** We call a type [T] or a term [t] locally closed iff [lc_T T] and
   [lc_t t] are true. Both of these definitions depend on two
   functions called [open_T (n:nat) (t:typ) (t':typ) : typ] and
   [open_t (n:nat) (t:trm) (t':trm) : trm].  The former replaces all
   bound variables [typ_bvar n] with the type [t] in [t']. The latter
   does the same with respect to terms.  There is also a third
   function we will see [open_tT (n:nat) (t:typ) (t':trm) : trm] which
   replaces all bound type variables [typ_bvar n] with the type [t] in
   the term [t']. 
   
   Next we define full $\(\beta\eta\)-reduction.  This is the
   standard definition so we do not comment on it.  We denote
   the reflexive and transitive closure of this relation
   by [t1 ~*> t2]. *)

(* head_t: Crawls a term and returns the head of that term. *)
(* begin hide *)
Fixpoint head_t (t:trm) : trm :=
  match t with
    | trm_app t1 t2 => head_t t1
    | trm_tapp t T  => head_t t
    | t => t
  end. 

(* Capture Avoiding Substitution. *)
Fixpoint subst_t (s:trm) (x:nat) (t:trm) : trm := 
 match t with
    | trm_bvar x'   => t
    | trm_fvar x'   => match (nat_compare x x') with
                         | Eq => s
                         | _  => t
                       end
    | trm_lam  T t1 => trm_lam T (subst_t s x t1)
    | trm_Lam  t    => trm_Lam (subst_t s x t)
    | trm_app t1 t2 => trm_app (subst_t s x t1) (subst_t s x t2)
    | trm_tapp t T  => trm_tapp (subst_t s x t) T
    | trm_c         => trm_c
  end.

Fixpoint subst_tT (s:typ) (x:nat) (t:trm) : trm := 
  match t with
    | trm_bvar x' | trm_fvar x'   => t
    | trm_lam  T t1 => 
      match T with
        | typ_fvar n => 
          match (nat_compare n x) with
            | Eq => trm_lam s (subst_tT s x t1)
            | _  => trm_lam T (subst_tT s x t1)
          end
        | _ => trm_lam T (subst_tT s x t1)
      end
    | trm_Lam  t    => trm_Lam (subst_tT s x t)
    | trm_app t1 t2 => trm_app (subst_tT s x t1) (subst_tT s x t2)
    | trm_tapp t T  => 
      match T with
        | typ_fvar n => 
          match (nat_compare n x) with
            | Eq => trm_tapp (subst_tT s x t) s
            | _  => trm_tapp (subst_tT s x t) T
          end
        | _ => trm_tapp (subst_tT s x t) T
      end
    | trm_c         => trm_c
  end.
(* end hide *)

(* Full Beta-Redution.*)
(* begin hide *)
Reserved Notation "t1 '~>' t2"  (at level 40).
Reserved Notation "t1 '~*>' t2" (at level 40).
(* end hide *)
(* step_t: Small step full-beta reduction. 
 *
 * The most interesting part of this definiton is how
 * we handle reduction under the lambda-abstraction.
 *
 * As far as I know this hasn't been done before.
 * All of the papers I have seen use CBV. *)
Inductive step_t : trm -> trm -> Prop :=
  | ST_lam : forall A q q' L,
    lc_T A ->
    (forall y, 
      ~ In y L -> 
      exists q'', open_t 0 (trm_fvar y) q ~> q'' /\ q' = close_t 0 y q'') -> 
    (trm_lam A q) ~> (trm_lam A q')

  | ST_Lam : forall t t',
    t ~> t' ->
    (trm_Lam t) ~> (trm_Lam t')

  | ST_beta : forall T t1 t2,
    lc (trm_lam T t1) -> 
    lc t2 ->
    (trm_app (trm_lam T t1) t2) ~> (open_t 0 t2 t1)

  | ST_eta : forall t T,
    lc t ->
    (trm_lam T (trm_app t (trm_bvar 0))) ~> t

  | ST_type : forall t T,
    lc t ->
    lc_T T ->
    (trm_tapp (trm_Lam t) T) ~> (open_tT 0 T t)

  | ST_app1 : forall t1 t1' t2,
    lc t2 ->
    t1 ~> t1' ->
    trm_app t1 t2 ~> trm_app t1' t2

  | ST_app2 : forall t1 t2 t2',
    lc t1 ->
    t2 ~> t2' ->
    trm_app t1 t2 ~> trm_app t1 t2'

  | ST_tapp : forall t t' T, 
    lc_T T ->
    t ~> t' ->
    trm_tapp t T ~> trm_tapp t' T
  where "t1 '~>' t2" := (step_t t1 t2).
(* Reflexive Transitive Closure of step_t. *)
(* begin hide *)
Inductive mstep_t : nat -> trm -> trm -> Prop :=
  | MSRefl : forall (t1:trm), 
    mstep_t 0 t1 t1
  | MSStep : forall (n:nat) (t1 t2 t3:trm),
    step_t t1 t2 ->
    mstep_t n t2 t3 ->
    mstep_t (S n) t1 t3.

(* [S]tar [Step]: t ~>* t'. *)
Inductive sstep_t (t1:trm) (t2:trm) : Prop :=
  | SStar : forall n, mstep_t n t1 t2 -> sstep_t t1 t2
where "t1 '~*>' t2" := (sstep_t t1 t2).
Hint Constructors step_t mstep_t sstep_t.
(* end hide *)

(* begin hide *)
(* This function takes in a set of 
 * names and returns a fresh name. *)
Fixpoint pick_fresh (L:list nat) : nat :=
  match L with
    | nil => 0
    | n::rest => n + (pick_fresh rest) + 1
  end.

(* (* Contexts modeled as simply a list of pairs of *)
(*  * nats and types. *) *)
Definition context : Set := list (nat*typ).
Fixpoint dom_t (G:context) : list nat :=
  match G with
    | nil => nil
    | ((x,T)::rest) => x::(dom_t rest)
  end.

(* (* Well-formed contexts; contexts without *)
(*  * duplicate variables in the domain. *) *)
Inductive Ok : context -> Prop :=
  | Ok_empty : Ok nil
  | Ok_ex : forall x T G,
    Ok G -> ~ (In x (dom_t G)) -> Ok ((x,T)::G).
Hint Constructors Ok.
(* end hide *)

(** The standard definition of typing for church-style system F goes
    something like the following;  [context] are just [List (nat*typ)]. In fact 
    all names are nats. The proposition [Ok G] where [G:context] states that
    contexts are well-formed, which means that all variables in the domain 
    of [G] are distinct. *)

(* The type checking relation. *)
(* begin hide *)
Reserved Notation "G :> t ; T" (at level 40).
(* end hide *)
Inductive type_check (G:context) : trm -> typ -> Prop :=
  | T_Var : forall T x,
    Ok G -> In (x,T) G ->
    type_check G (trm_fvar x) T

  | T_Lam : forall L t T1 T2,
    (forall (x:nat),
      ~ (In x L) ->
      type_check ((x,T1) :: G) (open_t 0 (trm_fvar x) t) T2) ->
    type_check G (trm_lam T1 t) (typ_arrow T1 T2)

  | T_TLam : forall L t T,
    (forall (x:nat),
      ~ (In x L) ->
      type_check G (open_tT 0 (typ_fvar x) t) (open_T 0 (typ_fvar x) T)) ->
    type_check G (trm_Lam t) (typ_forall T)

  | T_App : forall T1 T2 t1 t2,
    type_check G t1 (typ_arrow T1 T2) ->
    type_check G t2 T1 ->
    type_check G (trm_app t1 t2) T2

  | T_AppT : forall t T T' A,
    lc_T T' ->
    type_check G t (typ_forall T) ->
    (open_T 0 T' T) = A ->
    type_check G (trm_tapp t T') A

  | T_C :
    Ok G ->
    type_check G trm_c typ_base
where "G :> t ; T" := (type_check G t T).
(* begin hide *)
Hint Constructors type_check.
(* end hide *)

(** Finally we define \(\beta\eta\)-equality. This definition is rather long
    and tedious.  If the reader would like a clearer picture see page ?? of
    Cardelli's paper cited above.  There Cardelli gives the definition for
    \(\beta\eta\)-equality for system F with subtyping which the following
    definition is based. *)

(* begin hide *)
Reserved Notation "G :> t1 <~> t2 ; T"  (at level 40, no associativity).
(* end hide *)
Inductive trm_eq (G:context) : trm -> trm -> typ -> Prop :=
  | Eq_var :  forall n T, 
    G :> (trm_fvar n) ; T -> 
    G :> (trm_fvar n) <~> (trm_fvar n) ; T

  | Eq_lam : forall L t1 t2 T1 T2,
    (forall (x:nat),
      ~ (In x L) ->
      ((x,T1) :: G) :> (open_t 0 (trm_fvar x) t1) <~> (open_t 0 (trm_fvar x) t2) ; T2) ->
    G :> (trm_lam T1 t1) <~> (trm_lam T1 t2) ; (typ_arrow T1 T2)

  | Eq_tlam : forall L t1 t2 T,
    (forall (n:nat),
      ~ In n L ->
    G :> (open_tT 0 (typ_fvar n) t1) <~> (open_tT 0 (typ_fvar n) t2) ; (open_T 0 (typ_fvar n) T)) ->
    G :> (trm_Lam t1) <~> (trm_Lam t2) ; (typ_forall T)

  | Eq_app : forall a a' b b' A B,
    G :> a <~> a' ; typ_arrow A B ->
    G :> b <~> b' ; A ->
    G :> (trm_app a b) <~> (trm_app a' b') ; B
  
  | Eq_tapp : forall a a' A B C,
    lc_T B ->
    G :> a <~> a' ; typ_forall A ->
    C = (open_T 0 B A) ->
    G :> (trm_tapp a B) <~> (trm_tapp a' B) ; C

  | Eq_beta : forall L a a' b b' c A B,
    (forall (x:nat),
      ~ (In x L) ->
      ((x,A) :: G) :> (open_t 0 (trm_fvar x) b) <~> (open_t 0 (trm_fvar x) b') ; B) ->
    G :> a <~> a' ; A ->
    c = (open_t 0 a' b') -> 
    G :> (trm_app (trm_lam A b) a) <~>  c ; B 

  | Eq_tbeta : forall L a b c A B C,
    lc_T B ->
    (forall (n:nat),
      ~ In n L ->
    G :> (open_tT 0 (typ_fvar n) a) <~> (open_tT 0 (typ_fvar n) b) ; (open_T 0 (typ_fvar n) A)) ->
    c = open_tT 0 B b -> 
    C = open_T 0 B A ->
    G :> (trm_tapp (trm_Lam a) B) <~>  c ; C

  | Eq_eta : forall b b' A B,
    G :> b <~> b' ; typ_arrow A B ->
    G :> (trm_lam A (trm_app b (trm_bvar 0))) <~> b' ; typ_arrow A B
    
  | Eq_teta : forall b b' A,
    G :> b <~> b' ; typ_forall A ->
    G :> (trm_Lam (trm_tapp b (typ_fvar 0))) <~> b' ; typ_forall A

  | Eq_sym : forall t1 t2 T, 
    G :> t2 <~> t1 ; T -> 
    G :> t1 <~> t2 ; T 

  | Eq_trans : forall t1 t2 t3 T,  
    G :> t1 <~> t3 ; T ->  
    G :> t3 <~> t2 ; T -> G :> t1 <~> t2 ; T 
where "G :> t1 <~> t2 ; T" := (trm_eq G t1 t2 T).
(* begin hide *)
Hint Constructors trm_eq.
(* end hide *)

(** This concludes the definition of system F with \(\beta\eta\)-equality.  
    The next step is to define the church encoding of pairs. Following the definition
    we state several correctness properties certifying that we have the correct 
    definition. *)