(** * Smallstep: Small-step Operational Semantics *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.

(* ################################################################# *)
(** * Relations *)

(** We will be working with several different single-step relations,
    so it is helpful to generalize a bit and state a few definitions
    and theorems about relations in general.  (The optional chapter
    [Rel.v] develops some of these ideas in a bit more detail; it may
    be useful if the treatment here is too dense.)

    A _binary relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

Definition relation (X : Type) := X -> X -> Prop.

(** Our main examples of such relations in this chapter will be
    the single-step reduction relation, [-->], and its multi-step
    variant, [-->*] (defined below), but there are many other
    examples -- e.g., the "equals," "less than," "less than or equal
    to," and "is the square of" relations on numbers, and the "prefix
    of" relation on lists and strings. *)

(** One simple property of the [-->] relation is that, like the
    big-step evaluation relation for Imp, it is _deterministic_.

    _Theorem_: For each [t], there is at most one [t'] such that [t]
    steps to [t'] ([t --> t'] is provable). *)

(** _Proof sketch_: We show that if [x] steps to both [y1] and
    [y2], then [y1] and [y2] are equal, by induction on a derivation
    of [step x y1].  There are several cases to consider, depending on
    the last rule used in this derivation and the last rule in the
    given derivation of [step x y2].

      - If both are [ST_PlusConstConst], the result is immediate.

      - The cases when both derivations end with [ST_Plus1] or
        [ST_Plus2] follow by the induction hypothesis.

      - It cannot happen that one is [ST_PlusConstConst] and the other
        is [ST_Plus1] or [ST_Plus2], since this would imply that [x]
        has the form [P t1 t2] where both [t1] and [t2] are
        constants (by [ST_PlusConstConst]) _and_ one of [t1] or [t2]
        has the form [P _].

      - Similarly, it cannot happen that one is [ST_Plus1] and the
        other is [ST_Plus2], since this would imply that [x] has the
        form [P t1 t2] where [t1] has both the form [P t11 t12] and the
        form [C n]. [] *)

(** Formally: *)

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.


(* ################################################################# *)
(** * Multi-Step Reduction *)

(** We've been working so far with the _single-step reduction_
    relation [-->], which formalizes the individual steps of an
    abstract machine for executing programs.

    We can use the same machine to reduce programs to completion -- to
    find out what final result they yield.  This can be formalized as
    follows:

    - First, we define a _multi-step reduction relation_ [-->*], which
      relates terms [t] and [t'] if [t] can reach [t'] by any number
      (including zero) of single reduction steps.

    - Then we define a "result" of a term [t] as a normal form that
      [t] can reach by multi-step reduction. *)

(** Since we'll want to reuse the idea of multi-step reduction many
    times, let's take a little extra trouble and define it
    generically.

    Given a relation [R] (which will be [-->] for present purposes),
    we define a relation [multi R], called the _multi-step closure
    of [R]_ as follows. *)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

(** (In the [Rel] chapter of _Logical Foundations_ and
    the Coq standard library, this relation is called
    [clos_refl_trans_1n].  We give it a shorter name here for the sake
    of readability.) *)

(** The effect of this definition is that [multi R] relates two
    elements [x] and [y] if

       - [x = y], or
       - [R x y], or
       - there is some nonempty sequence [z1], [z2], ..., [zn] such that

           R x z1
           R z1 z2
           ...
           R zn y.

    Thus, if [R] describes a single-step of computation, then [z1] ... [zn] 
    is the sequence of intermediate steps of computation between [x] and 
    [y]. *)

(** We write [-->*] for the [multi step] relation on terms. *)

(** The relation [multi R] has several crucial properties.

    First, it is obviously _reflexive_ (that is, [forall x, multi R x
    x]).  In the case of the [-->*] (i.e., [multi step]) relation, the
    intuition is that a term can execute to itself by taking zero
    steps of execution. *)

(** Second, it contains [R] -- that is, single-step executions are a
    particular case of multi-step executions.  (It is this fact that
    justifies the word "closure" in the term "multi-step closure of
    [R].") *)

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

(** Third, [multi R] is _transitive_. *)

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.
