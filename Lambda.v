Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
Require Import Smallstep.
Require Import Maps.

Module Lambda.

(* ################################################################# *)
(** * Syntax *)

(** We next formalize the syntax of the Lambda Calculus. *)

(* ================================================================= *)
(** ** Expressions *)

Inductive exp : Type :=
  | var : string -> exp
  | abs : string -> exp -> exp
  | app : exp -> exp -> exp.

(* ################################################################# *)
(** * Operational Semantics *)

(* ================================================================= *)
(** ** Values *)

Inductive value : exp -> Prop :=
  (*| v_var : forall s,
      value (var s)*)
  | v_abs : forall x e,
      value (abs x e).

Hint Constructors value.

(* ================================================================= *)
(** ** Substitution *)

(** Here is the definition, informally...

       [x:=s]x       = s
       [x:=s]y       = y                     if x <> y
       [x:=s](\x. e) = \x. e
       [x:=s](\y. e) = \y. [x:=s]e           if x <> y
       [x:=s](e1 e2) = ([x:=s]e1) ([x:=s]e2)
*)

(** ... and formally: *)

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : exp) (t : exp) : exp :=
  match t with
  | var x' =>
     if eqb_string x x' then s else t
  | abs x' e =>
     abs x' (if eqb_string x x' then e else ([x:=s] e))
  | app e1 e2 =>
     app ([x:=s] e1) ([x:=s] e2)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* ================================================================= *)
(** ** Reduction *)

Reserved Notation "e1 '-->' e2" (at level 40).

Inductive step : exp -> exp -> Prop :=
  | ST_AppAbs : forall x e v,
      value v ->
      (app (abs x e) v) --> [x:=v]e
  | ST_App1 : forall e1 e1' e2,
      e1 --> e1' ->
      app e1 e2 --> app e1' e2
  | ST_App2 : forall v1 e2 e2',
      value v1 ->
      e2 --> e2' ->
      app v1 e2 --> app v1 e2'

where "e1 '-->' e2" := (step e1 e2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "e1 '-->*' e2" := (multistep e1 e2) (at level 40).

(* ################################################################# *)
(** * Syntax *)

(** We next formalize the syntax of the Lambda Calculus for K. *)

(* ================================================================= *)
(** ** Expressions *)

Inductive expK : Type :=
  | expL : exp -> expK
  | cl   : string -> expK -> partial_map expK -> expK.

(* ================================================================= *)
(** ** Values *)

Inductive valueK : expK -> Prop :=
  | v_cl : forall s e m, valueK (cl s e m).

Hint Constructors valueK.

(* ================================================================= *)
(** ** Contexts *)

Inductive ctxt : Type :=
  | hole : ctxt
  | app1 : ctxt -> expK -> ctxt
  | app2 : expK -> ctxt -> ctxt.

Inductive K : Type :=
  | K_exp : expK -> K
  | K_ctx : ctxt -> K
  | K_map : partial_map expK -> K
  | K_dot : K
  | K_arr : K -> K -> K.

(* ================================================================= *)
(** ** Configurations *)

Inductive cfg : Type :=
  | pair : K -> partial_map expK -> cfg.

(* ################################################################# *)
(** * Operational Semantics *)

Reserved Notation "c1 '==>' c2" (at level 40).

Inductive stepK : cfg -> cfg -> Prop :=
  | KST_App1 : forall e1 e2 rho k,
      pair (K_arr (K_exp (expL (app e1 e2))) k) rho ==>
      pair (K_arr (K_exp (expL e1))
                  (K_arr (K_ctx (app1 hole (expL e2))) k)) rho
  | KST_App2 : forall x e1 e2 rho1 rho2 k,
      pair (K_arr (K_exp (cl x e1 rho1))
                  (K_arr (K_ctx (app1 hole (expL e2))) k)) rho2 ==>
      pair (K_arr (K_exp (expL e2))
                  (K_arr (K_ctx (app2 (cl x e1 rho1) hole)) k)) rho2
  | KST_Cl1 : forall x e rho k,
      pair (K_arr (K_exp (expL (abs x e))) k) rho ==>
      pair (K_arr (K_exp (cl x (expL e) rho)) k) rho
  | KST_Cl2 : forall x1 x2 e1 e2 rho1 rho2 rho3 k,
      pair (K_arr (K_exp (cl x1 e1 rho1))
                  (K_arr (K_ctx (app2 (cl x2 e2 rho2) hole)) k)) rho3 ==>
      pair (K_arr (K_exp e2)
                  (K_arr (K_map rho3) k)) (update rho2 x2 (cl x1 e1 rho1))
  | KST_Env : forall x e rho rho' rho'' k,
      pair (K_arr (K_exp (cl x e rho'')) (K_arr (K_map rho) k)) rho' ==>
      pair (K_arr (K_exp (cl x e rho'')) k) rho

where "c1 '==>' c2" := (stepK c1 c2).

Notation multistepK := (multi stepK).
Notation "k1 '==>*' k2" := (multistepK k1 k2) (at level 40).

Lemma kdot_id : forall k1 k2,
  K_arr k1 k2 = K_arr (K_arr k1 K_dot) k2.
Admitted.

Theorem step_equiv : forall (e1 : exp) (e2 : exp) x k,
  e1 -->* (abs x e2) <->
  pair (K_arr (K_exp (expL e1)) k) empty ==>* pair (K_arr (K_exp (cl x (expL e2) empty)) k) empty.
Proof.
  split; intros. generalize dependent k. generalize dependent x. generalize dependent e2.
  induction e1; intros.
  inversion H; inversion H0.
  inversion H; subst. eapply multi_step. constructor. apply multi_refl.
  inversion H; inversion H0.
  
  eapply multi_step. constructor. eapply multi_trans. apply IHe1_1. admit.
  eapply multi_step. constructor. eapply multi_trans. apply IHe1_2. admit.

  Admitted.

End Lambda.
