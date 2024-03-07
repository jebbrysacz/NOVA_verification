(* This file consists of some of the basics properties of elliptic curves. *)

Require Import Field.
Require Import Arith.
Require Import Coq.Program.Wf.

(* We first want to build some definitions of finite fields on naturals*)

Section Finite_Fields.

Variable F : Type.

Definition ff_add (a n m : nat) : nat :=
  (n + m) mod a.

Definition ff_add_inv (a n : nat) : nat := a - n.

Definition ff_sub (a n m : nat) : nat :=
  match (n ?= m) with
  | Gt | Eq => n - m
  | Lt => a - (m - n)
  end.

Definition ff_mul (a n m : nat) : nat :=
  (n * m) mod a.

(* naive implementation of the Euclidean algorithm to find mult inv *)
Program Fixpoint find_inv (b a n : nat) {measure b} : nat :=
  match ((ff_mul a b n) ?= 1), b with
  | Eq, _ => b
  | _, 0 => 0
  | _, _ => find_inv (b-1) a n
  end.
Next Obligation.
  Admitted.
Next Obligation.
  split. 
  - intros. unfold not. intros. destruct H. discriminate H0.
  - intros. unfold not. intros. destruct H. discriminate H.
Qed.
Next Obligation.
  split.
  - intros. unfold not. intros. destruct H. discriminate H0.
  - intros. unfold not. intros. destruct H. discriminate H.
Qed.

Definition ff_mul_inv (a n : nat) : nat := find_inv a a n.

Definition ff_div (a n m : nat) : nat := ff_mul a n (ff_mul_inv a m).

Definition ff_opp (a n : nat) : nat := a - n.

Theorem ff_opp_th : forall (a n : nat), ff_add a n (ff_opp a n) = 0.
Proof.
  intros. unfold ff_add. unfold ff_opp. Search "-". Admitted. (* destruct (n ?= n) eqn:E. 
  - apply Nat.sub_diag.
  - rewrite Nat.compare_refl in E. discriminate E.
  - apply Nat.sub_diag.
Qed. *)

Definition ff_eq (n m : nat) : Prop := 
  match (n ?= m) with
  | Eq => True
  | _ => False
  end.

Definition fin_field (size : nat):
  field_theory 0 1 (ff_add size) (ff_mul size) (ff_sub size) (ff_add_inv size)
                   (ff_div size) (ff_mul_inv size) (ff_eq).

(* Finite Fields Defined!!! *)














