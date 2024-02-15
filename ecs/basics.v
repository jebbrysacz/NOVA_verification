(* This file consists of some of the basics properties of elliptic curves. *)

Require Import Field.
Require Import Arith.

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
Fixpoint find_inv (b a n : nat) : nat. Admitted.
(*  match ((ff_mul a b n) ?= 1) with
  | Eq => b
  | _ => find_inv (b-1) a n
  end.
*)
Definition ff_mul_inv (a n : nat) : nat := find_inv a a n


Definition Fin_Field (size : nat): 
  field_theory 0 1 (ff_add size) (ff_mult size) (ff_sub size)