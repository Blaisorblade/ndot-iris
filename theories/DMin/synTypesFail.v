(* Strict positivity gets in the way: *)
From Autosubst Require Export Autosubst.
From stdpp Require Import base.
From Coq.ssr Require Import ssreflect.

Module fail.
Inductive tm (α: Type) : Type :=
  | tv : vl α → tm α
with vl (α: Type) : Type :=
  | vabs : tm α → vl α
  (* | vpack : α → tm → vl *)
  .
(* Non-strictly positive?! *)
Fail Inductive ty: Type :=
| TProj : vl ty → ty.
(* The command has indeed failed with message:
Non strictly positive occurrence of "ty" in "vl ty → ty". *)

End fail.

Inductive tm {α: Type} : Type :=
  | tv : vl → tm
  | tapp : tm → tm → tm
  | tproj : vl → tm
  | tskip : tm -> tm
with vl {α: Type} : Type :=
  | var_vl : var → vl
  | vnat : nat → vl
  | vabs : tm → vl
  | vpack : α → tm → vl
with ty {α: Type}: Type :=
  | TProj : vl → ty.

Arguments tm: clear implicits.
Arguments vl: clear implicits.
Arguments ty: clear implicits.
Fail Inductive loop :=
  | mkL : ty loop → loop.
