From Autosubst Require Export Autosubst.
From stdpp Require Import base.

From DN Require Import autosubst_preds.
From DN.DMin Require syn.

Section synty.
  Inductive tm : Type :=
    | tv : vl → tm
    | tapp : tm → tm → tm
    | tproj : vl → tm
    | tskip : tm -> tm
  with vl : Type :=
    | var_vl : var → vl
    | vnat : nat → vl
    | vabs : tm → vl
    | vpack : ty → tm → vl
  with ty : Type :=
    | TProj : vl → ty.

  Implicit Types (t: tm) (v: vl) (T: ty).

  Scheme tm_mut := Induction for tm Sort Prop
  with   vl_mut := Induction for vl Sort Prop
  with   ty_mut := Induction for ty Sort Prop.
  Combined Scheme syntax_mutind from tm_mut, vl_mut, ty_mut.

  Section transf.
    Variable (α: Type) (m_α: ty → α).
    Fixpoint m_vl (v: vl): syn.vl α :=
    match v with
    | var_vl i => syn.var_vl i
    | vnat n => syn.vnat n
    | vabs t => syn.vabs (m_tm t)
    | vpack T t => syn.vpack (m_α T) (m_tm t)
    end
    with m_tm (t: tm): syn.tm α :=
    match t with
    | tv v => syn.tv (m_vl v)
    | tskip t => syn.tskip (m_tm t)
    | tapp t1 t2 => syn.tapp (m_tm t1) (m_tm t2)
    | tproj v => syn.tproj (m_vl v)
    end.
  End transf.
End synty.
