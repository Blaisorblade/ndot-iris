From Autosubst Require Export Autosubst.
From stdpp Require Import base.
From Coq.ssr Require Import ssreflect.
From iris.algebra Require Import base.

(* Class SynExt vl α := {
  r :> Rename α;
  r :> Rename α;
}. *)

Section syn.
  Context (α: Type).

  Inductive tm : Type :=
    | tv : vl → tm
    | tapp : tm → tm → tm
    | tproj : vl → tm
    | tskip : tm -> tm
  with vl : Type :=
    | var_vl : var → vl
    | vnat : nat → vl
    | vabs : tm → vl
    | vpack : α → vls → tm → vl
  with vls: Type :=
    | vnil : vls
    | vcons : vl → vls → vls.

  Implicit Types (t: tm) (v: vl) (vs: vls).

  Scheme tm_mut := Induction for tm Sort Prop
  with   vl_mut := Induction for vl Sort Prop
  with   vls_mut := Induction for vls Sort Prop.
  Combined Scheme syntax_mutind from tm_mut, vl_mut, vls_mut.

  Instance Inh_vl : Inhabited vl := populate (vnat 0).
  Instance Inh_tm : Inhabited tm := populate (tv inhabitant).
  Instance Inh_vls : Inhabited vls := populate (vnil).

  Instance Ids_vl : Ids vl.
  Proof. by constructor. Defined.
  Instance Ids_tm : Ids tm := λ _, inhabitant.
  Instance Ids_vls : Ids vls := λ _, inhabitant.

  Fixpoint tm_rename (sb : var → var) t : tm :=
    let a := vl_rename : Rename vl in
    (* let b := tm_rename : Rename tm in *)
    match t with
    | tv v => tv (rename sb v)
    | tapp t1 t2 => tapp (tm_rename sb t1) (tm_rename sb t2)
    | tproj v => tproj (rename sb v)
    | tskip t => tskip (tm_rename sb t)
    end
  with
  vl_rename (sb : var → var) v : vl :=
    let a := vl_rename : Rename vl in
    let b := vls_rename : Rename vls in
    (* let c := tm_rename : Rename tm in *)
    match v with
    | var_vl x => var_vl (sb x)
    | vnat n => vnat n
    | vabs t => vabs (tm_rename (upren sb) t)
    | vpack α vs t => vpack α (rename sb vs) (tm_rename sb t)
    end
  with
  vls_rename (sb : var → var) vs : vls :=
    let a := vl_rename : Rename vl in
    let b := vls_rename : Rename vls in
    match vs with
    | vnil => vnil
    | vcons v vs => vcons (rename sb v) (rename sb vs)
    end.

  Instance Rename_vl : Rename vl := vl_rename.

  Context {HaS: HSubst vl α}.

  Fixpoint tm_hsubst (sb : var → vl) (e : tm) : tm :=
    let a := tm_hsubst : HSubst vl tm in
    let b := vl_subst : Subst vl in
    match e with
    | tv v => tv (subst sb v)
    | tapp t1 t2 => tapp (hsubst sb t1) (hsubst sb t2)
    | tproj t => tproj (subst sb t)
    | tskip t => tskip (hsubst sb t)
    end
  with
  vl_subst (sb : var → vl) (v : vl) : vl :=
    let a := tm_hsubst : HSubst vl tm in
    let b := vl_subst : Subst vl in
    let c := vls_hsubst : HSubst vl vls in
    match v with
    | var_vl x => sb x
    | vnat n => vnat n
    | vabs t => vabs (hsubst (up sb) t)
    | vpack α vs t => vpack α (hsubst sb vs) (hsubst sb t)
    end
  with
  vls_hsubst (sb : var → vl) vs : vls :=
    let a := tm_hsubst : HSubst vl tm in
    let b := vl_subst : Subst vl in
    let c := vls_hsubst : HSubst vl vls in
    match vs with
    | vnil => vnil
    | vcons v vs => vcons (subst sb v) (hsubst sb vs)
    end.

  Instance HSubst_tm : HSubst vl tm := tm_hsubst.
  Instance Subst_vl : Subst vl := vl_subst.
  Instance HSubst_vls : HSubst vl vls := vls_hsubst.

  (* Don't solve HSubst vl ? randomly. *)
  Hint Mode HSubst - + : typeclass_instances.
  Context {α_eq_dec : EqDecision α}.

  Lemma
  tm_eq_dec (t1 t2 : tm) : Decision (t1 = t2)
  with
  vl_eq_dec (v1 v2 : vl) : Decision (v1 = v2)
  with
  vls_eq_dec (vs1 vs2 : vls) : Decision (vs1 = vs2).
  Proof.
    all: rewrite /Decision; decide equality;
      try (apply vl_eq_dec || apply tm_eq_dec || apply vls_eq_dec ||
           apply nat_eq_dec || apply α_eq_dec); eauto.
  Qed.
  Instance tm_eq_dec' : EqDecision tm := tm_eq_dec.
  Instance vl_eq_dec' : EqDecision vl := vl_eq_dec.
  Instance vls_eq_dec' : EqDecision vls := vls_eq_dec.

  Local Ltac finish_lists l x := idtac.

  (* Hypothesis α_rename_Lemma: ∀ (ξ : var → var) (a : α), rename ξ a = a.|[ren ξ]. *)

  Lemma tm_rename_Lemma (ξ : var → var) t : tm_rename ξ t = t.|[ren ξ]
  with
  vl_rename_Lemma (ξ : var → var) v  : rename ξ v = v.[ren ξ]
  with
  vls_rename_Lemma (ξ : var → var) vs : vls_rename ξ vs = vs.|[ren ξ].
  Proof.
    all: destruct 0; rewrite /= ?up_upren_internal; by f_equal.
  Qed.

  Lemma tm_ids_Lemma t : t.|[ids] = t
  with
  vl_ids_Lemma v : v.[ids] = v
  with
  vls_ids_Lemma vs : vs.|[ids] = vs.
  Proof.
    all: destruct 0; rewrite /= ?up_id_internal; by f_equal.
  Qed.

  Lemma vl_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (v : vl) :
    (rename ξ v).[σ] = v.[ξ >>> σ]
  with
  tm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (t : tm) :
    (tm_rename ξ t).|[σ] = t.|[ξ >>> σ]
  with
  vls_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (vs : vls) :
    (vls_rename ξ vs).|[σ] = vs.|[ξ >>> σ].
  Proof.
    all: destruct 0; rewrite /= 1? up_comp_ren_subst; by f_equal.
  Qed.

  Lemma vl_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (v : vl) :
    rename ξ v.[σ] = v.[σ >>> rename ξ]
  with
  tm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (t : tm) :
    tm_rename ξ t.|[σ] = t.|[σ >>> rename ξ]
  with
  vls_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (vs : vls) :
    vls_rename ξ vs.|[σ] = vs.|[σ >>> rename ξ].
  Proof.
    all: destruct 0; rewrite /= ? up_comp_subst_ren_internal; f_equal => //;
      auto using vl_rename_Lemma, vl_comp_rename_Lemma.
  Qed.

  Lemma vl_comp_Lemma (σ τ : var → vl) (v : vl) : v.[σ].[τ] = v.[σ >> τ]
  with
  tm_comp_Lemma (σ τ : var → vl) (t : tm) : t.|[σ].|[τ] = t.|[σ >> τ]
  with
  vls_comp_Lemma (σ τ : var → vl) (vs : vls) : vs.|[σ].|[τ] = vs.|[σ >> τ].
  Proof.
    all: destruct 0; rewrite /= ? up_comp_internal; f_equal;
      auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma.
  Qed.

  Instance SubstLemmas_vl : SubstLemmas vl.
  Proof.
    split; auto using vl_rename_Lemma, vl_ids_Lemma, vl_comp_Lemma.
  Qed.

  Instance HSubstLemmas_tm : HSubstLemmas vl tm.
  Proof.
    split; auto using tm_ids_Lemma, tm_comp_Lemma.
  Qed.

  Instance HSubstLemmas_vls : HSubstLemmas vl vls.
  Proof.
    split; auto using vls_ids_Lemma, vls_comp_Lemma.
  Qed.

End syn.
