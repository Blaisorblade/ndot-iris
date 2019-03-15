(** AUTHORS:
    The Autosubst instantiation code derives from code from Amin Timany,
    used in a parallel project with me.
    Paolo. *)

From Autosubst Require Export Autosubst.
From stdpp Require Import base.
From Coq.ssr Require Import ssreflect.
From iris.algebra Require Import base.

From DN Require Import autosubst_preds.

Section syn.
  Context {α: Type} {Ids_α: Ids α} {Rename_α: Rename α}.

  Inductive tm : Type :=
    | tv : vl → tm
    | tapp : tm → tm → tm
    | tproj : vl → tm
    | tskip : tm -> tm
  with vl : Type :=
    | var_vl : var → vl
    | vnat : nat → vl
    | vabs : tm → vl
    | vpack : α → tm → vl.

  Implicit Types (t: tm) (v: vl).

  Scheme tm_mut := Induction for tm Sort Prop
  with   vl_mut := Induction for vl Sort Prop.
  Combined Scheme syntax_mutind from tm_mut, vl_mut.

  Global Instance Inh_vl : Inhabited vl := populate (vnat 0).
  Global Instance Inh_tm : Inhabited tm := populate (tv inhabitant).

  Global Instance Ids_vl : Ids vl.
  Proof. by constructor. Defined.
  Global Instance Ids_tm : Ids tm := λ _, inhabitant.

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
    (* let b := tm_rename : Rename tm in *)
    match v with
    | var_vl x => var_vl (sb x)
    | vnat n => vnat n
    | vabs t => vabs (tm_rename (upren sb) t)
    | vpack a t => vpack (rename sb a) (tm_rename sb t)
    end.

  Global Instance Rename_vl : Rename vl := vl_rename.

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
    match v with
    | var_vl x => sb x
    | vnat n => vnat n
    | vabs t => vabs (hsubst (up sb) t)
    | vpack a t => vpack (hsubst sb a) (hsubst sb t)
    end.

  Global Instance HSubst_tm : HSubst vl tm := tm_hsubst.
  Global Instance Subst_vl : Subst vl := vl_subst.

  Context `{!HRenameLemma vl α} `{!HCompRenameLemma vl α} `{!HCompLemma vl α} `{!HRenameCompLemma vl α} `{!HSubstIdLemma vl α}.

  (* Don't solve HSubst vl ? randomly. *)
  Hint Mode HSubst - + : typeclass_instances.

  Lemma tm_rename_Lemma (ξ : var → var) t : tm_rename ξ t = t.|[ren ξ]
  with
  vl_rename_Lemma (ξ : var → var) v  : rename ξ v = v.[ren ξ].
  Proof.
    all: destruct 0; rewrite /= ?up_upren_internal; by f_equal.
  Qed.

  Lemma tm_ids_Lemma t : t.|[ids] = t
  with
  vl_ids_Lemma v : v.[ids] = v.
  Proof.
    all: destruct 0; rewrite /= ?up_id_internal; by f_equal.
  Qed.

  Lemma vl_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (v : vl) :
    (rename ξ v).[σ] = v.[ξ >>> σ]
  with
  tm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (t : tm) :
    (tm_rename ξ t).|[σ] = t.|[ξ >>> σ].
  Proof.
    all: destruct 0; rewrite /= 1? up_comp_ren_subst; by f_equal.
  Qed.

  Lemma vl_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (v : vl) :
    rename ξ v.[σ] = v.[σ >>> rename ξ]
  with
  tm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (t : tm) :
    tm_rename ξ t.|[σ] = t.|[σ >>> rename ξ].
  Proof.
    all: destruct 0; rewrite /= ? up_comp_subst_ren_internal; f_equal => //;
      eauto using vl_rename_Lemma, vl_comp_rename_Lemma.
  Qed.

  Lemma vl_comp_Lemma (σ τ : var → vl) (v : vl) : v.[σ].[τ] = v.[σ >> τ]
  with
  tm_comp_Lemma (σ τ : var → vl) (t : tm) : t.|[σ].|[τ] = t.|[σ >> τ].
  Proof.
    all: destruct 0; rewrite /= ? up_comp_internal; f_equal => //;
      eauto using vl_rename_comp_Lemma, vl_comp_rename_Lemma.
  Qed.

  Global Instance SubstLemmas_vl : SubstLemmas vl.
  Proof.
    split; auto using vl_rename_Lemma, vl_ids_Lemma, vl_comp_Lemma.
  Qed.

  Global Instance HSubstLemmas_tm : HSubstLemmas vl tm.
  Proof.
    split; auto using tm_ids_Lemma, tm_comp_Lemma.
  Qed.
End syn.

Arguments tm: clear implicits.
Arguments vl: clear implicits.

(* sv = sem values *)
(* As expected, we can't instantiate alpha with predicates over values;
  we must use OFEs for this. *)
Fail Inductive sv := | mksv: vl (pred sv) -> sv.

(** That would work out if we stratified things using OFEs.
    Here's a test of how the rest of the infrastructure works: we use unit as
    the approximation of vl.

    Surprisingly, this instantiation is harder than it should be using OFEs.
    Since we're not constructing the limit, we need both instances for `pred unit`
    (where unit is vl_0) and instances for `pred fake_sv`.
  *)

Section level0.
  Definition pu := pred ().

  Global Instance Ids_pu: Ids pu := _.
  Global Instance Rename_pu: Rename pu := _.
  Global Instance HSubst_pu: HSubst (vl pu) pu := λ sb pr ρ, pr (fun _ => tt).

  Global Instance HSubstIdLemma_pu: HSubstIdLemma (vl pu) pu.
  Proof.
    rewrite /HSubstIdLemma /rename /hsubst /Rename_pu /HSubst_pu /Rename_pred /HSubst_pred //=.
    intros; f_ext => c; f_equal; f_ext => /= x.
    (* get "eta" for unit: *)
    by destruct (c x).
  Qed.

  Global Instance HSubstLemmas_pu: HSubstLemmas (vl pu) pu.
  Proof. split => //. exact HSubstIdLemma_pu. Qed.

  Global Instance HRenameLemma_pu : HRenameLemma (vl pu) pu.
  Proof.
    rewrite /HRenameLemma /rename /hsubst /Rename_pu /HSubst_pu /Rename_pred /HSubst_pred //=.
    intros; f_ext => c; f_equal; f_ext => /= x.
    by destruct (c (ξ x)).
  Qed.

  Global Instance HCompRenameLemma_pu : HCompRenameLemma (vl pu) pu.
  Proof. done. Qed.

  Global Instance HRenameCompLemma_pu : HRenameCompLemma (vl pu) pu.
  Proof. done. Qed.

  Global Instance HCompLemma_pu : HCompLemma (vl pu) pu.
  Proof. done. Qed.

  Global Instance pv_subst: Subst (vl pu) := _.
End level0.

Section fake_sv.
  Inductive fake_sv := | mksv: vl (pred unit) -> fake_sv.
  Implicit Types (sv: fake_sv).

  Definition unsv '(mksv v) := v.

  Lemma sv_unsv sv: mksv (unsv sv) = sv.
  Proof. by destruct sv. Qed.

  Global Instance Ids_fake_sv: Ids fake_sv := ids >>> mksv.

  Lemma ids_unsv_ids: ids >>> unsv = ids.
  Proof. done. Qed.
  Hint Rewrite ids_unsv_ids sv_unsv: autosubst.

  Global Instance Rename_fake_sv: Rename fake_sv := fun r sv => mksv (rename r (unsv sv)).
  Global Instance Subst_fake_sv: Subst fake_sv := fun s sv => mksv (subst (s >>> unsv) (unsv sv)).

  Global Instance HSubst_psv: HSubst fake_sv (pred fake_sv) := _.

  Global Instance SubstLemmas_fake_sv: SubstLemmas fake_sv.
  Proof.
    (* Unwrap fake values and exploit SubstLemmas_vl through asimpl. *)
    split; intros; try match goal with
      x: fake_sv |- _ => destruct x
    end; rewrite /Rename_fake_sv /Subst_fake_sv /=; by asimpl.
  Qed.

  Global Instance HSubstLemmas_pred : HSubstLemmas fake_sv (pred fake_sv) := _.
  Global Instance HRenameLemma_pred : HRenameLemma fake_sv (pred fake_sv) := _.

  Global Instance HCompRenameLemma_pred : HCompRenameLemma fake_sv (pred fake_sv) := _.

  Global Instance HRenameCompLemma_pred : HRenameCompLemma fake_sv (pred fake_sv) := _.

  Global Instance HCompLemma_pred : HCompLemma fake_sv (pred fake_sv) := _.
End fake_sv.
