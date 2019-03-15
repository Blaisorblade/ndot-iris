From Autosubst Require Export Autosubst.
From stdpp Require Import base.
From Coq.ssr Require Import ssreflect.
From iris.algebra Require Import base.

From DN Require Import autosubst_preds.

Inductive sort := tms | vls.

Section syn.
  Context {α: Type} {Ids_α: Ids α} {Rename_α: Rename α}.

  Inductive syn : sort → Type :=
    | tv : syn vls → syn tms
    | tapp : syn tms → syn tms → syn tms
    | tproj : syn vls → syn tms
    | tskip : syn tms -> syn tms
    | var_vl : var → syn vls
    | vnat : nat → syn vls
    | vabs : syn tms → syn vls
    | vpack : α → syn tms → syn vls.

  Notation tm := (syn tms).
  Notation vl := (syn vls).
  Implicit Types (t: tm) (v: vl) (s: sort).

  Global Instance Inh_vl : Inhabited vl := populate (vnat 0).
  Global Instance Inh_tm : Inhabited tm := populate (tv inhabitant).

  Global Instance Ids_vl : Ids vl.
  Proof. by constructor. Defined.
  Global Instance Ids_tm : Ids tm := λ _, inhabitant.

  Fixpoint syn_rename {s} (sb : var → var) (ast: syn s): syn s :=
    (* let a := (fun {s} => @syn_rename s) : ∀ {s}, Rename (syn s) in *)
    let a := syn_rename : Rename vl in
    let b := syn_rename : Rename tm in
    match ast with
    | tv v => tv (rename sb v)
    | tapp t1 t2 => tapp (rename sb t1) (rename sb t2)
    | tproj v => tproj (rename sb v)
    | tskip t => tskip (rename sb t)
    | var_vl x => var_vl (sb x)
    | vnat n => vnat n
    | vabs t => vabs (rename (upren sb) t)
    | vpack a t => vpack (rename sb a) (rename sb t)
    end.

  Global Instance Rename_syn {s}: Rename (syn s) := syn_rename.

  Context {HaS: HSubst vl α}.
  Fixpoint syn_hsubst {s} (sb : var → vl) (ast : syn s) : syn s :=
    let a := syn_hsubst : HSubst vl tm in
    let b := syn_hsubst : Subst vl in
    match ast with
    | tv v => tv (subst sb v)
    | tapp t1 t2 => tapp (hsubst sb t1) (hsubst sb t2)
    | tproj t => tproj (subst sb t)
    | tskip t => tskip (hsubst sb t)
    | var_vl x => sb x
    | vnat n => vnat n
    | vabs t => vabs (hsubst (up sb) t)
    | vpack a t => vpack (hsubst sb a) (hsubst sb t)
    end.
  Definition tm_hsubst: (var → vl) → tm → tm := syn_hsubst.
  Definition vl_subst: (var → vl) → vl → vl := syn_hsubst.
  Global Instance HSubst_tm : HSubst vl tm := tm_hsubst.
  Global Instance Subst_vl : Subst vl := vl_subst.

  Context `{!HRenameLemma vl α} `{!HCompRenameLemma vl α} `{!HCompLemma vl α} `{!HRenameCompLemma vl α} `{!HSubstIdLemma vl α}.

  (* Don't solve HSubst vl ? randomly. *)
  Hint Mode HSubst - + : typeclass_instances.

  Fixpoint syn_rename_Lemma {s} (ξ : var → var) (t: syn s) : rename ξ t = syn_hsubst (ren ξ) t.
  Proof. destruct 0; rewrite /= ?up_upren_internal; f_equal; eauto. Defined.

  Fixpoint syn_ids_Lemma {s} (t: syn s) : syn_hsubst ids t = t.
  Proof. destruct 0; rewrite /= ?up_id_internal; f_equal; eauto. Defined.

  Fixpoint syn_comp_rename_Lemma {s} (ξ : var → var) (σ : var → vl) (t : syn s) :
    syn_hsubst σ (rename ξ t) = syn_hsubst (ξ >>> σ) t.
  Proof. destruct 0; rewrite /= 1? up_comp_ren_subst; f_equal; eauto. Defined.

  Fixpoint syn_rename_comp_Lemma {s} (σ : var → vl) (ξ : var → var) (t : syn s) :
    rename ξ (syn_hsubst σ t) = syn_hsubst (σ >>> rename ξ) t.
  Proof.
    destruct 0; rewrite /= ? up_comp_subst_ren_internal; f_equal;
      eauto using syn_rename_Lemma, syn_comp_rename_Lemma.
  Defined.

  Fixpoint syn_comp_Lemma {s} (σ τ : var → vl) (t: syn s) : (syn_hsubst τ (syn_hsubst σ t)) = (syn_hsubst (σ >> τ) t).
  Proof.
    destruct 0; rewrite /= ? up_comp_internal; f_equal;
      eauto using syn_rename_comp_Lemma, syn_comp_rename_Lemma.
  Defined.

  Global Instance SubstLemmas_vl : SubstLemmas vl.
  Proof. split; eauto using syn_rename_Lemma, syn_ids_Lemma, syn_comp_Lemma. Qed.

  Global Instance HSubstLemmas_tm : HSubstLemmas vl tm.
  Proof. split; eauto using syn_ids_Lemma, syn_comp_Lemma. Qed.
End syn.

(* Make α explicit for syn and implicit for data constructors: *)
Arguments syn: clear implicits.

Reserved Notation "'vl'".

Module withSynTypes.
  Inductive ty: Type :=
  | TProj : vl → ty
  where "'vl'" := (syn ty vls).

  Notation tm := (syn ty tms).
  Implicit Types (T: ty).

  Global Instance Inh_ty : Inhabited ty := populate (TProj inhabitant).
  Global Instance Ids_ty : Ids ty := λ _, inhabitant.

  Fixpoint ty_rename (sb : var → var) T: ty :=
    let a := ty_rename : Rename ty in
    let b := syn_rename : Rename vl in
    (* let c := syn_rename : Rename tm in *)
    match T with
    | TProj v => TProj (rename sb v)
    end.
  Global Instance Rename_ty: Rename ty := ty_rename.
  Global Instance Rename_syn {s}: Rename (syn ty s) := syn_rename.

  Fixpoint ty_hsubst (sb : var → vl) T: ty :=
    let a := ty_hsubst : HSubst vl ty in
    let b := syn_hsubst : Subst vl in
    match T with
    | TProj v => TProj (subst sb v)
    end.

  Global Instance HSubst_ty: HSubst vl ty := ty_hsubst.
  Global Instance HSubst_tm : HSubst vl tm := tm_hsubst.
  Global Instance Subst_vl : Subst vl := vl_subst.

  (** To show termination, Coq must see that syn_rename_Lemma only calls
      ty_rename_Lemma recursively on subterms.
      Hence, syn_rename_Lemma can only be made opaque after this point.
   *)
  Fixpoint ty_rename_Lemma (ξ : var → var) T : rename ξ T = T.|[ren ξ].
  Proof.
    destruct 0; rewrite /= ?up_upren_internal; f_equal; eauto.
    unshelve eapply syn_rename_Lemma. exact: ty_rename_Lemma.
  Qed.
  Global Opaque syn_rename_Lemma.
  Instance ty_rename_Lemma' : HRenameLemma vl ty := ty_rename_Lemma.

  Fixpoint ty_ids_Lemma T: T.|[ids] = T.
  Proof.
    destruct 0; rewrite /= ?up_id_internal; f_equal; eauto.
    unshelve eapply syn_ids_Lemma. exact: ty_ids_Lemma.
  Qed.
  Global Opaque syn_ids_Lemma.
  Instance ty_ids_Lemma' : HSubstIdLemma vl ty := ty_ids_Lemma.

  Fixpoint ty_comp_rename_Lemma (ξ : var → var) (σ : var → vl) T :
      (rename ξ T).|[σ] = T.|[ξ >>> σ].
  Proof.
    destruct 0; rewrite /= 1? up_comp_ren_subst; f_equal; eauto.
    unshelve eapply syn_comp_rename_Lemma. exact: ty_comp_rename_Lemma.
  Qed.
  Global Opaque syn_comp_rename_Lemma.
  Instance ty_comp_rename_Lemma' : HCompRenameLemma vl ty := ty_comp_rename_Lemma.

  Fixpoint ty_rename_comp_Lemma (σ : var → vl) (ξ : var → var) T:
      rename ξ T.|[σ] = T.|[σ >>> rename ξ].
  Proof.
    destruct 0; rewrite /= ? up_comp_subst_ren_internal; f_equal => //.
    unshelve eapply syn_rename_comp_Lemma. exact: ty_rename_comp_Lemma.
  Qed.
  Global Opaque syn_rename_comp_Lemma.
  Instance ty_rename_comp_Lemma' : HRenameCompLemma vl ty := ty_rename_comp_Lemma.

  Fixpoint ty_comp_Lemma (σ τ : var → vl) T:
      T.|[σ].|[τ] = T.|[σ >> τ].
  Proof.
    destruct 0; rewrite /= ? up_comp_subst_ren_internal; f_equal => //.
    unshelve eapply syn_comp_Lemma. exact: ty_comp_Lemma.
  Qed.
  Global Opaque syn_comp_Lemma.
  Instance ty_comp_Lemma' : HCompLemma vl ty := ty_comp_Lemma.

  Global Instance HSubstLemmas_ty : HSubstLemmas vl ty.
  Proof.
    split; eauto using ty_ids_Lemma, ty_comp_Lemma.
  Qed.
End withSynTypes.

Section level0.
  Definition pu := pred ().
  Notation "'vl'" := (syn pu vls).
  Notation tm := (syn pu tms).

  Global Instance Ids_pu: Ids pu := _.
  Global Instance Rename_pu: Rename pu := _.
  Global Instance HSubst_pu: HSubst vl pu := fun sb pred ρ => pred (fun _ => tt).

  Global Instance HSubstIdLemma_pu: HSubstIdLemma vl pu.
  Proof.
    rewrite /HSubstIdLemma /rename /hsubst /Rename_pu /HSubst_pu /Rename_pred /HSubst_pred //=.
    intros; f_ext => c; f_equal; f_ext => /= x.
    (* get "eta" for unit: *)
    by destruct (c x).
  Qed.

  Global Instance HSubstLemmas_pu: HSubstLemmas vl pu.
  Proof. split => //. exact HSubstIdLemma_pu. Qed.

  Global Instance HRenameLemma_pu : HRenameLemma vl pu.
  Proof.
    rewrite /HRenameLemma.
    rewrite /rename /hsubst /Rename_pu /HSubst_pu /Rename_pred /HSubst_pred //=.
    intros; f_ext => c; f_equal; f_ext => /= x.
    by destruct (c (ξ x)).
  Qed.

  Global Instance HCompRenameLemma_pu : HCompRenameLemma vl pu.
  Proof. done. Qed.

  Global Instance HRenameCompLemma_pu : HRenameCompLemma vl pu.
  Proof. done. Qed.

  Global Instance HCompLemma_pu : HCompLemma vl pu.
  Proof. done. Qed.

  Global Instance pv_subst: Subst vl := _.
End level0.

Section fake_sv.
  Inductive fake_sv := | mksv: syn (pred unit) vls -> fake_sv.
  Notation "'vl'" := (syn (pred unit) vls).
  Notation tm := (syn (pred unit) tms).

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

  Global Instance HSubstIdLemma_pred : HSubstIdLemma fake_sv (pred fake_sv) := _.
  Global Instance HSubstLemmas_pred : HSubstLemmas fake_sv (pred fake_sv) := _.
  Global Instance HRenameLemma_pred : HRenameLemma fake_sv (pred fake_sv) := _.
  Global Instance HCompRenameLemma_pred : HCompRenameLemma fake_sv (pred fake_sv) := _.
  Global Instance HRenameCompLemma_pred : HRenameCompLemma fake_sv (pred fake_sv) := _.
  Global Instance HCompLemma_pred : HCompLemma fake_sv (pred fake_sv) := _.
End fake_sv.
