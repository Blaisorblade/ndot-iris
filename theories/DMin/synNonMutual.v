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

Arguments syn: clear implicits.

Module withTypes.
  Inductive ty: Type :=
  | TProj : syn ty vls → ty.

  Notation tm := (syn ty tms).
  Notation vl := (syn ty vls).
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

  Fixpoint ty_ids_Lemma T: T.|[ids] = T.
  Proof.
    destruct 0; rewrite /= ?up_id_internal; f_equal; eauto.
    unshelve eapply syn_ids_Lemma. exact: ty_ids_Lemma.
  Qed.
  Global Opaque syn_ids_Lemma.
  Instance ty_ids_Lemma' : HSubstIdLemma vl ty := ty_ids_Lemma.

  Global Instance HSubstLemmas_ty : HSubstLemmas vl ty.
  Proof.
    split; eauto using ty_ids_Lemma, ty_comp_Lemma.
  Qed.
End withTypes.
