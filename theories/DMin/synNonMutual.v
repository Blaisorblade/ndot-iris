From Autosubst Require Export Autosubst.
From stdpp Require Import base.
From Coq.ssr Require Import ssreflect.
From iris.algebra Require Import base.

From DN Require Import autosubst_preds.

Local Hint Resolve α_rename_Lemma α_comp_rename_Lemma α_rename_comp_Lemma α_comp_Lemma.

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

  Definition tm := syn tms.
  Definition vl := syn vls.
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

  Context `{!HSubstLemmas vl α} `{!HRenameLemmas vl α}.

  (* Don't solve HSubst vl ? randomly. *)
  Hint Mode HSubst - + : typeclass_instances.

  Require Import Program.Equality.
  Fixpoint syn_rename_Lemma {s} (ξ : var → var) (t: syn s) : rename ξ t = syn_hsubst (ren ξ) t.
  Proof. destruct t; rewrite /= ?up_upren_internal; f_equal; eauto. Qed.

  Fixpoint syn_ids_Lemma {s} (t: syn s) : syn_hsubst ids t = t.
  Proof.
    destruct t; rewrite /= ?up_id_internal; f_equal; eauto; by asimpl.
  Qed.

  Fixpoint syn_comp_rename_Lemma {s} (ξ : var → var) (σ : var → vl) (t : syn s) :
    syn_hsubst σ (rename ξ t) = syn_hsubst (ξ >>> σ) t.
  Proof.
    destruct t; rewrite /= 1? up_comp_ren_subst; f_equal; eauto.
  Qed.

  Fixpoint syn_rename_comp_Lemma {s} (σ : var → vl) (ξ : var → var) (t : syn s) :
    rename ξ (syn_hsubst σ t) = syn_hsubst (σ >>> rename ξ) t.
  Proof.
    destruct t; rewrite /= ? up_comp_subst_ren_internal; f_equal => //;
      eauto using syn_rename_Lemma, syn_comp_rename_Lemma.
  Qed.

  Fixpoint syn_comp_Lemma {s} (σ τ : var → vl) (t: syn s) : (syn_hsubst τ (syn_hsubst σ t)) = (syn_hsubst (σ >> τ) t).
  Proof.
    destruct 0; rewrite /= ? up_comp_internal; f_equal;
      eauto using syn_rename_comp_Lemma, syn_comp_rename_Lemma.
  Qed.

  Global Instance SubstLemmas_vl : SubstLemmas vl.
  Proof.
    split; eauto using syn_rename_Lemma, syn_ids_Lemma, syn_comp_Lemma.
  Qed.

  Global Instance HSubstLemmas_tm : HSubstLemmas vl tm.
  Proof.
    split; eauto using syn_ids_Lemma, syn_comp_Lemma.
  Qed.
End syn.

Arguments syn: clear implicits.
Inductive ty: Type :=
| TProj : syn ty vls → ty.
