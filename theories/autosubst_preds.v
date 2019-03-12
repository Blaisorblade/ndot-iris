From Coq.ssr Require Import ssreflect.
From stdpp Require Import base.
From Autosubst Require Import Autosubst.

(**
    Goal: we want to be able to parameterize a datatype over an unspecified sort, and define
    Autosubst 1 operations.

    Substituting one sort through all the other sorts is not a usecase that Autosubst 1
    was designed for, but it works. However, we end up needing a few extra lemmas about rename.

    Here's the ones I needed in my proofs. *)
Class HRenameLemmas (vl α: Type)
  `{!Ids α} `{!Rename α}
  `{!Ids vl} `{!Rename vl} `{!Subst vl} `{!HSubst vl α} := {
  mixin_α_rename_Lemma :>
    ∀ (ξ : var → var) (a : α), rename ξ a = a.|[ren ξ];
  mixin_α_comp_rename_Lemma :>
    ∀ (ξ : var → var) (σ : var → vl) (a: α),
    (rename ξ a).|[σ] = a.|[ξ >>> σ];
  mixin_α_rename_comp_Lemma :>
    ∀ (σ : var → vl) (ξ : var → var) (t : α),
    rename ξ t.|[σ] = t.|[σ >>> rename ξ];
  mixin_α_comp_Lemma :>
    ∀ (σ τ : var → vl) (t : α), t.|[σ].|[τ] = t.|[σ >> τ]
}.

Section HRenameLemmas.
  Context `{RL: HRenameLemmas vl α}.

  Lemma α_rename_Lemma: ∀ (ξ : var → var) (a : α), rename ξ a = a.|[ren ξ].
  Proof. by destruct RL. Qed.

  Lemma α_comp_rename_Lemma: ∀ (ξ : var → var) (σ : var → vl) (a: α),
    (rename ξ a).|[σ] = a.|[ξ >>> σ].
  Proof. by destruct RL. Qed.

  Lemma α_rename_comp_Lemma: ∀ (σ : var → vl) (ξ : var → var) (t : α),
    rename ξ t.|[σ] = t.|[σ >>> rename ξ].
  Proof. by destruct RL. Qed.

  Lemma α_comp_Lemma: ∀ (σ τ : var → vl) (t : α), t.|[σ].|[τ] = t.|[σ >> τ].
  Proof. by destruct RL. Qed.
End HRenameLemmas.

Section composition.
  Context (vl: Type) {Rename_vl: Rename vl} `{!Ids vl, !Subst vl, !SubstLemmas vl}.

  Definition pred := (var -> vl) → vl → Prop.

  Global Instance Rename_pred : Rename pred := fun r pred ρ => pred (r >>> ρ).

  Global Instance HSubst_pred : HSubst vl pred := fun sb pred ρ => pred (sb >> ρ).

  Global Instance Inh_pred : Inhabited pred := populate (fun _ _ => False).
  Global Instance Ids_pred : Ids pred := λ _, inhabitant.

  Global Instance HSubstLemmas_pred : HSubstLemmas vl pred.
  Proof.
    split; rewrite /hsubst /HSubst_pred => //= *; f_ext => ?; by asimpl.
  Qed.

  Global Instance HRenameLemmas_pred : HRenameLemmas vl pred.
  Proof.
    split; rewrite /rename /hsubst /Rename_pred /HSubst_pred //=; intros; f_ext => ?;
      fold (@rename _ Rename_vl); by asimpl.
  Qed.
End composition.
