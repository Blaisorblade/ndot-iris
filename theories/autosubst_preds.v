From Coq.ssr Require Import ssreflect.
From stdpp Require Import base.
From Autosubst Require Import Autosubst.

(**
    Goal: we want to be able to parameterize a datatype over an unspecified sort, and define
    Autosubst 1 operations.

    Substituting one sort through all the other sorts is not a usecase that Autosubst 1
    was designed for, but it works. However, we end up needing a few extra lemmas about rename.

    Here's the ones I needed in my proofs. *)
Section classes.
  Context (vl α: Type)
    `{!Ids vl} `{!Rename vl} `{!Subst vl}
    `{!Ids α} `{!Rename α} `{!HSubst vl α}.

  Class HRenameLemma :=
    α_rename_Lemma :
      ∀ (ξ : var → var) (a : α), rename ξ a = a.|[ren ξ].

  Class HSubstIdLemma :=
    α_hsubst_id_Lemma :
      ∀ (a : α), a.|[ids] = a.

  Class HCompRenameLemma :=
    α_comp_rename_Lemma :
      ∀ (ξ : var → var) (σ : var → vl) (a: α),
      (rename ξ a).|[σ] = a.|[ξ >>> σ].

  Class HRenameCompLemma :=
    α_rename_comp_Lemma :
      ∀ (σ : var → vl) (ξ : var → var) (t : α),
      rename ξ t.|[σ] = t.|[σ >>> rename ξ].

  (** These two lemmas are part of HSubstLemmas, but we must split them to allow mutual
      recursion among the base syntax and the plug-in sort α. *)
  Class HCompLemma :=
    α_comp_Lemma :
      ∀ (σ τ : var → vl) (t : α), t.|[σ].|[τ] = t.|[σ >> τ].
End classes.

Section composition.
  Context (vl: Type) {Rename_vl: Rename vl} `{!Ids vl, !Subst vl, !SubstLemmas vl}.

  Definition pred := (var -> vl) → vl → Prop.

  Global Instance Rename_pred : Rename pred := fun r pred ρ => pred (r >>> ρ).

  Global Instance HSubst_pred : HSubst vl pred := fun sb pred ρ => pred (sb >> ρ).

  Global Instance Inh_pred : Inhabited pred := populate (fun _ _ => False).
  Global Instance Ids_pred : Ids pred := λ _, inhabitant.

  Global Instance HRenameLemma_pred : HRenameLemma vl pred.
  Proof.
    rewrite /HRenameLemma.
    rewrite /hsubst /HSubst_pred [@rename _ Rename_pred]/rename /Rename_pred /=.
    intros; f_ext => ?; by asimpl.
  Qed.

  Global Instance HSubstIdLemma_pred : HSubstIdLemma vl pred.
  Proof.
    rewrite /HSubstIdLemma /hsubst /HSubst_pred //= => *; f_ext => ?. by asimpl.
  Qed.

  Global Instance HCompRenameLemma_pred : HCompRenameLemma vl pred.
  Proof. done. Qed.

  Global Instance HRenameCompLemma_pred : HRenameCompLemma vl pred.
  Proof.
    rewrite /HRenameCompLemma.
    rewrite /hsubst /HSubst_pred [@rename _ Rename_pred]/rename /Rename_pred /=.
    intros; f_ext => ?; by asimpl.
  Qed.

  Global Instance HCompLemma_pred : HCompLemma vl pred.
  Proof.
    rewrite /HCompLemma /hsubst /HSubst_pred /rename /Rename_pred //=;
    intros; f_ext => ?; by asimpl.
  Qed.

  Global Instance HSubstLemmas_pred : HSubstLemmas vl pred.
  Proof.
    split => //. exact HSubstIdLemma_pred. exact HCompLemma_pred.
  Qed.
End composition.
