(**
   Build syntax containing semantic types, try 1.
   This only works for *closed* semantic types, with no support for
   substitution, but works otherwise pretty well.
 *)

From Autosubst Require Export Autosubst.
From stdpp Require Import base.
From Coq.ssr Require Import ssreflect.
From iris.algebra Require Import base ofe.
From iris.base_logic Require Export iprop.
From iris.proofmode Require Export tactics.
Import uPred.

From DN Require Import autosubst_preds DMin.synNonMutual DMin.synNMOfe.

Section semanticSyntax.
  Context {Σ : gFunctors}. (* Look ma', no requirements! *)
  (* XXX wonder if lifting up the later would make
     proofs easier. *)
  Definition semVls: cFunctor := (synCF ((▶ ∙) -n> iProp Σ) vls)%CF.
  Import cofe_solver.

  Definition semVls_result:
    solution semVls := solver.result _.
  Definition iPreVl: ofeT := semVls_result.

  Definition preD := laterC iPreVl -n> iProp Σ.
  Definition iSyn s : ofeT := synC preD s.

  Notation "'vl'" := (iSyn vls).
  Notation "'tm'" := (iSyn tms).
  Notation D := (vl -n> iProp Σ).

  (*
  Inspired from code in
  https://gitlab.mpi-sws.org/iris/iris/blob/82e7e2ef749e4f25af0fa14d27d01d624bb9cbd6/theories/base_logic/lib/iprop.v#L133-150
  *)
  Definition iSyn_unfold : vl -n> iPreVl :=
    solution_fold semVls_result.
  Definition iSyn_fold : iPreVl -n> vl := solution_unfold _.
  Lemma iSyn_fold_unfold (v : vl) : iSyn_fold (iSyn_unfold v) ≡ v.
  Proof. apply solution_unfold_fold. Qed.
  Lemma iSyn_unfold_fold (v : iPreVl) : iSyn_unfold (iSyn_fold v) ≡ v.
  Proof. apply solution_fold_unfold. Qed.
  (* Semantic types! *)

  (* Check that values contain terms. *)
  Definition _test (v: vl) (t: tm) : iProp Σ :=
    (∃ Φ t, v ≡ vpack Φ t)%I.

  Program Definition unpack: preD -n> D :=
    λne Φ v, Φ (Next (iSyn_unfold v)).
  Solve All Obligations with solve_proper.

  (** Note that here we get an extra later when we *pack*
      predicates (so that we can pass them to vpack). *)
  Program Definition pack: D -n> preD :=
    λne Φ '(Next w), (▷ Φ (iSyn_fold w))%I.
  Solve All Obligations with solve_contractive || solve_proper.

  Lemma unpack_pack Φ v: unpack (pack Φ) v ≡ (▷ Φ v)%I.
  Proof. by rewrite /= iSyn_fold_unfold. Qed.
  Lemma pack_unpack Φ v: pack (unpack Φ) v ≡ (▷ Φ v)%I.
  Proof. by rewrite /= iSyn_unfold_fold. Qed.

  Instance Inhabited_preD: Inhabited preD := populate (λne v, False)%I.
  Instance Ids_pred: Ids preD := λ _, inhabitant.
  (* XXX Argh, this completely doesn't work. We
     need to follow autosubst_preds — and that's what we
     had on the whiteboard. *)
  (* Global Instance Rename_preD : Rename preD := λ r preD, λne '(Next v), preD (Next (rename r v)).
  ρ, pred (r >>> ρ). *)


  (* First semantic type! *)
  Program Definition proj2: vl -n> D :=
    λne v w, (∃ Φ t, v ≡ vpack Φ t ∧ □ unpack Φ w)%I.
  Solve All Obligations with solve_proper.

  (** As a sanity check, let's try to port the not-quite-Russell paradox
      to this setting. This is *not* a paradox, nor does it construct one
      assuming axioms that we don't have.
      Instead, this shows what happens in place of a paradox if we try to
      encode (a variant of) Russell's paradox. *)
  Notation "¬ P" := (□ (P -∗ False))%I.
  Program Definition selfApp : D := λne v, proj2 v v.
  Solve All Obligations with solve_proper.
  Instance: Persistent (selfApp v) := _.

  Program Definition russellP : D := λne v, ¬ selfApp v.
  Solve All Obligations with solve_proper.
  Instance: Persistent (russellP v) := _.

  Definition russellV : vl := vpack (pack russellP) inhabitant.

  (** ofe_flip and ofe_apply are defined to pass to f_equiv. *)
  Program Definition ofe_flip {A B C: ofeT}:
    (A -n> B -n> C) -n> B -n> A -n> C :=
    λne f b a, f a b.
  Solve All Obligations with solve_proper_core ltac:(fun _ => first [ intros ?; progress simpl | f_equiv ]).

  Program Definition ofe_apply {A B: ofeT}: (A -n> B) -n> A -n> B :=
    λne f a, f a.
  Solve All Obligations with solve_proper.

  Lemma unpack_lemma w φ φ' t t':
    (vpack (pack φ) t ≡ vpack φ' t' -∗
    unpack φ' w ≡ ▷ φ w)%I: iProp Σ.
  Proof.
    rewrite -unpack_pack. iIntros "Heq".
    (* unshelve iApply (f_equiv (λne P, unpack P w)); [> solve_proper | apply _ | idtac ]. *)
    iApply (f_equiv (ofe_flip ofe_apply w)). iApply f_equiv.
    iApply (f_equiv (vpack_1_inv inhabitant) (vpack φ' t') (vpack (pack φ) t)).
    by iRewrite "Heq".
  Qed.

  (* Taken from another  *)
  Lemma later_not_selfApp: selfApp russellV -∗ ▷ False.
  Proof.
    iIntros "#Hvav"; iDestruct "Hvav" as (φ t) "[Heq Hvav]".
    iRewrite (unpack_lemma russellV with "Heq") in "Hvav".
    iApply "Hvav". iNext; iExists _, _; iSplit => //.
    by rewrite unpack_pack.
  Qed.

  Lemma selfAppEquiv: ((▷ ¬ selfApp russellV) ∗-∗ selfApp russellV)%I.
  Proof.
    iSplit.
    - iIntros "#HnotVAV"; iExists _, _; iSplit => //.
      rewrite unpack_pack. by iApply "HnotVAV".
    - iIntros "#Hvav".
      iPoseProof (later_not_selfApp with "Hvav") as "#HF".
      by iNext.
  Qed.

  (** uauEquiv would be absurd without later: a proposition
      can't be equivalent to its negation. *)
  Lemma taut0 (P: Prop): ¬ (¬ P ↔ P). Proof. tauto. Qed.
  (** But with later, there's no paradox — we get instead ¬¬P. *)
  Lemma irisTaut (P : iProp Σ):
    □((▷ ¬P) ∗-∗ P) -∗ ¬¬P.
  Proof. iIntros "#Eq !> #NP". iApply "NP". by iApply "Eq". Qed.

  Lemma notNotSelfAppRussellV: (¬¬ selfApp russellV)%I.
  Proof.
    iIntros "!> #notVAV". iApply (irisTaut (selfApp russellV)) => //.
    by iApply selfAppEquiv.
  Qed.

  Definition notRussellV: (¬ russellP russellV)%I := notNotSelfAppRussellV.

  (* XXX TODO: ltyping.v pairs predictes with their proofs
     of persistence, then builds a COFE on such predicates. *)
  Record sem_ty := {
    sem_ty_car :> vl -n> iProp Σ;
    sem_ty_persistent v : Persistent (sem_ty_car v);
  }.

End semanticSyntax.
