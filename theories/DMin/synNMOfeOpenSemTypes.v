(**
   Build syntax containing semantic types, try 2, with *open* semantic types.
   They support renaming, and hopefully we should manage to get substitution.
 *)

From Autosubst Require Export Autosubst.
From stdpp Require Import base.
From Coq.ssr Require Import ssreflect.
From iris.algebra Require Import base ofe.
From iris.base_logic Require Export iprop.
From iris.proofmode Require Export tactics.
Import uPred.

From DN Require Import autosubst_preds DMin.synNonMutual DMin.synNMOfe.

Canonical Structure varO: ofeT := leibnizO var.
Section openSemanticSyntax.
  Context {Σ : gFunctors}. (* Look ma', no requirements! *)
  (* Here, we put the later around the whole function, as an experiment.
     This *)
  Definition semVls: oFunctor := (synCF (▶ ((varO -n> ∙) -n> ∙ -n> iPropO Σ)) vls)%OF.
  Import cofe_solver.

  Definition semVls_result:
    solution semVls := solver.result _.
  Definition iPreVl: ofeT := semVls_result.

  Definition preD := (varO -n> iPreVl) -n> iPreVl -n> iPropO Σ.
  Definition iSyn s : ofeT := synO (laterO preD) s.

  Notation "'vl'" := (iSyn vls).
  Notation "'tm'" := (iSyn tms).
  Notation D := ((varO -n> vl) -n> vl -n> iPropO Σ).

  (*
  Inspired from code in
  https://gitlab.mpi-sws.org/iris/iris/blob/82e7e2ef749e4f25af0fa14d27d01d624bb9cbd6/theories/base_logic/lib/iprop.v#L133-150
  *)
  Definition iSyn_unfold : vl -n> iPreVl :=
    ofe_iso_1 semVls_result.
  Definition iSyn_fold : iPreVl -n> vl := ofe_iso_2 semVls_result.
  Lemma iSyn_fold_unfold (v : vl) : iSyn_fold (iSyn_unfold v) ≡ v.
  Proof. apply ofe_iso_21. Qed.
  Lemma iSyn_unfold_fold (v : iPreVl) : iSyn_unfold (iSyn_fold v) ≡ v.
  Proof. apply ofe_iso_12. Qed.
  (* Semantic types! *)

  (* Check that values contain terms. *)
  Definition _test (v: vl) (t: tm) : iProp Σ :=
    (∃ Φ t, v ≡ vpack Φ t)%I.

  Program Definition unpack: laterO preD -n> D :=
    λne '(Next Φ) ρ v, (▷ Φ (λne x, (iSyn_unfold (ρ x))) (iSyn_unfold v))%I.
  (* Body copy-pasted from somewhere in Iris (but had simpl, not cbn). *)
  Ltac solve_proper_cbn := solve_proper_core ltac:(fun _ => first [ intros ?; progress simpl | f_equiv ]).
  Solve All Obligations with solve_contractive || solve_proper_cbn.

  (** Note that here we get an extra later when we *pack*
      predicates (so that we can pass them to vpack). *)
  Program Definition pack: D -n> laterO preD :=
    λne Φ, Next (λne ρ v, Φ (λne x, iSyn_fold (ρ x)) (iSyn_fold v))%I.
  Solve All Obligations with solve_contractive || solve_proper_cbn.

  Lemma unpack_pack Φ ρ v: unpack (pack Φ) ρ v ≡ (▷ Φ ρ v)%I.
  Proof.
    (* rewrite /= iSyn_fold_unfold. (repeat f_equiv) => ? /=. *)
    (* exact: iSyn_fold_unfold. *)
    solve_proper_core
      ltac:(fun _ => first [ rewrite iSyn_fold_unfold | intros ?; progress simpl | f_equiv ]).
  Qed.
  Program Definition later_preD : preD -n> preD := (λne Φ ρ v, ▷ Φ ρ v)%I.
  Solve All Obligations with solve_proper.

  Lemma pack_unpack (Φ: preD):
    pack (unpack (Next Φ)) ≡ Next (later_preD Φ).
  Proof.
    solve_proper_core
      ltac:(fun _ => first [ rewrite iSyn_unfold_fold | intros ?; progress simpl | f_equiv ]).
  Qed.

  Instance Inhabited_preD: Inhabited preD := populate (λne _ _, False)%I.
  Instance Ids_pred: Ids preD := λ _, inhabitant.

  Program Definition lift_varfun {A: ofeT} (f: var → A): varO -n> A :=
    λne x, f x.
  Solve All Obligations with solve_proper_cbn.

  Global Program Instance Rename_preD : Rename preD :=
    λ r preD, λne ρ, preD (lift_varfun (r >>> ρ)).
  Solve All Obligations with solve_proper_cbn.

  (* This will probably need some Iris fixpoint.
    And we need to lift subst to the category of OFEs. *)
  Fail Global Program Instance HSubst_pred : HSubst vl preD :=
    λ sb preD, λne ρ, preD (lift_varfun (sb >>> iSyn_unfold >>> subst ρ)).

  (* XXX First I thought of lifting Autosubst functions to
     OFEs, then realized then lift_varfun
     allows avoiding that.
     But not so for substitution. So maybe these will be needed?
     *)
  (* ofe-variant of funcomp/>>>. *)
  Program Definition ofe_compose {A B C} (f: A -n> B) (g: B -n> C): A -n> C :=
    λne x, g (f x).
  Solve All Obligations with solve_proper_cbn.
  Program Definition lift_ren {A} (r: var -> var) :=
    λne (ρ: varO -n> A),
    ofe_compose (lift_varfun r) ρ.
  Solve All Obligations with solve_proper_cbn.
  (* ofe-variant of scomp/>>. *)
  (* Program Definition ofe_scomp {A: ofeT} {H: Subst A}
    (sb: var → A) (ρ: varO -n> A) := *)
End openSemanticSyntax.
