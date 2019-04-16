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
Require Import Program.Equality.
Unset Program Cases.

Canonical Structure varC: ofeT := leibnizC var.
Section openSemanticSyntax.
  Context {Σ : gFunctors}. (* Look ma', no requirements! *)
  (* Here, we put the later around the whole function, as an experiment.
     This *)
  Definition semVls: cFunctor := (synCF ((var -c> ▶ ∙) -n> ▶ ∙ -n> iProp Σ) vls)%CF.
  Import cofe_solver.

  Definition semVls_result:
    solution semVls := solver.result _.
  Definition iPreVl: ofeT := semVls_result.

  Definition preD := (var -c> laterC iPreVl) -n> laterC iPreVl -n> iProp Σ.
  Definition iSyn s : ofeT := synC preD s.

  Notation "'vl'" := (iSyn vls).
  Notation "'tm'" := (iSyn tms).
  Notation D := ((var -c> vl) -n> vl -n> iProp Σ).

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

  Program Definition iSyn_unfold' : vl -n> laterC iPreVl :=
    CofeMor Next ◎ iSyn_unfold.
  Program Definition iSyn_fold' : laterC iPreVl → vl :=
    iSyn_fold ∘ later_car.
  Global Arguments iSyn_unfold': simpl never.
  Global Arguments iSyn_fold': simpl never.
  Instance iSyn_fold'_anti_contractive n :
    Proper (dist n ==> dist_later n) iSyn_fold'.
  Proof. move :n =>[|n]; rewrite /iSyn_fold' => *??? //=. by f_equiv. Qed.
  Lemma iSyn_fold_unfold' (v : vl) : iSyn_fold' (iSyn_unfold' v) ≡ v.
  Proof. apply solution_unfold_fold. Qed.
  Lemma iSyn_unfold_fold' (v : laterC iPreVl) : iSyn_unfold' (iSyn_fold' v) ≡ v.
  Proof. apply solution_fold_unfold. Qed.

  (* Semantic types! *)

  (* Check that values contain terms. *)
  Definition _test (v: vl) (t: tm) : iProp Σ :=
    (∃ Φ t, v ≡ vpack Φ t)%I.

  Program Definition unpack: preD -n> D :=
    λne Φ ρ v, Φ (iSyn_unfold' ∘ ρ) (iSyn_unfold' v).
  (* Body copy-pasted from somewhere in Iris (but had simpl, not cbn). *)
  Ltac solve_proper_cbn := solve_proper_core ltac:(fun _ => first [ intros ?; progress simpl | f_equiv ]).
  Ltac solve_contractive_cbn := solve_proper_core ltac:(fun _ => first [ intros ?; progress simpl | f_contractive | f_equiv ]).
  Ltac solve_proper_ho_core tac :=
  solve [repeat intro; cbn; repeat tac (); cbn in *;
  repeat match goal with H : _ ≡{_}≡ _|- _ => apply H end].
  Ltac solve_proper_ho := solve_proper_ho_core ltac:(fun _ => first [intros ?; progress simpl | f_equiv]).
  Ltac solve_contractive_ho := solve_proper_ho_core ltac:(fun _ => first [intros ?; progress simpl | f_contractive | f_equiv]).

  Solve All Obligations with solve_proper_ho.

  (** Note that here we get an extra later when we *pack*
      predicates (so that we can pass them to vpack). *)
  Program Definition pack: D -n> preD :=
    λne Φ ρ v, (▷ Φ (λne x, iSyn_fold' (ρ x)) (iSyn_fold' v))%I.
  Solve All Obligations with rewrite /iSyn_fold'; (solve_contractive || solve_proper_cbn || solve_contractive_ho || solve_proper_ho).
  Next Obligation.
    rewrite /iSyn_fold' =>*?? H[?]/=.
    f_contractive; repeat f_equiv; move=>?/=.
    f_equiv. apply H.
  Qed.
  Solve All Obligations with rewrite /iSyn_fold'; solve_contractive || solve_proper_cbn || solve_contractive_ho || solve_proper_ho.

  Program Definition later_pred {A B: ofeT}:
    (A -n> B -n> iProp Σ) -n> (A -n> B -n> iProp Σ) :=
    (λne Φ ρ v, ▷ Φ ρ v)%I.
  Solve All Obligations with solve_proper.

  Lemma unpack_pack Φ: unpack (pack Φ) ≡ later_pred Φ.
  Proof.
    move=>??/=; rewrite iSyn_fold_unfold'.
    (repeat f_equiv) =>?/=. by rewrite /= iSyn_fold_unfold'.

    (* solve_proper_core
      ltac:(fun _ => first [ f_equiv | move=>?; progress cbn | rewrite iSyn_fold_unfold']). *)
    (* solve_proper_core
      ltac:(fun _ => first [ rewrite /= ?iSyn_fold_unfold ?iSyn_fold_unfold' | intros ?; progress simpl | f_equiv ]). *)
  Qed.

  Lemma pack_unpack Φ: pack (unpack Φ) ≡ later_pred Φ.
  Proof.
    solve_proper_core
      ltac:(fun _ => first [ rewrite iSyn_unfold_fold | intros ?; progress simpl | f_equiv ]).
  Qed.

  (* Autosubst instances. *)

  Instance Inhabited_preD: Inhabited preD := populate (λne _ _, False)%I.
  Instance Ids_pred: Ids preD := λ _, inhabitant.

  Definition lift_varfun {A: ofeT} (f: var → A): var -c> A := f.
  Program Definition rename_preD: (var → var) -c> preD -n> preD :=
    λ r, λne preD ρ, preD (r >>> ρ).
  Solve All Obligations with solve_proper_ho.

  (* Renaming is relatively easy: *)
  Global Instance Rename_preD : Rename preD := rename_preD.
  Global Instance Rename_iSyn {s}: Rename (iSyn s) := _.

  Global Instance syn_rename_ne {s: sort} r:
    NonExpansive (@syn_rename preD Rename_preD s r).
  Proof.
    intros ** t t' Ht. move: r t' Ht.
    induction t; intros; inversion Ht; simplify_eq; cbn; f_equiv;
      try by [|apply IHt | apply IHt1 | apply IHt2 | f_equiv].
  Qed.

  Global Instance subst_prevl `{!HSubst vl preD} : Subst iPreVl :=
    λ sb v, iSyn_unfold (subst (iSyn_fold ∘ sb) (iSyn_fold v)).
  Global Instance subst_lprevl `{!HSubst vl preD} : Subst (laterC iPreVl) :=
    λ sb v, iSyn_unfold' (subst (iSyn_fold' ∘ sb) (iSyn_fold' v)).

  Global Instance hsubst_lpreD `{!HSubst vl preD} : HSubst vl (laterC preD) :=
    λ sb '(Next preD), Next (hsubst sb preD).

  Global Instance subst_vl_preD_ne
    (HSubstPred0 : (var -c> vl) -n> preD -n> preD):
    let HSubstPred: HSubst vl preD := (λ sb p, HSubstPred0 sb p)
    in NonExpansive2 (λ (s: var -c> vl), @syn_hsubst preD _ HSubstPred vls s).
  Proof.
    move => /= n s1 s2 Heqs x.
    induction x => y Heq; inversion Heq; simplify_eq; cbn.
    all: match goal with a: var, b: var, H: ?a ≡{ _ }≡ ?b |- _ => by [inversion H; apply Heqs] end || f_equiv.
    all: rewrite /hsubst; try by [|apply IHx|apply IHx1|apply IHx2].
    - apply IHx => //.
      (* Show that up is non-expansive: *)
      rewrite // /up; move => [|i] //=. by eapply syn_rename_ne, Heqs.
      (* Maybe lift that to a separate version: *)
      (* Global Program Instance syn_up_ne: NonExpansive (@up vl _ _). *)
    - (* repeat f_equiv. *)
      f_equiv => //. by apply HSubstPred0.
  Qed.

  Program Definition hsubst_preD (rec: (var -c> vl) -n> preD -n> preD): (var -c> vl) -n> preD -n> preD :=
    let hsubst_preD' : HSubst vl preD := λ s t, rec s t in
    λne sb preD ρ, preD (sb >>> iSyn_unfold' >>> subst ρ).
  Next Obligation. intros **???.
    f_equiv=>?. rewrite /= /subst_lprevl.
    f_equiv. rewrite /subst /Subst_vl /vl_subst /=.
    apply subst_vl_preD_ne => // x1.
    specialize (H x1).
    (* apply iSyn_fold'_anti_contractive. *)
    rewrite /iSyn_fold' /=.
    f_equiv.
    destruct (x x1), (y x1).
    case: n H => [|n] /= H.
    - hnf in H; admit.
    - hnf in H; cbn in H.
    admit.
  Admitted.
(*
  (* This will probably need some Iris fixpoint.
    And we need to lift subst to the category of OFEs. *)
  Program Definition hsubst_preD (rec: (var -c> vl) → preD → preD): (var -c> vl) → preD → preD :=
    let hsubst_preD' : HSubst vl preD := rec in
    λ sb preD, λne ρ, preD (sb >>> iSyn_unfold >>> @subst _ subst_prevl ρ).
  Next Obligation. intros **???. f_equiv. rewrite /lift_varfun => ? /=. f_equiv. Admitted. *)

End openSemanticSyntax.
