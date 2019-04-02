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
  Definition semVls: cFunctor := (synCF (▶ ((varC -n> ∙) -n> ∙ -n> iProp Σ)) vls)%CF.
  Import cofe_solver.

  Definition semVls_result:
    solution semVls := solver.result _.
  Definition iPreVl: ofeT := semVls_result.

  Definition preD := (varC -n> iPreVl) -n> iPreVl -n> iProp Σ.
  Definition iSyn s : ofeT := synC (laterC preD) s.

  Notation "'vl'" := (iSyn vls).
  Notation "'tm'" := (iSyn tms).
  Notation D := ((varC -n> vl) -n> vl -n> iProp Σ).

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

  Program Definition unpack: laterC preD -n> D :=
    λne '(Next Φ) ρ v, (▷ Φ (λne x, (iSyn_unfold (ρ x))) (iSyn_unfold v))%I.
  (* Body copy-pasted from somewhere in Iris (but had simpl, not cbn). *)
  Ltac solve_proper_cbn := solve_proper_core ltac:(fun _ => first [ intros ?; progress simpl | f_equiv ]).
  Solve All Obligations with solve_contractive || solve_proper_cbn.

  (** Note that here we get an extra later when we *pack*
      predicates (so that we can pass them to vpack). *)
  Program Definition pack: D -n> laterC preD :=
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

  Program Definition lift_varfun {A: ofeT} (f: var → A): varC -n> A :=
    λne x, f x.
  Solve All Obligations with solve_proper_cbn.

  Global Program Instance Rename_preD : Rename preD :=
    λ r preD, λne ρ, preD (lift_varfun (r >>> ρ)).
  Solve All Obligations with solve_proper_cbn.

  Global Instance Rename_lpreD : Rename (laterC preD) :=
    λ r '(Next preD), Next (rename r preD).
  Global Instance Rename_iSyn {s}: Rename (iSyn s) := _.

  Global Instance hsubst_lpreD `{!HSubst vl preD} : HSubst vl (laterC preD) :=
    λ sb '(Next preD), Next (hsubst sb preD).
  Global Instance proper_hslpreD ρ `{!HSubst vl preD}
    `{proper_hspreD: ∀ ρ, NonExpansive (λ v: preD, hsubst ρ v)}:
    NonExpansive (λ v: laterC preD, hsubst ρ v).
  Proof.
    move => n [x] [y] H /=. rewrite /hsubst_lpreD.
    f_contractive. by eapply proper_hspreD.
  Qed.

  Global Instance subst_prevl `{!HSubst vl preD} : Subst iPreVl :=
    λ sb v, iSyn_unfold (subst (λ x, (iSyn_fold (sb x))) (iSyn_fold v)).

  (* This will probably need some Iris fixpoint.
    And we need to lift subst to the category of OFEs. *)
  Program Definition hsubst_preD (rec: (var → vl) → preD → preD): (var → vl) → preD → preD :=
    let hsubst_preD' : HSubst vl preD := rec in
    λ sb preD, λne ρ, preD (lift_varfun (sb >>> iSyn_unfold >>> @subst _ subst_prevl ρ)).
  Next Obligation. intros **???. f_equiv. rewrite /lift_varfun => ? /=. f_equiv. Admitted.

  Global Instance discr_fun_equiv `{OfeDiscrete A} `{Equiv B} : Equiv (A → B) :=
    λ f g, ∀ x, f x ≡ g x.
  Global Instance discr_fun_equivalence `{OfeDiscrete A} `{Equiv B} `{!Equivalence (≡@{B})} :
    Equivalence (≡@{A → B}).
  Proof.
    split => //=; hnf.
    - by intros f ?.
    - by intros f g ? x.
    - by intros f g h ?? x; trans (g x).
  Qed.
  Global Instance rens_equiv `{Equiv A} : Equiv (var → A) := discr_fun_equiv.
  Global Instance rens_equivalence `{Equiv A} `{!Equivalence (≡@{A})} : Equivalence (≡@{var → A}) := _.
  Canonical Structure renameC := discreteC (var → var).
  Global Instance discr_fun_syn_equiv `{OfeDiscrete A} {s} : Equiv (A → iSyn s) := _.
  Global Instance discr_fun_syn_dist `{OfeDiscrete A} {s} : Dist (A → iSyn s) := λ n f g, ∀ x, f x ≡{n}≡ g x.

  Definition ofe_fun_syn_mixin `{OfeDiscrete A} {s} : OfeMixin (A → iSyn s).
  Proof. split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure substC `{OfeDiscrete A} {s} : ofeT := OfeT (A → iSyn s) ofe_fun_syn_mixin.

  Global Program Instance syn_rename_ne {s: sort}
    `{proper_hrpreD1: ∀ ρ, NonExpansive (λ v: preD, rename ρ v)}
    `{proper_hrpreD2: NonExpansive2 (λ (ρ: varC -n> varC) (v: preD), rename ρ v)}:
    NonExpansive2 (@syn_rename (laterC preD) _ s).
  Next Obligation.
    intros ** r1 r2 Hr t t' Ht. move: r1 r2 t' Ht Hr.
    induction t; intros; inversion Ht; simplify_eq; cbn; f_equiv;
      try by [apply IHt | apply IHt1 | apply IHt2|].
    - inversion H1; exact: Hr.
    - eapply IHt=>//. move => [|m] //=. f_equiv. apply Hr.
    - move: α α2 {Ht} H2 => [α] [α2] H2 /=. rewrite /Rename_lpreD.
      f_contractive.
      by eapply (proper_hrpreD2 n (λne x, r1 x) (λne x, r2 x)).
  Qed.

  Program Definition syn_rename_ofe {s}
    `{proper_hrpreD1: ∀ ρ, NonExpansive (λ v: preD, rename ρ v)}
    `{proper_hrpreD2: NonExpansive2 (λ (ρ: varC -n> varC) (v: preD), rename ρ v)}:
    (varC -n> varC) -n> iSyn s -n> iSyn s :=
    λne ρ v, syn_rename ρ v.
  Solve All Obligations with solve_proper_cbn.
  Fail Next Obligation.

  Program Definition syn_hsubst_ofe {s} {hspreD: HSubst vl preD}
    `{proper_hrpreD1: ∀ ρ, NonExpansive (λ v: preD, rename ρ v)}
    `{proper_hrpreD2: NonExpansive2 (λ (ρ: varC -n> varC) (v: preD), rename ρ v)}
    `{proper_hspreD1: ∀ ρ, NonExpansive (λ v: preD, hsubst ρ v)}
    `{proper_hspreD2: NonExpansive2 (λ (ρ: varC -n> vl) (v: preD), hsubst ρ v)}:
    (varC -n> vl) -n> iSyn s -n> iSyn s :=
    λne ρ v, syn_hsubst ρ v.
  Next Obligation.
    intros **???. move: s x y H ρ.
    induction x; intros; inversion H; simplify_eq; cbn; f_equiv;
      try by [apply IHx| apply IHx1 | apply IHx2|].
    by unshelve eapply (IHx _ _ (λne x, up ρ x)).
    by f_equiv.
  Qed.
  Next Obligation.
    intros ** x y H t; move: x y H.
    induction t; cbn; intros; f_equiv;
    try by [apply IHt| apply IHt1 | apply IHt2|]; eauto.
    - unshelve eapply (IHt (λne z, up x z) (λne z, up y z)).
      rewrite /up.
      move => [|m] //=.
      by f_equiv.
    - move: α => [α] /=. rewrite /hsubst_lpreD.
      f_contractive.
      eapply proper_hspreD2 => //. by apply dist_S.
  Qed.


  (* Global Instance proper_hspreD n ρ `{!HSubst vl preD} :
    Proper (dist n ==> dist n) (λ v: preD, hsubst ρ v).
  Proof. intros** x y H. *)

  (* Global Program Instance syn_hsubst_ne s: NonExpansive2 (@syn_hsubst (laterC preD) _ _ s). *)
  Fail Next Obligation.
  Fail Global Program Instance HSubst_preD : HSubst vl preD :=
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
    λne (ρ: varC -n> A),
    ofe_compose (lift_varfun r) ρ.
  Solve All Obligations with solve_proper_cbn.
  (* ofe-variant of scomp/>>. *)
  (* Program Definition ofe_scomp {A: ofeT} {H: Subst A}
    (sb: var → A) (ρ: varC -n> A) := *)
End openSemanticSyntax.
