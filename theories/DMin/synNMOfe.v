From Autosubst Require Export Autosubst.
From stdpp Require Import base.
From Coq.ssr Require Import ssreflect.
From iris.algebra Require Import base.

From DN Require Import autosubst_preds DMin.synNonMutual.

From iris.algebra Require Import ofe.

Section syn_relation.
  Context `{α : Type}.
  Notation "'vl'" := (syn α vls).
  Notation "'tm'" := (syn α tms).

  Context {Rα: relation α}.
  Context {Rvar: relation var}.
  Context {Rnat: relation nat}.
  Inductive sr : ∀ {s}, relation (syn α s) :=
  | rtv v1 v2 :
      sr v1 v2 →
      sr (tv v1) (tv v2)
  | rtapp ta1 ta2 tb1 tb2:
      sr ta1 ta2 →
      sr tb1 tb2 →
      sr (tapp ta1 tb1) (tapp ta2 tb2)
  | rtproj v1 v2:
      sr v1 v2 →
      sr (tproj v1) (tproj v2)
  | rtskip t1 t2:
      sr t1 t2 →
      sr (tskip t1) (tskip t2)
  | rvar_vl i1 i2:
      Rvar i1 i2 →
      sr (var_vl i1) (var_vl i2)
  | rvnat n1 n2:
      Rnat n1 n2 →
      sr (vnat n1) (vnat n2)
  | rvabs t1 t2:
      sr t1 t2 →
      sr (vabs t1) (vabs t2)
  | rvpack α1 α2 t1 t2:
      Rα α1 α2 →
      sr t1 t2 →
      sr (vpack α1 t1) (vpack α2 t2)
  .
End syn_relation.

Arguments sr {_} _ _ _ {_}.

Require Import Program.Equality.

Section syn_relation_prop.
  Context `{R1 : relation α, R2 : relation var, R3 : relation nat}.

  Global Instance sr_refl :
    Reflexive R1 → Reflexive R2 → Reflexive R3 → Reflexive (sr R1 R2 R3 (s := s)).
  Proof. intros ????; elim; constructor; eauto. Qed.
  Global Instance sr_sym :
    Symmetric R1 → Symmetric R2 → Symmetric R3 → Symmetric (sr R1 R2 R3 (s := s)).
  Proof. induction 4; constructor; eauto. Qed.
  Global Instance sr_trans :
    Transitive R1 → Transitive R2 → Transitive R3 → Transitive (sr R1 R2 R3 (s := s)).
  Proof. induction 4; intro x; dependent induction x; constructor; eauto. Qed.
  Global Instance sr_equiv :
    Equivalence R1 → Equivalence R2 → Equivalence R3 → Equivalence (sr R1 R2 R3 (s := s)).
  Proof. split; apply _. Qed.

  (* A few of these instances; do we really need one per constructor? *)
  Global Instance tv_proper : Proper (sr R1 R2 R3 ==> sr R1 R2 R3) tv.
  Proof. constructor; auto. Qed.
  Global Instance tapp_proper : Proper (sr R1 R2 R3 ==> sr R1 R2 R3 ==> sr R1 R2 R3) tapp.
  Proof. constructor; auto. Qed.
  Global Instance tproj_proper : Proper (sr R1 R2 R3 ==> sr R1 R2 R3) tproj.
  Proof. constructor; auto. Qed.
  Global Instance tskip_proper : Proper (sr R1 R2 R3 ==> sr R1 R2 R3) tskip.
  Proof. constructor; auto. Qed.
  Global Instance var_vl_proper : Proper (R2 ==> sr R1 R2 R3) var_vl.
  Proof. constructor; auto. Qed.
  Global Instance vnat_proper : Proper (R3 ==> sr R1 R2 R3) vnat.
  Proof. constructor; auto. Qed.
  Global Instance vabs_proper : Proper (sr R1 R2 R3 ==> sr R1 R2 R3) vabs.
  Proof. constructor; auto. Qed.
  Global Instance vpack_proper : Proper (R1 ==> sr R1 R2 R3 ==> sr R1 R2 R3) vpack.
  Proof. constructor; auto. Qed.

  Global Instance tv_inj : Inj (sr R1 R2 R3) (sr R1 R2 R3) tv.
  Proof. inversion_clear 1; auto. Qed.
  Global Instance tapp_inj: Inj2 (sr R1 R2 R3) (sr R1 R2 R3) (sr R1 R2 R3) tapp.
  Proof. inversion_clear 1; auto. Qed.
  Global Instance tproj_inj : Inj (sr R1 R2 R3) (sr R1 R2 R3) tproj.
  Proof. inversion_clear 1; auto. Qed.
  Global Instance tskip_inj : Inj (sr R1 R2 R3) (sr R1 R2 R3) tskip.
  Proof. inversion_clear 1; auto. Qed.
  Global Instance var_vl_inj : Inj R2 (sr R1 R2 R3) var_vl.
  Proof. inversion_clear 1; auto. Qed.
  Global Instance vnat_inj : Inj R3 (sr R1 R2 R3) vnat.
  Proof. inversion_clear 1; auto. Qed.
  Global Instance vabs_inj : Inj (sr R1 R2 R3) (sr R1 R2 R3) vabs.
  Proof. inversion_clear 1; auto. Qed.
  Global Instance vpack_inj: Inj2 R1 (sr R1 R2 R3) (sr R1 R2 R3) vpack.
  Proof. inversion_clear 1; auto. Qed.
End syn_relation_prop.

Global Instance equivSyn : ∀ {α s} `{!Equiv α}, Equiv (syn α s) :=
  λ α s Eα, sr (≡) (≡) (≡).
(* Beware we keep the same n for Rα. I expect we'll use [α = Next ...] for
   OFEs. *)
Global Instance distSyn : ∀ {α s} `{!Dist α}, Dist (syn α s) :=
  λ α s Eα n, sr (dist n) (dist n) (dist n).

Section syn_map.
  Context {α β: Type}.

  Fixpoint syn_map {s} (f: α → β) (ast: syn α s): syn β s :=
    match ast with
    | tv v => tv (syn_map f v)
    | tapp t1 t2 => tapp (syn_map f t1) (syn_map f t2)
    | tproj v => tproj (syn_map f v)
    | tskip t => tskip (syn_map f t)
    | var_vl x => var_vl x
    | vnat n => vnat n
    | vabs t => vabs (syn_map f t)
    | vpack a t => vpack (f a) (syn_map f t)
    end.
  Arguments syn_map {_} _ !_ / : assert.
  Instance syn_map_inj {s} (f: α → β):
    Inj (=) (=) f → Inj (=) (=) (@syn_map s f).
  Proof.
    intros HinjF x y; induction x; dependent destruction y; intros [=];
      f_equal; auto.
  Qed.
End syn_map.

Section synOfe.
  Context {α: ofeT}.
  Notation "'vl'" := (syn α vls).
  Notation "'tm'" := (syn α tms).

  Global Instance tv_ne: NonExpansive (@tv α) := _.
  Global Instance vpack_ne: NonExpansive2 (@vpack α) := _.

  Definition synOfeMixin s : OfeMixin (syn α s).
  Proof.
    split.
    - move => x y; split => Hx.
      + induction Hx => n; constructor;
        unfold dist, distSyn in *; eauto.
        by apply equiv_dist.
      + induction (Hx 0).
        all: try by constructor; apply equiv_dist.
        all: try by [constructor; apply IHd => n; apply (inj _ _ _ (Hx n))].
        * constructor; [> apply IHd1 => n | apply IHd2 => n].
          (* This seems to busy-loop? *)
          (* destruct (inj2 _ _ _ _ (Hx n)). *)
          all: by destruct (inj2 _ _ _ _ _ (Hx n)).
        * constructor; [> apply equiv_dist => n | apply IHd => n];
          by destruct (inj2 _ _ _ _ _ (Hx n)).
    - apply _.
    - move => n x y; elim; constructor; eauto; by apply dist_S.
  Qed.

  Canonical Structure synC s: ofeT := OfeT (syn α s) (synOfeMixin s).
  Canonical Structure vlC: ofeT := synC vls.
  Canonical Structure tmC: ofeT := synC tms.
  Unset Program Cases.

  Program Definition tv_inv {s} (v : vlC) : synC s -n> vlC := λne ast,
    match ast with tv v' => v' | _ => v end.
  Next Obligation. solve_proper. Qed.

  Program Definition tapp_1_inv {s} (t : tmC) : synC s -n> tmC := λne ast,
    match ast with tapp t' _ => t' | _ => t end.
  Next Obligation. solve_proper. Qed.
  Program Definition tapp_2_inv {s} (t : tmC) : synC s -n> tmC := λne ast,
    match ast with tapp _ t' => t' | _ => t end.
  Next Obligation. solve_proper. Qed.

  Program Definition tproj_inv {s} (v : vlC) : synC s -n> vlC := λne ast,
    match ast with tproj v' => v' | _ => v end.
  Next Obligation. solve_proper. Qed.
  Program Definition tskip_inv {s} (t : tmC) : synC s -n> tmC := λne ast,
    match ast with tskip t' => t' | _ => t end.
  Next Obligation. solve_proper. Qed.

  Program Definition vpack_1_inv {s} (a : α) : synC s -n> α := λne ast,
    match ast with vpack a' _ => a' | _ => a end.
  Next Obligation. solve_proper. Qed.
  Program Definition vpack_2_inv {s} (t : tmC) : synC s -n> tmC := λne ast,
    match ast with vpack _ t' => t' | _ => t end.
  Next Obligation. solve_proper. Qed.
  Program Definition vabs_inv {s} (t : tmC) : synC s -n> tmC := λne ast,
    match ast with vabs t' => t' | _ => t end.
  Next Obligation. solve_proper. Qed.

End synOfe.
Arguments synC: clear implicits.
Arguments tmC: clear implicits.
Arguments vlC: clear implicits.

Section synCofe.
  Context {α: ofeT}.

  (* We must write syn_compl
     by recursion on (c 0); when we get to an alpha, we
     take the limit. *)
  Implicit Types (t: tmC α) (v: vlC α) (s: sort).
  Fixpoint syn_traverse {s} `{Cofe α}
    (ast: synC α s) : Compl (synC α s) := λ c,
    match ast with
    | tv v => tv
        (syn_traverse v (chain_map (tv_inv v) c))
    | tapp t1 t2 => tapp
        (syn_traverse t1 (chain_map (tapp_1_inv t1) c))
        (syn_traverse t2 (chain_map (tapp_2_inv t2) c))
    | tproj v => tproj
        (syn_traverse v (chain_map (tproj_inv v) c))
    | tskip t => tskip
        (syn_traverse t (chain_map (tskip_inv t) c))
    | vabs t => vabs
        (syn_traverse t (chain_map (vabs_inv t) c))
    | vpack a t => vpack
        (compl (chain_map (vpack_1_inv a) c))
        (syn_traverse t (chain_map (vpack_2_inv t) c))
    | var_vl i => var_vl i
    | vnat n => vnat n
    end.

  Definition syn_compl {s} `{Cofe α} : Compl (synC α s) := λ c,
    syn_traverse (c 0) c.
  Global Program Instance syn_cofe {s} `{Cofe α} : Cofe (synC α s) :=
    { compl := syn_compl }.
  Next Obligation.
    intros ?? n c; rewrite /syn_compl.
    feed pose proof (chain_cauchy c 0 n) as Heq; first by auto with lia.
    move: (c 0) Heq => ci.
    induction ci; intros; inversion Heq; subst;
    dependent destruction H0; rewrite -x /= ?conv_compl /= -?x; try by f_equiv.
    - have -> : v1 = chain_car (chain_map (tv_inv ci) c) n. by rewrite /= -x.
      f_equiv; eapply IHci. by rewrite /= -/(tv_inv ci (c n)) Heq.
    - have -> : ta1 = chain_car (chain_map (tapp_1_inv ci1) c) n. by rewrite /= -x.
      have -> : tb1 = chain_car (chain_map (tapp_2_inv ci2) c) n. by rewrite /= -x.
      f_equiv; [eapply IHci1|eapply IHci2]; by rewrite /= -/(tapp_1_inv ci1 (c n)) -/(tapp_2_inv ci2 (c n)) Heq.
    - have ->: v1 = chain_car (chain_map (tproj_inv ci) c) n. by rewrite /= -x.
      f_equiv; eapply IHci. by rewrite /= -/(tproj_inv ci (c n)) Heq.
    - have ->: t1 = chain_car (chain_map (tskip_inv ci) c) n. by rewrite /= -x.
      f_equiv; eapply IHci. by rewrite /= -/(tskip_inv ci (c n)) Heq.
    - have ->: t1 = chain_car (chain_map (vabs_inv ci) c) n. by rewrite /= -x.
      f_equiv; eapply IHci. by rewrite /= -/(vabs_inv ci (c n)) Heq.
    - have ->: t1 = chain_car (chain_map (vpack_2_inv ci) c) n. by rewrite /= -x.
      f_equiv; eapply IHci. by rewrite /= -/(vpack_2_inv ci (c n)) Heq.
  Qed.
End synCofe.

Instance syn_map_ne {A A' : ofeT} {s} n :
  Proper ((dist n ==> dist n) ==>
           dist n ==> dist n) (@syn_map A A' s).
Proof. induction 2; cbn; constructor; eauto. Qed.

Definition synC_map {A A' s} (f : A -n> A') :
  synC A s -n> synC A' s := CofeMor (syn_map f).
Instance synC_map_ne {A A' s} :
  NonExpansive (@synC_map A A' s).
Proof. intros ???? ast; induction ast; cbn; constructor; eauto. Qed.

Program Definition synCF (F : cFunctor) s: cFunctor := {|
  cFunctor_car A B := synC (cFunctor_car F A B) s;
  cFunctor_map A1 A2 B1 B2 fg :=
    synC_map (cFunctor_map F fg)
|}.
Next Obligation.
  intros ?? A1 A2 B1 B2 n ???; by apply synC_map_ne; apply cFunctor_ne.
Qed.
Next Obligation. induction 0; cbn; f_equiv; eauto using cFunctor_id. Qed.
Next Obligation. induction 0; cbn; f_equiv; eauto using cFunctor_compose. Qed.

Instance synCF_contractive F s:
  cFunctorContractive F →
  cFunctorContractive (synCF F s).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply synC_map_ne; apply cFunctor_contractive.
Qed.
