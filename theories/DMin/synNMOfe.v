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
        all: try by constructor; apply equiv_dist].
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

  (* Fail to define a COFE.
    - Try 1: have completion only for α in vpack.
      That's broken, since there might be α's nested elsewhere.
    - Try 2: try traversing recursively the term in vpack (ignoring
      other subterms for now, but they must be traversed as well).
      That fails termination checking!
    *)
  Unset Program Cases.
  Program Definition vpack_chain1 {s} (c : chain (synC s)) (a : α) : chain α :=
    {| chain_car n := match c n return _ with vpack a' _ => a' | _ => a end |}.
  Next Obligation. intros s c a n i ?. simpl. by destruct (chain_cauchy c n i). Qed.

  Definition syn_complv1 {s} `{Cofe α} : Compl (synC s) := λ c,
    match c 0 with
    | vpack a t => vpack (compl (vpack_chain1 c a)) t
    | x => x
    end.
(* Ugly proof sketch for syn_cofe. Comment back in to see where it fails. *)
(*
  Global Program Instance syn_cofe {s} `{Cofe α} : Cofe (synC s) :=
    { compl := syn_complv1 }.
  Print Cofe.
  Next Obligation.
    intros ?? n c; rewrite /syn_complv1.
    feed pose proof (chain_cauchy c 0 n) as Heq; first by auto with lia.
    (* Require Import DN.tactics. *)
    inversion Heq.
    1-7: admit.
    -
    dependent destruction H1. dependent destruction H5.
    rewrite -x (conv_compl n (vpack_chain1 c _)) /= -x0. f_equiv.
    (* Unprovable *)
  Abort.
  Abort Obligations. *)

  Program Definition vpack_chain2 {s} (c : chain (synC s)) (a : synC tms) : chain (synC tms) :=
    {| chain_car n := match c n return _ with vpack _ t' => t' | _ => a end |}.
  Next Obligation. intros s c a n i ?; simpl. by destruct (chain_cauchy c n i). Qed.

  Fail Fixpoint syn_compl {s} `{Cofe α} : Compl (synC s) := λ c,
    match c 0 with
    | vpack a t => vpack (compl (vpack_chain1 c a)) (compl (vpack_chain2 c t))
    | x => x
    end.
  (* Eye-balling this recursive call suggests that in fact is *is* terminating
     and that this can be shown by well-founded induction on term size.
     Maybe with Equations that's even convenient.
     But avoiding that'd be nice.
   *)
  Fail Fixpoint syn_compl {s} `{Cofe α} : Compl (synC s) := λ c,
    match c 0 with
    | vpack a t => vpack (compl (vpack_chain1 c a)) (syn_compl (vpack_chain2 c t))
    | x => x
    end.
End synOfe.
Arguments synC: clear implicits.

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
