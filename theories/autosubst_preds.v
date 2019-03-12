From Coq.ssr Require Import ssreflect.
From stdpp Require Import base.
From Autosubst Require Import Autosubst.

Section composition.
  Context (vl: Type) `{!Ids vl, !Rename vl, !Subst vl, SubstLemmas vl}.

  Definition pred := (var -> vl) → vl → Prop.

  Instance HSubst_pred : HSubst vl pred := fun sb pred ρ => pred (sb >> ρ).

  Instance Rename_pred : Rename pred := fun r pred => pred.|[ren r].
  Instance Inh_pred : Inhabited pred := populate (fun _ _ => False).
  Instance Ids_pred : Ids pred := λ _, inhabitant.

  Instance HSubstLemmas_pred : HSubstLemmas vl pred.
  Proof.
    split; rewrite /hsubst /HSubst_pred => //= *; f_ext => ?; by asimpl.
  Qed.
End composition.
