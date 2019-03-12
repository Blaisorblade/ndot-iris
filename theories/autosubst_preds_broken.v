From Coq.ssr Require Import ssreflect.
From stdpp Require Import base.
From Autosubst Require Import Autosubst.

Module composition_broken.
Section composition_broken.
  Context (vl: Type) `{!Ids vl, !Rename vl, !Subst vl, SubstLemmas vl, !HSubst vl (list vl), HSubstLemmas vl (list vl)}.

  Definition pred := list vl → vl → Prop.

  Instance HSubst_pred : HSubst vl pred := fun sb pred ρ => pred ρ.|[sb].

  Instance Rename_pred : Rename pred := fun r pred => pred.|[ren r].
  Instance Inh_pred : Inhabited pred := populate (fun _ _ => False).
  Instance Ids_pred : Ids pred := λ _, inhabitant.

  Instance HSubstLemmas_pred : HSubstLemmas vl pred.
  Proof.
    split; rewrite /hsubst /HSubst_pred //=; asimpl; try done.
    - move => ???; f_ext => x. asimpl. Fail done. (* Fails, wrong way around! *)
  Abort.
End composition_broken.
End composition_broken.

(** The proof failure is about the order of composition, not about using lists.
    Demonstration. *)
Module composition_broken_v2.
Section composition_broken_v2.
  Context (vl: Type) `{!Ids vl, !Rename vl, !Subst vl, SubstLemmas vl}.

  Definition pred := (var -> vl) → vl → Prop.

  Instance HSubst_pred : HSubst vl pred := fun sb pred ρ => pred (ρ >> sb).

  Instance Rename_pred : Rename pred := fun r pred => pred.|[ren r].
  Instance Inh_pred : Inhabited pred := populate (fun _ _ => False).
  Instance Ids_pred : Ids pred := λ _, inhabitant.

  Instance HSubstLemmas_pred : HSubstLemmas vl pred.
  Proof.
    split; rewrite /hsubst /HSubst_pred //=; asimpl; try done.
    - move=>???; f_ext => x; asimpl. Fail done. (* Fails, wrong way around! *)
  Abort.
End composition_broken_v2.
End composition_broken_v2.
(** Defining composition the right way around would be `sb.|[ρ]`,
    but for that we need to convert from a finite list ρ to an infinite Autosubst
    substitution. That can be done, but adds boilerplate. *)
