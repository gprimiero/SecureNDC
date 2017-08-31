Require Import Program.
Require Import unSecureND.

Lemma remove_empty: forall Pa f,
  NDProof (profile_merge empty_profile Pa) f ->
  NDProof Pa f.
Proof.
  intros. apply -> ndproof_m. apply H. reflexivity. rewrite profile_merge_empty_l. reflexivity.
Qed.

Ltac sprem :=
  try assumption || (left; assumption) || (right; reflexivity) ||
    (apply typable_impl; intro; apply typable_bottom) || apply empty_profile_typable.

Lemma lemma1a: forall Ra Rb (* Pa Pb *) f1 f2 f3,
  repository_lt Ra Rb -> (* typable_profile Ra Pa -> typable_profile Rb Pb -> *)
  Resource.lt f1 f2 -> typable Ra f1 -> typable Ra f2 -> typable Rb f3 ->
  NDProof (singleton_profile f1) (nd_impl (nd_read f3) nd_bottom) ->
  NDProof (singleton_profile f2) (nd_impl (nd_read f3) nd_bottom).
Proof.
  intros.
  apply nd_exec with Ra Rb; sprem.
    apply singleton_profile_typable; assumption.
  apply remove_empty.
  apply nd_weakening with Ra Ra; sprem.
  apply nd_write_intro with Ra Rb; sprem.
  apply nd_read_intro with Ra Rb; sprem.
  apply nd_trust_intro with Ra Rb; sprem.
  apply nd_read_intro with Ra Rb; sprem.
    simpl; trivial.
  apply nd_trust_intro with Ra Ra; sprem.
  apply nd_read_intro with Ra Rb; sprem.
    simpl; trivial.
Qed.
