Require Import unSecureND.
Require Import Program.

Variable Ra Rb Rn: Repository.t.
Axiom HRb: repository_lt Ra Rb.
Axiom HRn: repository_lt Rb Rn.

Variable Pa Pb: profile.
Axiom HPa: typable_profile Ra Pa.
Axiom HPb: typable_profile Rb Pb.

Variable f: Resource.t.
Axiom Hf: typable Rb f.
Program Axiom f_distrusted: NDProof Pa (nd_not (nd_trust f)).

Axiom profile_merge_typable: forall R P1 P2,
  typable_profile R P1 -> typable_profile R P2 -> typable_profile R (profile_merge P1 P2).

Lemma not_impl_bottom: forall x, Resource.eq (nd_not x) (nd_impl x nd_bottom).
  destruct x; simpl; try (try split; reflexivity); destruct x2; try split; reflexivity.
Qed.

Axiom zip_eq: forall l1 l1' l2 l2',
  eqlistA Resource.eq l1 l1' -> eqlistA Resource.eq l2 l2' -> eqlistA Resource.eq (zip l1 l2) (zip l1' l2').

Add Morphism zip with signature (eqlistA Resource.eq) ==> (eqlistA Resource.eq) ==> (eqlistA Resource.eq) as zip_m.
Proof.
  intros. apply zip_eq. apply H. apply H0.
Qed.

Add Morphism profile_merge with signature profile_eq ==> profile_eq ==> profile_eq as profile_merge_m.
Proof.
  unfold profile_eq; unfold profile_merge; simpl. intros. split.
     apply zip_eq. apply H. apply H0.
     split. intros. apply ResourceSet.union_spec. elim (ResourceSet.union_spec (separate x) (separate x0) a).
       intros. elim H2. intros. left. apply (proj2 H). apply H4.
       intros. right. apply (proj2 H0). apply H4. apply H1.
     intros. apply ResourceSet.union_spec. elim (ResourceSet.union_spec (separate y) (separate y0) a).
       intros. elim H2. intros. left. apply (proj2 H). apply H4.
       intros. right. apply (proj2 H0). apply H4. apply H1.
Qed.

Add Morphism singleton_profile with signature Resource.eq ==> profile_eq as singleton_profile_m.
  intros. unfold profile_eq. unfold singleton_profile. simpl. split.
    apply eqlistA_cons. apply H.
    apply eqlistA_nil.
    reflexivity.
Qed.

Hint Resolve HPa HRb HRn.

Ltac sprem :=
  repeat match goal with
  | |- repository_leq ?x ?x => right; reflexivity
  | |- repository_leq ?x ?y => try (assumption || left)
  | |- profile_in ?x (singleton_profile ?x) => left; apply InA_cons_hd; reflexivity
  | |- profile_in ?x (profile_merge ?y (singleton_profile ?x)) => left; apply zip_in_r; apply InA_cons_hd; reflexivity
  | |- profile_in ?x (profile_merge (singleton_profile ?x) ?y) => left; apply zip_in_l; apply InA_cons_hd; reflexivity
  | |- typable_profile ?R empty_profile => apply empty_profile_typable
  | |- typable_profile ?R (singleton_profile ?x) => apply singleton_profile_typable
  | |- typable_profile ?R (profile_merge ?x ?y) => apply profile_merge_typable
  | |- typable ?R (nd_impl ?x ?y) => apply typable_impl; intros
  | |- typable ?R (nd_trust ?x) => apply typable_trust
  | |- typable ?R (nd_not ?x) => apply typable_not
  | |- typable ?R nd_bottom => apply typable_bottom
  | _ => auto
  end.

Lemma singleton_truth: forall R x,
   typable R x ->
   NDProof (singleton_profile x) x.
Proof.
  intros. rewrite <- (profile_merge_self (singleton_profile x)).
  apply nd_atom_rule with R R; sprem.
Qed.

Lemma trust_to_thingy: forall R1 R2 P x,
  typable_profile R1 P -> typable R2 x -> repository_leq R1 R2 ->
  NDProof P (nd_trust x) ->
  NDProof P x.
Proof.
  intros. apply nd_exec with R1 R2; sprem.
  apply nd_write_intro with R1 R2; sprem.
  apply nd_read_intro with R1 R2; sprem.
Qed.

(*Lemma implication: forall R P x y,
  typable_profile R P -> typable R x -> typable R y ->
  NDProof (profile_merge (profile_merge P (singleton_profile x)) (singleton_profile (nd_impl x y))) y.
Proof.
  intros. rewrite <- profile_merge_assoc. rewrite <- (profile_merge_self (singleton_profile x)).
  rewrite <- (profile_merge_assoc (singleton_profile x) (singleton_profile x) _).
  rewrite (profile_merge_comm (singleton_profile x) (singleton_profile (nd_impl x y))).
  rewrite profile_merge_assoc. rewrite profile_merge_assoc.
  apply nd_impl_elim with R R R; sprem.
  apply nd_atom_rule with R R; sprem.
  rewrite profile_merge_comm.
  apply nd_atom_rule with R R; sprem.
Qed.*)

Axiom empty_blerp: forall Pa f,
  NDProof empty_profile f -> 
  NDProof Pa f.
(* proof through repeated applications of the weakening rule *)

Axiom down_typability:
  forall x R1 R2, typable R1 x -> repository_lt R1 R2 -> typable R2 x.

Lemma aux: forall g, typable Rb f -> typable Rn g -> 
  NDProof Pa (nd_impl (nd_not (nd_trust f)) g) ->
  NDProof Pa (nd_impl (nd_trust (nd_not f)) g).
Proof.
  intros.
  apply nd_impl_intro with Ra Rb Rn; sprem.
  rewrite <- profile_merge_empty_l.
  apply nd_cut with Ra Rn (nd_impl (nd_trust (nd_not f)) (nd_not (nd_trust f))); sprem.
    intros x Hx; apply down_typability with Ra; [ apply HPa; apply Hx | ].
    apply repository_lt_trans with Rb; auto.
    apply repository_lt_trans with Rb; auto.
  apply nd_impl_intro with Rb Rb Rb; sprem.
    rewrite profile_merge_empty_l.
  replace (nd_trust (nd_not f)) with (nd_trust (nd_impl f nd_bottom)) by (apply -> resource_eq; simpl; reflexivity).
  replace (nd_not (nd_trust f)) with (nd_impl (nd_trust f) nd_bottom) by (apply -> resource_eq; simpl; reflexivity).
  apply nd_impl_intro with Rb Rb Rb; sprem.
    rewrite profile_merge_comm.
  apply nd_cut with Rb Rb f; sprem.
  apply trust_to_thingy with Rb Rb; sprem; apply singleton_truth with Rb; sprem.
  apply nd_cut with Rb Rb (nd_impl f nd_bottom); sprem.
    apply trust_to_thingy with Rb Rb; sprem; apply singleton_truth with Rb; sprem.
    rewrite <- (profile_merge_self (singleton_profile f)).
    rewrite <- profile_merge_assoc.
    rewrite profile_merge_comm.
  apply nd_impl_elim with Rb Rb Rb; sprem.
  apply nd_atom_rule with Rb Rb; sprem.
    rewrite profile_merge_comm. 
  apply nd_atom_rule with Rb Rb; sprem.
    rewrite <- profile_merge_assoc. rewrite profile_merge_comm.
  apply nd_cut with Ra Rn (nd_not (nd_trust f)); sprem.
    intros x Hx; apply down_typability with Ra; [ apply HPa; apply Hx | ].
      apply repository_lt_trans with Rb; auto.
      apply repository_lt_trans with Rb; auto.
    rewrite profile_merge_comm. rewrite <- (profile_merge_self (singleton_profile (nd_trust (nd_not f)))).
    rewrite profile_merge_assoc.
  apply nd_impl_elim with Rb Rb Rb; sprem.
    rewrite profile_merge_comm.
  apply nd_atom_rule with Rb Rb; sprem. 
  apply nd_atom_rule with Rb Rb; sprem.
  apply nd_impl_elim with Ra Rb Rn; sprem.
  apply f_distrusted.
Qed.
