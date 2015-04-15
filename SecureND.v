(* SecureND *)

Require Import Coq.Structures.Orders.
Require Export MSets.
Require Import Program.

(* Repository type: lt is the dominance relationship *)
Module Type REPOSITORY <: OrderedType.
  Parameter t: Type.

  Parameter eq: t -> t -> Prop.
  Parameter lt: t -> t -> Prop. 

  Axiom eq_refl: forall x: t, eq x x.
  Axiom eq_sym: forall x y: t, eq x y -> eq y x.
  Axiom eq_trans: forall x y z: t, eq x y -> eq y z -> eq x z.
  Instance eq_equiv : Equivalence eq := Build_Equivalence t eq eq_refl eq_sym eq_trans. 

  Axiom lt_trans: forall x y z: t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq: forall x y: t, lt x y -> ~ eq x y.
  Axiom lt_strorder: StrictOrder lt.
  Axiom lt_compat : Proper (eq==>eq==>iff) lt.
 
  Parameter compare: t -> t -> comparison.
  Parameter compare_spec : forall s s', CompSpec eq lt s s' (compare s s').

  Parameter eq_dec: forall x y, { eq x y } + { ~ eq x y }.
End REPOSITORY.

(* Atom *)
Module Type ATOM (G: REPOSITORY) <: DecidableType.
  Definition t := G.t -> Type.

  Parameter eq: t -> t -> Prop.

  Axiom eq_refl: forall x: t, eq x x.
  Axiom eq_sym: forall x y: t, eq x y -> eq y x.
  Axiom eq_trans: forall x y z: t, eq x y -> eq y z -> eq x z.
  Instance eq_equiv : Equivalence eq := Build_Equivalence t eq eq_refl eq_sym eq_trans. 
  
  Parameter eq_dec: forall x y, { eq x y } + { ~ eq x y }.
End ATOM.

(* The resource type, defining the different connectives *)
Inductive Resource {A: Type} {S: Type}: Type :=
| nd_atom: A -> Resource
| nd_impl: Resource -> Resource -> Resource
| nd_and: Resource -> Resource -> Resource
| nd_or: Resource -> Resource -> Resource 
| nd_read: Resource -> Resource
| nd_write: Resource -> Resource
| nd_trust: Resource -> Resource.

(* Resources, with equality *)
Module Resource (R: REPOSITORY) (Atom: ATOM R) <: DecidableType.

  Definition t := @Resource Atom.t R.t.
  Function eq (x y: t): Prop :=
  match x with
  | nd_atom x' => match y with nd_atom y' => Atom.eq x' y' | _ => False end
  | nd_impl x1 x2 =>
    match y with nd_impl y1 y2 => eq x1 y1 /\ eq x2 y2 | _ => False end
  | nd_and x1 x2 =>
    match y with nd_and y1 y2 => eq x1 y1 /\ eq x2 y2 | _ => False end
  | nd_or x1 x2 =>
    match y with nd_or y1 y2 => eq x1 y1 /\ eq x2 y2 | _ => False end
  | nd_read x' => match y with nd_read y' => eq x' y' | _ => False end
  | nd_write x' => match y with nd_write y' => eq x' y' | _ => False end
  | nd_trust x' => match y with nd_trust y' => eq x' y' | _ => False end
  end.

  Lemma eq_refl: forall x, eq x x.
  Proof.
    induction x;
      [apply Atom.eq_refl |
      (split; [apply IHx1 | apply IHx2]) .. |
      apply IHx | apply IHx | apply IHx].
  Qed.
  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    induction x.
      destruct y;
      [apply Atom.eq_sym |
      (intros X; contradiction X) ..].
      destruct y;
      [intros X; contradiction X |
       split; [apply IHx1; apply H | apply IHx2; apply H] |
       (intros X; contradiction X) ..].
      destruct y;
      [intros X; contradiction X | intros X; contradiction X |
       split; [apply IHx1; apply H | apply IHx2; apply H] |
       (intros X; contradiction X) ..].
      destruct y;
      [intros X; contradiction X .. |
       split; [apply IHx1; apply H | apply IHx2; apply H] |
       intros X; contradiction X | intros X; contradiction X | intros X; contradiction X].
      destruct y;
      [intros X; contradiction X .. |
       apply IHx; apply H |
       intros X; contradiction X | intros X; contradiction X].
      destruct y;
      [intros X; contradiction X .. |
       apply IHx; apply H |
       intros X; contradiction X].
      destruct y;
      [intros X; contradiction X .. |
       apply IHx; apply H].
  Qed.
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z. 
  Proof.
   induction x.
      destruct y;
        [destruct z;
          [apply Atom.eq_trans | intros X Y; contradiction Y ..]
        | intros z X; contradiction X ..].
      destruct y;
      [ intros z X; contradiction X
      | destruct z;
        [ intros X Y; contradiction Y
        | split;
            [apply IHx1 with y1; [apply H | apply H0] |
             apply IHx2 with y2; [apply H | apply H0]
            ]
        | intros X Y; contradiction Y ..
        ]
      | intros z X; contradiction X .. ].
      destruct y;
      [ intros z X; contradiction X
      | intros z X; contradiction X
      | destruct z;
        [ intros X Y; contradiction Y
        | intros X Y; contradiction Y
        | split;
            [apply IHx1 with y1; [apply H | apply H0] |
             apply IHx2 with y2; [apply H | apply H0]
            ]
        | intros X Y; contradiction Y ..
        ]
      | intros z X; contradiction X .. ].
      destruct y;
      [ intros z X; contradiction X ..
      | destruct z;
        [ intros X Y; contradiction Y ..
        | split;
            [apply IHx1 with y1; [apply H | apply H0] |
             apply IHx2 with y2; [apply H | apply H0]
            ]
        | intros X Y; contradiction Y
        | intros X Y; contradiction Y
        | intros X Y; contradiction Y
        ]
      | intros z X; contradiction X
      | intros z X; contradiction X
      | intros z X; contradiction X ].
      destruct y;
      [ intros z X; contradiction X ..
      | destruct z;
        [ intros X Y; contradiction Y ..
        | intros; apply IHx with y; [apply H | apply H0]
        | intros X Y; contradiction Y
        | intros X Y; contradiction Y ]
      | intros z X; contradiction X
      | intros z X; contradiction X].
      destruct y;
      [ intros z X; contradiction X ..
      | destruct z;
        [ intros X Y; contradiction Y ..
        | intros; apply IHx with y; [apply H | apply H0]
        | intros X Y; contradiction Y ]
      | intros z X; contradiction X].
      destruct y;
      [ intros z X; contradiction X ..
      | destruct z;
        [ intros X Y; contradiction Y ..
        | intros; apply IHx with y; [apply H | apply H0]]
      ].
  Qed.
  Instance eq_equiv: Equivalence eq := Build_Equivalence _ eq eq_refl eq_sym eq_trans.

  Lemma eq_dec: forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    induction x.
      destruct y;
      [ apply Atom.eq_dec
      | right; auto ..
      ].
      destruct y;
      [ right; auto
      | elim (IHx1 y1);
        [ elim (IHx2 y2);
          [ left; split; [ apply a0 | apply a ]
          | right; intro; apply b; apply H ]
        | right; intro; apply b; apply H ]
      | right; auto .. ].         
      destruct y;
      [ right; auto | right; auto
      | elim (IHx1 y1);
        [ elim (IHx2 y2);
          [ left; split; [ apply a0 | apply a ]
          | right; intro; apply b; apply H ]
        | right; intro; apply b; apply H ]
      | right; auto .. ].
      destruct y;
      [ right; auto | right; auto | right; auto
      | elim (IHx1 y1);
        [ elim (IHx2 y2);
          [ left; split; [ apply a0 | apply a ]
          | right; intro; apply b; apply H ]
        | right; intro; apply b; apply H ]
      | right; auto .. ].
      destruct y;
      [ right; auto ..
      | elim (IHx y);
        [ left; apply a
        | right; auto
        ]
      | right; auto | right; auto ].
      destruct y;
      [ right; auto ..
      | elim (IHx y);
        [ left; apply a
        | right; auto
        ]
      | right; auto ].
      destruct y;
      [ right; auto ..
      | elim (IHx y);
        [ left; apply a
        | right; auto
        ]
      ].
  Qed.
End Resource.

(* A protocol is a set of resources *)
Module Profile (R: REPOSITORY) (A: ATOM R).
  Module E := Resource(R)(A).  
  Include WSetsOn E.
End Profile.

(* Define two standard groups Ga and Rb, s.t. Ga < Rb *)
Declare Module Repository: REPOSITORY.
Declare Module Atom: ATOM Repository.
Module Export P := Profile(Repository)(Atom).
Module Export PFacts := WFactsOn P.E P.
Module Export PProps := WPropertiesOn P.E P.

(* typability (of a profile and a message is defined by its properties. *)
Parameter typable: Repository.t -> P.E.t -> Prop.
Parameter typable_eq: forall Ra Rb f1 f2,
  Repository.eq Ra Rb -> P.E.eq f1 f2 -> typable Ra f1 -> typable Rb f2.
Add Morphism typable with signature Repository.eq ==> P.E.eq ==> Logic.iff as typable_m.
Proof.
  intros. split.
    apply typable_eq. apply H. apply H0.
    apply typable_eq; symmetry; assumption. 
Qed.
  
(* a profile is typable if all its messages are typable *)
Definition typable_profile (R: Repository.t) (P: P.t): Prop :=
  forall f, In f P -> typable R f.
Add Morphism typable_profile with signature Repository.eq ==> P.eq ==> Logic.iff as typable_profile_m.
Proof.
  intros. unfold typable_profile. split.
    intros. apply typable_eq with x f. apply H. reflexivity. apply H1. rewrite H0. apply H2.
    intros; apply typable_eq with y f. symmetry; assumption. reflexivity. apply H1. rewrite <- H0. apply H2. 
Qed.
  
(*Lemma dec_and:
  forall P Q, { P } + { ~P } -> { Q } + { ~Q } -> { P /\ Q } + { ~(P /\ Q) }.
Proof.
  intros P Q HP HQ. destruct HP as [ HP | HnotP ]. 
    destruct HQ as [ HQ | HnotQ ].
      left. split. exact HP. exact HQ.
      right. intro. apply HnotQ. apply H.
    right. intro. apply HnotP. apply H.
Qed.

Lemma dec_not:
  forall P, { P } + { ~P } -> { ~P } + { ~~P }.
Proof.
  intros P HP. destruct HP as [ HP | HnotP ].
    right. intro. apply H. apply HP.
    left. exact HnotP.
Qed.*)

(* wellformedness - this used to include typability, but that is already provided by default *)
Definition well_formed (P: P.t): Prop :=
  ~Empty P.
Add Morphism well_formed with signature P.eq ==> Logic.iff as wf_m.
  intros Pa Pb Peq; unfold well_formed;
    split; intros H; [ rewrite <- Peq | rewrite Peq ]; apply H.
Qed.

Section NDC_definition.
Variable Ra: Repository.t.
Variable Rb: { x | Repository.lt Ra x }.

Variable Pa: { x | typable_profile Ra x }.
Variable Pb: { x | typable_profile (`Rb) x }.

(* ndproof:
   hypotheses |- message
   (i.e. NDProof P m is a proof of P |- m, where m is a message.)
   The ND calculus
 *)
Inductive NDProof: list P.t -> P.E.t -> Prop :=
  | nd_atom_mess: forall b,
      well_formed (`Pa) -> typable (`Rb) b ->
      NDProof (`Pa::`Pb::nil) b
  | nd_and_intro: forall f1 f2,
      NDProof (`Pa::nil) f1 -> typable Ra f1 -> 
      NDProof (`Pb::nil) f2 -> typable (`Rb) f2 -> 
      NDProof (`Pa::`Pb::nil) (nd_and f1 f2)
  | nd_and_elim_l: forall f1 f2,
      NDProof (`Pa::`Pb::nil) (nd_and f1 f2) ->
      typable Ra f1 -> typable (`Rb) f2 -> 
      NDProof (`Pa::`Pb::nil) f1
  | nd_and_elim_r: forall f1 f2,
      NDProof (`Pa::`Pb::nil) (nd_and f1 f2) ->
      typable Ra f1 -> typable (`Rb) f2 -> 
      NDProof (`Pa::`Pb::nil) f2
  | nd_or_intro_l: forall f1 f2,
      NDProof (`Pa::`Pb::nil) f1 ->
      typable Ra f1 -> typable (`Rb) f2 -> 
      NDProof (`Pa::`Pb::nil) (nd_or f1 f2)
  | nd_or_intro_r: forall f1 f2,
      NDProof (`Pa::`Pb::nil) f2 ->
      typable Ra f1 -> typable (`Rb) f2 -> 
      NDProof (`Pa::`Pb::nil) (nd_or f1 f2)
  | nd_or_elim: forall f1 f2 f, 
      NDProof (`Pa::`Pb::nil) (nd_or f1 f2) ->
      typable Ra f1 -> typable (`Rb) f2 -> 
      NDProof (P.singleton f1::nil) f ->
      NDProof (P.singleton f2::nil) f ->
      typable Ra f ->
      NDProof (`Pa::`Pb::nil) f
  | nd_impl_intro: forall f1 f2,
      NDProof (`Pa::P.singleton f1::nil) f2 ->
      typable (`Rb) f1 -> typable (`Rb) f2 ->
      NDProof (`Pa::nil) (nd_impl f1 f2)
  | nd_impl_elim: forall f1 f2,
      NDProof (`Pa::nil) (nd_impl f1 f2) ->
      typable (`Rb) f1 -> typable (`Rb) f2 ->
      NDProof (`Pa::nil) f1 ->
      NDProof (`Pa::P.singleton f1::nil) f2
  | nd_read_intro: forall f,
      well_formed (`Pa) -> typable (`Rb) f ->
      NDProof (`Pa::nil) (nd_read f)
  | nd_trust_intro: forall f,
      NDProof (`Pa::nil) (nd_read f) ->
      well_formed (P.add f (`Pa)) -> 
      NDProof (`Pa::nil) (nd_trust f)
  | nd_write_intro: forall f,
      NDProof (`Pa::nil) (nd_read f) -> NDProof (`Pa::nil) (nd_trust f) ->
      typable (`Rb) f ->
      NDProof (`Pa::nil) (nd_write f).

Axiom nd_import: forall f,
   NDProof (`Pa::nil) (nd_read f) ->
   typable (`Rb) f ->
   typable_profile Ra (P.add f (`Pa)).

(* Properties of dominance *)
Axiom typable_1_read: forall f,
  typable Ra f -> NDProof (`Pa::nil) (nd_read f).
Axiom typable_1_write: forall f,
  typable Ra f -> NDProof (`Pa::nil) (nd_write f).
Axiom typable_2_read: forall f,
  typable (`Rb) f -> NDProof (`Pa::nil) (nd_read f).
Axiom typable_3_write: forall f,
  typable (`Rb) f ->
  (NDProof (`Pa::nil) (nd_write f) <->
     NDProof (`Pa::nil) (nd_read f) /\
     NDProof (`Pa::nil) (nd_trust f)).

Axiom proof_in: forall P x,
  NDProof (P::nil) x <-> In x P.

Axiom add_empty_protocol: forall P P' f,
  NDProof (P::nil) f -> Empty P' -> NDProof (P::P'::nil) f.

(*Axiom equal_is_okay: forall l1 l2 f,
  NDProof l1 f -> eqlistA eq l1 l2 -> NDProof l2 f.*)

Axiom nd_write_proof: forall R P f, typable_profile R P -> typable R f ->
  NDProof (P::nil) (nd_write f) -> NDProof (P::nil) f.

(* Write down version of the import rule *)
Lemma nd_import_write_down: 
  (forall f, In f (`Pb) -> NDProof (`Pa::nil) (nd_write f)) ->
  well_formed (`Pa) ->
  typable_profile Ra (P.union (`Pa) (`Pb)).
Proof.
  intros Hin Hwf x Hx; destruct (union_1 Hx) as [ Ha | Hb ];
  [ apply (proj2_sig Pa); apply Ha
  | refine (nd_import _ _ _ _ _);
    [ refine (proj1 (proj1 (typable_3_write _ _) _));
      [ | apply Hin; apply Hb
      ]
    | | apply add_1; reflexivity
    ]
  ]; apply (proj2_sig Pb); apply Hb.
Qed.

End NDC_definition.
