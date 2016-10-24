(* SecureND *)

Require Import Coq.Structures.Orders.
Require Export MSets.
Require Import Program.

(* Repository type: *)
Module Type REPOSITORY <: DecidableType.
  Parameter t: Type.

  Parameter eq: t -> t -> Prop.

  Axiom eq_refl: forall x: t, eq x x.
  Axiom eq_sym: forall x y: t, eq x y -> eq y x.
  Axiom eq_trans: forall x y z: t, eq x y -> eq y z -> eq x z.
  Instance eq_equiv : Equivalence eq := Build_Equivalence eq eq_refl eq_sym eq_trans. 

  Parameter eq_dec: forall x y, { eq x y } + { ~ eq x y }.
End REPOSITORY.

(* Atom *)
Module Type ATOM (G: REPOSITORY) <: DecidableType.
  Definition t := G.t -> Type.

  Parameter eq: t -> t -> Prop.

  Axiom eq_refl: forall x: t, eq x x.
  Axiom eq_sym: forall x y: t, eq x y -> eq y x.
  Axiom eq_trans: forall x y z: t, eq x y -> eq y z -> eq x z.
  Instance eq_equiv : Equivalence eq := Build_Equivalence eq eq_refl eq_sym eq_trans. 
  
  Parameter eq_dec: forall x y, { eq x y } + { ~ eq x y }.
End ATOM.

(* The resource type, defining the different connectives *)
Inductive Resource {A: Type} {S: Type}: Type :=
| nd_atom: A -> Resource
| nd_bottom: Resource
| nd_impl: Resource -> Resource -> Resource
| nd_and: Resource -> Resource -> Resource
| nd_or: Resource -> Resource -> Resource
| nd_not: Resource -> Resource
| nd_read: Resource -> Resource
| nd_write: Resource -> Resource
| nd_trust: Resource -> Resource.

(* Resources, with equality *)
Module RESOURCE (R: REPOSITORY) (Atom: ATOM R) <: OrderedType.

  Definition t := @Resource Atom.t R.t.
  Function eq (x y: t): Prop :=
  match x with
  | nd_atom x' => match y with nd_atom y' => Atom.eq x' y' | _ => False end
  | nd_bottom => match y with nd_bottom => True | _ => False end
  | nd_impl x1 x2 =>
    match y with nd_impl y1 y2 => eq x1 y1 /\ eq x2 y2 | _ => False end
  | nd_and x1 x2 =>
    match y with nd_and y1 y2 => eq x1 y1 /\ eq x2 y2 | _ => False end
  | nd_or x1 x2 =>
    match y with nd_or y1 y2 => eq x1 y1 /\ eq x2 y2 | _ => False end
  | nd_not x1 =>
    match y with nd_not y1 => eq x1 y1 | _ => False end
  | nd_read x' => match y with nd_read y' => eq x' y' | _ => False end
  | nd_write x' => match y with nd_write y' => eq x' y' | _ => False end
  | nd_trust x' => match y with nd_trust y' => eq x' y' | _ => False end
  end.
  Parameter lt: t -> t -> Prop.

  Lemma eq_refl: forall x, eq x x.
  Proof.
  induction x;
    first [ apply Atom.eq_refl
    | reflexivity
    | (split; [apply IHx1 | apply IHx2])
    | apply IHx
    ].
  Qed.
  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    intros x y; functional induction eq x y; try (intros; contradiction);
    first
    [ intros Heq; apply Atom.eq_sym; apply Heq
    | reflexivity
    | intros [H1 H2]; split; [ apply IHP; apply H1 | apply IHP0; apply H2 ]
    | intros H1; apply IHP; apply H1
    ].
  Qed.
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z. 
  Proof.
    intros x y; functional induction eq x y; try (intros; contradiction);
    first
    [ destruct z; try (intros; contradiction); intros XY YZ; apply Atom.eq_trans with y'; [ apply XY | apply YZ ]
    | intros z _ H; apply H
    | destruct z; try (intros; contradiction); intros XY YZ; split; [ apply IHP | apply IHP0 ]; first [ apply XY | apply YZ ]
    | destruct z; try (intros; contradiction); intros XY YZ; apply IHP; [ apply XY | apply YZ ]
    ].
  Qed.
  Instance eq_equiv: Equivalence eq := Build_Equivalence eq eq_refl eq_sym eq_trans.

  Lemma eq_dec: forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    intros x y; functional induction eq x y; try first [ intros; contradiction | auto ];
    first
    [ apply Atom.eq_dec 
    | auto
    ];
    destruct IHP as [Heq1 | Hneq1]; destruct IHP0 as [Heq2 | Hneq2];
    first
    [ left; split; [ apply Heq1 | apply Heq2 ]
    | right; intro H; first [ apply Hneq1 | apply Hneq2 ]; apply H
    ].
  Qed.

  Axiom lt_trans: forall x y z: t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq: forall x y: t, lt x y -> ~ eq x y.
  Axiom lt_strorder: StrictOrder lt.
  Axiom lt_compat : Proper (eq==>eq==>iff) lt.
 
  Parameter compare: t -> t -> comparison.
  Parameter compare_spec : forall s s', CompSpec eq lt s s' (compare s s').
End RESOURCE.

(* A protocol is a list of resources *)

(* Define two standard repositories Ra and Rb, s.t. Ra < Rb *)
Declare Module Repository: REPOSITORY.
Declare Module Atom: ATOM Repository.
Module Resource := RESOURCE(Repository)(Atom).

Axiom resource_eq: forall (a b: Resource.t), Resource.eq a b <-> a = b.

Lemma resource_eq_dec: forall (a b: Resource.t), { a = b } + { a <> b }.
Proof.
  intros a b; destruct (Resource.eq_dec a b) as [ Heq | Hneq ];
  [ left; apply resource_eq; apply Heq
  | right; intros X; apply Hneq; apply <- resource_eq; apply X
  ].
Qed.

Fixpoint profile_eq (Pa: list Resource.t) (Pb: list Resource.t): Prop :=
  match Pa, Pb with
  | nil, nil => True
  | ha::ta, hb::tb => Resource.eq ha hb /\ profile_eq ta tb
  | _, _ => False
  end.

Instance profile_eq_equiv: Equivalence profile_eq.
Proof.
  split;
  [ intros P; induction P; 
    [ simpl; trivial
    | split; [ reflexivity | apply IHP ]
    ]
  | intros Pa; induction Pa; intros Pb; destruct Pb; intros H; try (simpl; trivial); split;
    [ symmetry; apply (proj1 H)
    | apply IHPa; apply (proj2 H)
    ]
  | intros Pa; induction Pa; intros Pb; destruct Pb; intros Pc; destruct Pc; try (simpl; trivial); try contradiction;
    intros Hab Hbc; split;
    [ transitivity t; [ apply (proj1 Hab) | apply (proj1 Hbc) ]
    | apply IHPa with Pb; [ apply (proj2 Hab) | apply (proj2 Hbc) ]
    ]
  ].
Qed.

Lemma profile_in_eq: forall f Pa Pb, In f Pa -> profile_eq Pa Pb -> In f Pb.
Proof.
  intros f Pa; induction Pa; destruct Pb; try contradiction; intros Ha Heq; destruct Ha as [Hf_eq | Hf_in];
  [ left; transitivity a; [ apply resource_eq; symmetry; apply (proj1 Heq) | apply Hf_eq ]
  | right; apply IHPa; [ apply Hf_in | apply (proj2 Heq) ]
  ].
Qed.

(* typability (of a profile and a message is defined by its properties. *)
Parameter typable: Repository.t -> Resource.t -> Prop.
Parameter typable_eq: forall Ra Rb f1 f2,
  Repository.eq Ra Rb -> Resource.eq f1 f2 -> typable Ra f1 -> typable Rb f2.
Add Morphism typable with signature Repository.eq ==> Resource.eq ==> Logic.iff as typable_m.
Proof.
  intros Ra Rb Hreq a b Hpeq; split; apply typable_eq;
  [ apply Hreq
  | apply Hpeq
  | symmetry; apply Hreq
  | symmetry; apply Hpeq
  ].
Qed.

(* a profile is typable if all its messages are typable *)
Definition typable_profile (R: Repository.t) (P: list Resource.t): Prop :=
  forall f, In f P -> typable R f.

Lemma typable_sublist: forall R f P, typable_profile R (f::P) -> typable_profile R P.
Proof.
  intros R f P Htyp x Hin; apply Htyp; right; apply Hin.
Qed.

Add Morphism typable_profile with signature Repository.eq ==> profile_eq ==> Logic.iff as typable_profile_m.
Proof.
  intros Ra Rb Hreq Pa Pb Heq; destruct Pa as [ | a Pa]; destruct Pb as [ | b Pb]; try contradiction;
  [ split; intros f R Hf; contradiction
  | split; intros Htyp f [ Hfeq | Hfin ];
    [ rewrite <- Hfeq; destruct Heq as [Eq_ab Eq_PaPb]; rewrite <- Eq_ab; rewrite <- Hreq; apply Htyp; apply in_eq
    | destruct Heq as [Eq1 Eq2]; rewrite <- Hreq; apply Htyp; apply in_cons; apply profile_in_eq with Pb; [ apply Hfin | symmetry; apply Eq2 ]
    | rewrite <- Hfeq; destruct Heq as [Eq_ab Eq_PaPb]; rewrite Eq_ab; rewrite Hreq; apply Htyp; apply in_eq
    | destruct Heq as [Eq1 Eq2]; rewrite Hreq; apply Htyp; apply in_cons; apply profile_in_eq with Pa; [ apply Hfin | apply Eq2 ]
    ]
  ].
Qed.

Axiom typable_and: forall R f1 f2, typable R f1 /\ typable R f2 -> typable R (nd_and f1 f2).

Axiom typable_or: forall R f1 f2, typable R f1 \/ typable R f2 -> typable R (nd_or f1 f2).

Axiom typable_impl: forall R f1 f2, (typable R f1 -> typable R f2) -> typable R (nd_impl f1 f2).

(* this is due to the fact that ~f is equivalent to f -> bot, and bot is typable everywhere *)
Axiom typable_not: forall R f, typable R (nd_not f).

Axiom repository_not_empty: forall R: Repository.t, exists f, typable R f.

(* lt order *)
Definition repository_lt (R1: Repository.t) (R2: Repository.t): Prop :=
  forall f1, typable R1 f1 -> forall f2, typable R2 f2 -> Resource.lt f1 f2.

Lemma repository_lt_trans: forall R1 R2 R3, repository_lt R1 R2 -> repository_lt R2 R3 -> repository_lt R1 R3.
Proof.
  intros R1 R2 R3 H12 H23 f1 Hf1 f3 Hf3; destruct (repository_not_empty R2) as [f2 Hf2]; transitivity f2;
  [ apply H12; [ apply Hf1 | apply Hf2 ]
  | apply H23; [ apply Hf2 | apply Hf3 ]
  ].
Qed.

Fixpoint is_valid (l: list Resource.t): Prop :=
  match l with
  | [] => True
  | h::t => match t with
    | [] => True
    | h'::t' => Resource.lt h h' /\ is_valid t
    end
  end.

Section NDC_definition.
(* ndproof:
   hypotheses |- message
   (i.e. NDProof P m is a proof of P |- m, where m is a message.)
   The ND calculus
 *)

Inductive NDProof: list Resource.t -> Resource.t -> Prop :=
  (* operational rules *)
  | nd_atom_mess: forall Ra Rb Pa Pb f, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_lt Ra Rb ->
      typable Rb f -> NDProof (Pa ++ Pb) f
  | nd_bot: forall Ra Pa f1, typable_profile Ra Pa ->
      typable Ra f1 ->
      NDProof Pa (nd_impl f1 nd_bottom) ->
      NDProof Pa (nd_not f1)
  | nd_and_intro: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_lt Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof Pa f1 -> NDProof Pb f2 ->
      NDProof (Pa ++ Pb) (nd_and f1 f2)
  | nd_and_elim_l: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_lt Ra Rb ->
      typable Ra f1 -> typable Rb f2 -> 
      NDProof (Pa ++ Pb) (nd_and f1 f2) ->
      NDProof (Pa ++ Pb) f1
  | nd_and_elim_r: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_lt Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof (Pa ++ Pb) (nd_and f1 f2) ->
      NDProof (Pa ++ Pb) f2
  | nd_or_intro_l: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_lt Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof (Pa ++ Pb) f1 ->
      NDProof (Pa ++ Pb) (nd_or f1 f2)
  | nd_or_intro_r: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_lt Ra Rb ->
      typable Ra f1 -> typable (Rb) f2 ->
      NDProof (Pa ++ Pb) f2 ->
      NDProof (Pa ++ Pb) (nd_or f1 f2)
  | nd_or_elim: forall Ra Rb Rc Pa Pb f1 f2 g, typable_profile Ra Pa -> typable_profile Rb Pb ->
      repository_lt Ra Rb ->
      typable Ra f1 -> typable Rb f2 -> typable Rc g ->
      NDProof (Pa ++ Pb) (nd_or f1 f2) ->
      NDProof [f1] g ->
      NDProof [f2] g ->
      NDProof (Pa ++ Pb) g
  | nd_impl_intro: forall Ra Rb Rc Pa f1 f2, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f1 -> typable Rc f2 ->
      NDProof (Pa ++ [f1]) f2 ->
      NDProof Pa (nd_impl f1 f2)
  | nd_impl_elim: forall Ra Rb Rc Pa  f1 f2, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f1 -> typable Rc f2 ->
      NDProof Pa (nd_impl f1 f2) ->
      NDProof Pa f1 ->
      NDProof (Pa ++ [f1]) f2
  (* access rules *)
  | nd_read_distrib: forall Ra Rb Pa f1, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f1 ->
      NDProof Pa (nd_not (nd_read f1)) ->
      NDProof Pa (nd_read (nd_not f1))
  | nd_trust_distrib: forall Ra Rb Pa f1, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f1 ->
      NDProof Pa (nd_not (nd_trust f1)) ->
      NDProof Pa (nd_trust (nd_not f1))
  | nd_write_distrib: forall Ra Rb Pa f1, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f1 ->
      NDProof Pa (nd_not (nd_write f1)) ->
      NDProof Pa (nd_write (nd_not f1))
  | nd_read_intro: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f -> NDProof Pa (nd_read f)
  | nd_trust_intro: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_read f) ->
      NDProof Pa (nd_trust f)
  | nd_write_intro: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_read f) ->
      NDProof Pa (nd_trust f) ->
      NDProof Pa (nd_write f)
  | nd_exec: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_write f) ->
      NDProof Pa f
  | nd_dtrust_intro: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_impl (nd_read f) nd_bottom) ->
      NDProof Pa (nd_not (nd_trust f))
  | nd_dtrust_elim: forall Ra Rb Rc Pa f1 f2, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Rb f1 -> typable Rc f2 ->
      NDProof Pa (nd_not (nd_trust f1)) ->
      NDProof Pa (nd_impl (nd_not (nd_trust f1)) f2) ->
      NDProof Pa (nd_write f2)
  | nd_mtrust_intro: forall Ra Rb Pa f1 f2, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof Pa (nd_impl (nd_read f2) nd_bottom) ->
      NDProof [f1] (nd_impl (nd_read f2) nd_bottom) ->
      NDProof (List.remove resource_eq_dec f1 Pa ++ [f2]) (nd_not (nd_trust f1))
  | nd_mtrust_elim: forall Ra Rb Rc Pa Pc f1 f2, typable_profile Ra Pa -> typable_profile Rc Pc -> repository_lt Ra Rb -> repository_lt Rc Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof (List.remove resource_eq_dec f1 Pa ++ [f2]) (nd_not (nd_trust f1)) ->
      NDProof (List.remove resource_eq_dec f1 Pa ++ Pc) (nd_trust f2)
  (* structural rules *)
  | nd_weakening: forall Ra Rb Pa f1 f2, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof Pa (nd_write f1) ->
      NDProof Pa (nd_trust f2) ->
      NDProof (Pa ++ [f2]) (nd_write f1)
  | nd_contraction: forall Ra Rb Pa f g, typable_profile Ra Pa -> repository_lt Ra Rb ->
      typable Ra f -> typable Rb f -> typable Ra g ->
      In f Pa -> NDProof (Pa ++ [f]) (nd_write f) ->
      NDProof Pa (nd_write f)
  (* exchange rule not needed? *)
  | nd_cut: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_lt Ra Rb ->
      typable Rb f1 -> typable Rb f2 ->
      NDProof Pa f1 ->
      In f1 Pb -> NDProof (Pb) f2 ->
      NDProof (Pa ++ Pb) f2.


(*Axiom nd_import: forall f,
   NDProof (`Pa::nil) (nd_read f) ->
   typable (`Rb) f ->
   typable_profile Ra (P.add f (`Pa)).*)

(* Properties of dominance *)
Axiom typable_1_read: forall Ra Pa f, typable_profile Ra Pa ->
  typable Ra f -> NDProof Pa (nd_read f).
Axiom typable_1_write: forall Ra Pa f, typable_profile Ra Pa ->
  typable Ra f -> NDProof Pa (nd_write f).
Axiom typable_2_read: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_lt Ra Rb ->
  typable Rb f -> NDProof Pa (nd_read f).
Axiom typable_3_write: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_lt Ra Rb ->
  typable Rb f ->
  (NDProof Pa (nd_write f) <->
     NDProof Pa (nd_read f) /\
     NDProof Pa (nd_trust f)).

(*Axiom proof_in: forall P x,
  NDProof (P::nil) x <-> In x P.

Axiom add_empty_protocol: forall P P' f,
  NDProof (P::nil) f -> Empty P' -> NDProof (P::P'::nil) f.*)

(*Axiom equal_is_okay: forall l1 l2 f,
  NDProof l1 f -> eqlistA eq l1 l2 -> NDProof l2 f.*)

(*Axiom nd_write_proof: forall R P f, typable_profile R P -> typable R f ->
  NDProof (P::nil) (nd_write f) -> NDProof (P::nil) f.*)

(* Write down version of the import rule *)
(*Lemma nd_import_write_down: 
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
Qed.*)

End NDC_definition.