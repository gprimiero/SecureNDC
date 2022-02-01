(* SecureND *)

(* needs Coq 8.5 or higher *)

Require Import Coq.Structures.Orders.
Require Export MSets.
Require Import Program.
Require Import Arith.
Require Import FunInd.
Import ListNotations.
Require Import RelationClasses.

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

Module Type OrderedBool := Coq.Structures.Orders.OrderedType <+ HasLtb <+ LtbSpec.

(* Resources, with equality *)
Module RESOURCE (R: REPOSITORY) (Atom: ATOM R) <: OrderedBool.
  Definition t := @Resource Atom.t R.t.
  Function eq (x y: t) { struct x }: Prop :=
  match x with
  | nd_atom x' => match y with nd_atom y' => Atom.eq x' y' | _ => False end
  | nd_bottom => match y with nd_bottom => True | _ => False end
  | nd_impl x1 nd_bottom =>
    match y with
    | nd_impl y1 nd_bottom => eq x1 y1
    | nd_not y1 => eq x1 y1
    | _ => False
    end
  | nd_impl x1 x2 =>
    match y with nd_impl y1 y2 => eq x1 y1 /\ eq x2 y2 | _ => False end
  | nd_and x1 x2 =>
    match y with nd_and y1 y2 => eq x1 y1 /\ eq x2 y2 | _ => False end
  | nd_or x1 x2 =>
    match y with nd_or y1 y2 => eq x1 y1 /\ eq x2 y2 | _ => False end
  | nd_not x1 =>
    match y with
    | nd_not y1 => eq x1 y1
    | nd_impl y1 nd_bottom => eq x1 y1
    | _ => False
    end
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
    | destruct x2; simpl; try split; assumption
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
    | intros [H1 H2]; functional induction eq x2 y2; simpl; try split;
      first
      [ apply IHP; apply H1
      | apply Atom.eq_sym; apply H2
      | destruct _x; auto
      | apply IHP0; apply H2
      ]
    ].
  Qed.
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z. 
  Proof.
    intros x y; functional induction eq x y; try (intros; contradiction);
    try first
    [ destruct z; try (intros; contradiction); intros XY YZ; apply Atom.eq_trans with y'; [ apply XY | apply YZ ]
    | intros z _ H; apply H
    | destruct z; try (intros; contradiction); intros XY YZ; split; [ apply IHP | apply IHP0 ]; first [ apply XY | apply YZ ]
    | destruct z; try (intros; contradiction); intros XY YZ; apply IHP; [ apply XY | apply YZ ]
    ]; intros z EQ; simpl;
    [ destruct z; try contradiction; try (destruct z2; try contradiction); apply IHP; apply EQ
    | destruct z; try contradiction; try (destruct z2; try contradiction); apply IHP; apply EQ
    | destruct EQ as [EQ1 EQ2]; destruct x2; destruct y2; try contradiction;
      destruct z; try contradiction; try (destruct z2; contradiction); try (destruct x2_2; contradiction);
      intros [EQz1 EQz2]; split;
      first
      [ apply IHP; [ apply EQ1 | apply EQz1 ]
      | auto
      ]
    | intros; destruct z; try contradiction; try (destruct z2; try contradiction); apply IHP; try (apply EQ || apply H)
    | intros; destruct z; try contradiction; try (destruct z2; try contradiction); apply IHP; try (apply EQ || apply H)
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

  Axiom lt_trans: Transitive lt.
  Axiom lt_irrefl: Irreflexive lt.
  Axiom lt_compat : Proper (eq==>eq==>iff) lt.
  Instance lt_strorder: StrictOrder lt := Build_StrictOrder lt lt_irrefl lt_trans.

  Parameter compare: t -> t -> comparison.
  Parameter compare_spec : forall s s', CompareSpec (eq s s') (lt s s') (lt s' s) (compare s s').

  Definition ltb x y :=
    match compare x y with
    | Lt => true
    | _ => false
    end.

  Parameter ltb_lt : forall x y, ltb x y = true <-> lt x y.
End RESOURCE.

(* A protocol is a list of resources *)

(* Define two standard repositories Ra and Rb, s.t. Ra < Rb *)
Declare Module Repository: REPOSITORY.
Declare Module Atom: ATOM Repository.
Module Resource := RESOURCE(Repository)(Atom).
Declare Module ResourceSet: MSetInterface.SetsOn Resource.
Module Import RSFacts := MSetFacts.WFactsOn Resource ResourceSet.
Module Import RSProps := MSetProperties.WPropertiesOn Resource ResourceSet.

Axiom resource_eq: forall (a b: Resource.t), Resource.eq a b <-> a = b.

Lemma resource_eq_dec: forall (a b: Resource.t), { a = b } + { a <> b }.
Proof.
  intros a b; destruct (Resource.eq_dec a b) as [ Heq | Hneq ];
  [ left; apply resource_eq; apply Heq
  | right; intros X; apply Hneq; apply <- resource_eq; apply X
  ].
Qed.

Lemma not_eq_bot: forall f, Resource.eq (nd_not f) (nd_impl f nd_bottom).
Proof.
  intros; simpl; reflexivity.
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

(* lt order *)
Definition repository_lt (R1: Repository.t) (R2: Repository.t): Prop :=
  (exists f1, typable R1 f1 /\ exists f2, typable R2 f2 /\ Resource.lt f1 f2) /\
  (forall f1, typable R1 f1 -> forall f2, typable R2 f2 -> ~Resource.lt f2 f1).

(* the definition does not directly imply this, but it is part of the definition *)
Axiom repository_lt_trans: forall R1 R2 R3,
  repository_lt R1 R2 -> repository_lt R2 R3 -> repository_lt R1 R3.

Definition repository_leq R1 R2 :=
  repository_lt R1 R2 \/ Repository.eq R1 R2.

Function is_valid_aux (l: list Resource.t): Prop :=
  match l with
  | [] => True
  | h::t => match t with
    | [] => True
    | h'::t' => Resource.lt h h' /\ is_valid_aux t
    end
  end.

Lemma valid_empty: is_valid_aux [].
Proof.
  simpl. trivial.
Qed.

Lemma is_valid_aux_tail:
  forall h t, is_valid_aux (h::t) -> is_valid_aux t.
Proof.
  intros h t H; destruct t as [_ | h']; try auto; apply (proj2 H).
Qed.

Lemma is_valid_aux_cons:
  forall h t, is_valid_aux (h::t) -> ~In h t.
Proof.
  intros h t H; induction t;
  [ apply in_nil
  | apply <- not_in_cons; split;
    [ intro H0; apply (Resource.lt_irrefl h); rewrite H0 at 2; apply (proj1 H)
    | apply IHt; induction t;
      [ simpl; auto
      | split;
        [ transitivity a; [ apply (proj1 H) | apply (proj1 (proj2 H)) ]
        | apply is_valid_aux_tail with a; apply is_valid_aux_tail with h; apply H
        ]
      ]
    ]
  ].
Qed.

Lemma is_valid_aux_elide:
  forall h h' t, is_valid_aux (h::h'::t) -> is_valid_aux (h::t).
Proof.
  intros h h' t H; induction t;
  [ simpl; auto
  | split;
    [ transitivity h'; [ apply (proj1 H) | apply (proj1 (proj2 H)) ]
    | apply is_valid_aux_tail with h'; apply is_valid_aux_tail with h; apply H
    ]
  ].
Qed.

Parameter zip: list Resource.t -> list Resource.t -> list Resource.t.
Parameter zip_in_l: forall x l1 l2, InA Resource.eq x l1 -> InA Resource.eq x (zip l1 l2).
Parameter zip_in_r: forall x l1 l2, InA Resource.eq x l2 -> InA Resource.eq x (zip l1 l2).

Parameter is_valid_aux_zip: forall l1 l2, is_valid_aux l1 -> is_valid_aux l2 ->
  is_valid_aux (zip l1 l2).

Parameter zip_self: forall l1, eqlistA Resource.eq (zip l1 l1) l1.
Parameter zip_commutative: forall l1 l2, eqlistA Resource.eq (zip l1 l2) (zip l2 l1).
Parameter zip_associative: forall l1 l2 l3, 
  eqlistA Resource.eq (zip l1 (zip l2 l3)) (zip (zip l1 l2) l3).

Parameter zip_nil_nil: zip [] [] = [].
Parameter zip_nil_list: forall l, zip [] l = l.
Parameter zip_list_nil: forall l, zip l [] = l.

Record profile := mkProfile
  { ordered: list Resource.t; 
    separate: ResourceSet.t;
    validity: is_valid_aux ordered
  }.

Definition profile_eq (Pa: profile) (Pb: profile): Prop :=
  eqlistA Resource.eq (ordered Pa) (ordered Pb) /\
  ResourceSet.eq (separate Pa) (separate Pb).

Instance profile_eq_equiv: Equivalence profile_eq.
Proof.
  split;
  [ intros Pa; split; reflexivity
  | intros Pa Pb Hab; split; symmetry; apply Hab
  | intros Pa Pb Pc Hab Hac; split; [ transitivity (ordered Pb) | transitivity (separate Pb) ];
    apply Hab || apply Hac
  ].
Qed.

Definition profile_in (f: Resource.t) (P: profile): Prop :=
  InA Resource.eq f (ordered P) \/ ResourceSet.In f (separate P).

Lemma profile_in_eq: forall f Pa Pb, profile_in f Pa -> profile_eq Pa Pb -> profile_in f Pb.
Proof.
  intros f Pa Pb [Hin_ord | Hin_sep] [Heq_ord Heq_sep];
  [ left; rewrite <- Heq_ord; apply Hin_ord
  | right; rewrite <- Heq_sep; apply Hin_sep
  ].
Qed.

(* a profile is typable if all its messages are typable *)
Definition typable_profile (R: Repository.t) (P: profile): Prop :=
  forall f, profile_in f P -> typable R f.

Add Morphism typable_profile with signature Repository.eq ==> profile_eq ==> Logic.iff as typable_profile_m.
Proof.
  intros Ra Rb Hreq Pa Pb Heq; split; intros Htyp f H;
  [ rewrite <- Hreq; apply Htyp; apply profile_in_eq with Pb; [ apply H | symmetry; apply Heq ]
  | rewrite Hreq; apply Htyp; apply profile_in_eq with Pa; [ apply H | apply Heq ]
  ].
Qed.

Axiom typable_bottom: forall R, typable R (nd_bottom).

Axiom typable_and: forall R f1 f2, typable R f1 /\ typable R f2 -> typable R (nd_and f1 f2).

Axiom typable_or: forall R f1 f2, typable R f1 \/ typable R f2 -> typable R (nd_or f1 f2).

Axiom typable_impl: forall R f1 f2, (typable R f1 -> typable R f2) -> typable R (nd_impl f1 f2).

(* this is due to the fact that ~f is equivalent to f -> bot, and bot is typable everywhere *)
Lemma typable_not: forall R f, typable R (nd_not f).
Proof.
  intros; rewrite not_eq_bot; apply typable_impl; intros; apply typable_bottom.
Qed.

Axiom typable_read: forall R f, typable R f -> typable R (nd_read f).
Axiom typable_write: forall R f, typable R f -> typable R (nd_write f).
Axiom typable_trust: forall R f, typable R f -> typable R (nd_trust f).

Program Definition profile_merge Pa Pb: profile :=
  mkProfile (zip (ordered Pa) (ordered Pb)) (ResourceSet.union (separate Pa) (separate Pb)) _.
Obligation 1.
  apply is_valid_aux_zip;
  [ apply (validity Pa)
  | apply (validity Pb)
  ].
Qed.

Theorem remove_In_eq: forall (A: Type) (eq_dec: forall x y: A, {x = y} + {x <> y})
  (l: list A) (x: A), ~In x l -> remove eq_dec x l = l.
Proof.
  intros A eq_dec l x Hin; induction l;
  [ auto
  | simpl; destruct (eq_dec x a);
    [ absurd (In x (a :: l)); [ apply Hin | rewrite e; left; reflexivity ]
    | rewrite IHl;
      [ reflexivity
      | intros ABS; apply Hin; right; apply ABS
      ]
    ]
  ].
Qed.

Theorem remove_In_head: forall (A: Type) (eq_dec: forall x y: A, {x = y} + {x <> y})
  (h: A) (t: list A) (x: A), h <> x -> remove eq_dec x (h::t) = h::remove eq_dec x t.
Proof.
  intros A eq_dec h t x Heq; unfold remove; destruct (eq_dec x h);
  [ absurd (h = x); [ apply Heq | symmetry; apply e ]
  | reflexivity
  ].
Qed.

Theorem remove_head_eq: forall (A: Type) (eq_dec: forall x y: A, {x = y} + {x <> y})
  h t x, x = h -> remove eq_dec x (h::t) = remove eq_dec x t.
Proof.
  intros; unfold remove; destruct (eq_dec x h);
  [ reflexivity
  | absurd (x = h); assumption
  ].
Qed.

Program Definition profile_remove (f: Resource.t) (P: profile): profile :=
  mkProfile (List.remove resource_eq_dec f (ordered P)) (ResourceSet.remove f (separate P)) _.
Obligation 1.
  destruct P as [o s Ho]; simpl; functional induction (is_valid_aux o); try auto; simpl;
  [ destruct (resource_eq_dec f h); try auto
  | destruct (resource_eq_dec f h); destruct (resource_eq_dec f h');
    [ absurd (Resource.lt h h'); [ rewrite <- e; rewrite <- e0; intro H; apply (Resource.lt_irrefl f H) | apply (proj1 Ho) ]
    | rewrite remove_In_eq; [ apply (proj2 Ho) | intros ABS; apply (is_valid_aux_cons f (h'::t')); [ rewrite e; apply Ho | right; apply ABS ] ]
    | rewrite remove_In_eq; [ apply is_valid_aux_elide with h'; apply Ho | apply is_valid_aux_cons; rewrite e; apply (proj2 Ho) ]
    | split; [ apply (proj1 Ho) | rewrite remove_In_head in IHP; [ apply IHP; apply (proj2 Ho) | apply sym_not_eq; apply n0 ] ]
    ]
  ].
Qed.

Program Definition empty_profile: profile :=
  mkProfile [] ResourceSet.empty _.

Program Definition singleton_profile (f: Resource.t): profile :=
  mkProfile [f] ResourceSet.empty _.

Lemma empty_profile_typable: forall R,
  typable_profile R empty_profile.
Proof.
  intros R x [Hx_eq | Hx_in];
  [ inversion Hx_eq
  | absurd (ResourceSet.In x ResourceSet.empty); [intro; apply -> RSFacts.empty_iff; apply H | assumption ]
  ].
Qed.

Lemma singleton_profile_typable: forall R f,
  typable R f ->
  typable_profile R (singleton_profile f).
Proof.
  intros R f H x Hx_in. destruct Hx_in as [Hx_eq | Hx_in].
    inversion Hx_eq. rewrite H1. assumption.
    inversion H1.
    simpl in Hx_in.
    absurd (ResourceSet.In x ResourceSet.empty); [ intro; apply -> RSFacts.empty_iff; apply H0 | assumption ].
Qed.

Lemma profile_merge_empty_l: forall P,
  profile_eq (profile_merge empty_profile P) P.
Proof.
  intros [OP SP HOP]; unfold profile_eq; unfold profile_merge; simpl; rewrite zip_nil_list; rewrite empty_union_1.
    split; reflexivity. apply empty_is_empty_2. reflexivity.
Qed.

Lemma profile_merge_empty_r: forall P,
  profile_eq (profile_merge P empty_profile) P.
Proof.
  intros [OP SP HOP]; unfold profile_eq; unfold profile_merge; simpl; rewrite zip_list_nil; rewrite empty_union_2.
    split; reflexivity. apply empty_is_empty_2. reflexivity.
Qed.

Lemma profile_merge_self: forall P1, 
  profile_eq (profile_merge P1 P1) P1.
Proof.
  intros [OP1 SP1 HOP1]; unfold profile_eq; unfold profile_merge; simpl; split.
    rewrite zip_self. reflexivity.
    split; rewrite ResourceSet.union_spec; intros; [ destruct H; assumption | left; assumption ].
Qed.

Lemma profile_merge_comm: forall P1 P2,
  profile_eq (profile_merge P1 P2) (profile_merge P2 P1).
Proof.
  intros [OP1 SP1 HOP1] [OP2 SP2 HOP2]; unfold profile_eq; unfold profile_merge; simpl; split.
    apply zip_commutative.
    apply union_sym.
Qed.

Lemma profile_merge_assoc: forall P1 P2 P3,
  profile_eq (profile_merge P1 (profile_merge P2 P3)) (profile_merge (profile_merge P1 P2) P3).
Proof.
  intros [OP1 SP1 HOP1] [OP2 SP2 HOP2] [OP3 SP3 HOP3]; unfold profile_eq; unfold profile_merge; simpl; split.
    apply zip_associative.
    symmetry; apply union_assoc.
Qed.

Program Definition dep_extend (Pa: profile) (f: Resource.t | is_valid_aux (ordered Pa ++ [f])) :=
  mkProfile (ordered Pa ++ [f]) (separate Pa) _.

Program Definition indep_extend (Pa: profile) (f: Resource.t) :=
  mkProfile (ordered Pa) (ResourceSet.add f (separate Pa)) (validity Pa).

Section NDC_definition.
(* ndproof:
   hypotheses |- message
   (i.e. NDProof P m is a proof of P |- m, where m is a message.)
   The ND calculus
 *)

Inductive NDProof: profile -> Resource.t -> Prop :=
  (* operational rules *)
  | nd_atom_rule: forall Ra Rb Pa Pb f, typable_profile Ra Pa -> typable_profile Rb Pb ->
      repository_leq Ra Rb -> typable Rb f -> profile_in f Pb ->
      NDProof (profile_merge Pa Pb) f
  | nd_bottom_rule: forall Ra Pa Rb f, typable_profile Ra Pa ->
      typable Rb f ->
      NDProof Pa nd_bottom ->
      NDProof Pa f
  | nd_and_intro: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_leq Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof Pa f1 -> NDProof Pb f2 ->
      NDProof (profile_merge Pa Pb) (nd_and f1 f2)
  | nd_and_elim_l: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_leq Ra Rb ->
      typable Ra f1 -> typable Rb f2 -> 
      NDProof (profile_merge Pa Pb) (nd_and f1 f2) ->
      NDProof (profile_merge Pa Pb) f1
  | nd_and_elim_r: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_leq Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof (profile_merge Pa Pb) (nd_and f1 f2) ->
      NDProof (profile_merge Pa Pb) f2
  | nd_or_intro_l: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_leq Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof (profile_merge Pa Pb) f1 ->
      NDProof (profile_merge Pa Pb) (nd_or f1 f2)
  | nd_or_intro_r: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_leq Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof (profile_merge Pa Pb) f2 ->
      NDProof (profile_merge Pa Pb) (nd_or f1 f2)
  | nd_or_elim: forall Ra Rb Rc Pa Pb f1 f2 g, typable_profile Ra Pa -> typable_profile Rb Pb ->
      repository_leq Ra Rb ->
      typable Ra f1 -> typable Rb f2 -> typable Rc g ->
      NDProof (profile_merge Pa Pb) (nd_or f1 f2) ->
      NDProof (singleton_profile f1) g ->
      NDProof (singleton_profile f2) g ->
      NDProof (profile_merge Pa Pb) g
  | nd_impl_intro: forall Ra Rb Rc Pa f1 f2, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Rb f1 -> typable Rc f2 ->
      NDProof (profile_merge Pa (singleton_profile f1)) f2 ->
      NDProof Pa (nd_impl f1 f2)
  | nd_impl_elim: forall Ra Rb Rc Pa  f1 f2, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Rb f1 -> typable Rc f2 ->
      NDProof Pa (nd_impl f1 f2) ->
      NDProof Pa f1 ->
      NDProof (profile_merge Pa (singleton_profile f1)) f2
  (* access rules *)
  | nd_read_distrib: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_not (nd_read f)) ->
      NDProof Pa (nd_read (nd_not f))
  | nd_write_distrib: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_not (nd_write f)) ->
      NDProof Pa (nd_write (nd_not f))
  | nd_trust_distrib: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_not (nd_trust f)) ->
      NDProof Pa (nd_trust (nd_not f))
  | nd_read_intro: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_leq Ra Rb ->
      NDProof Pa (nd_read f)
  | nd_trust_intro: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_read f) ->
      NDProof Pa (nd_trust f)
  | nd_write_intro: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_read f) ->
      NDProof Pa (nd_trust f) ->
      NDProof Pa (nd_write f)
  | nd_exec: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_write f) ->
      NDProof Pa f
  | nd_dtrust_intro: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Rb f ->
      NDProof Pa (nd_impl (nd_read f) nd_bottom) ->
      NDProof Pa (nd_not (nd_trust f))
  | nd_dtrust_elim: forall Ra Rb Rc Pa f1 f2, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Rb f1 -> typable Rc f2 ->
      NDProof Pa (nd_not (nd_trust f1)) ->
      NDProof Pa (nd_impl (nd_not (nd_trust f1)) f2) ->
      NDProof Pa (nd_write f2)
  | nd_mtrust_intro: forall Ra Rb Pa f1 f2, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof Pa (nd_impl (nd_read f2) nd_bottom) -> is_valid_aux (List.remove resource_eq_dec f1 (ordered Pa)) ->
      NDProof (profile_merge (profile_remove f1 Pa) (singleton_profile f2)) (nd_not (nd_trust f1))
  | nd_mtrust_elim: forall Ra Rb Rc Pa Pc f1 f2, typable_profile Ra Pa -> typable_profile Rc Pc -> repository_leq Ra Rb -> repository_leq Rc Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof (profile_merge (profile_remove f1 Pa) (singleton_profile f2)) (nd_not (nd_trust f1)) -> is_valid_aux (ordered Pc ++ [f2]) ->
      NDProof (profile_merge (profile_remove f1 Pa) Pc) (nd_trust f2)
  (* structural rules *)
  | nd_weakening: forall Ra Rb Pa f1 f2, typable_profile Ra Pa -> repository_leq Ra Rb ->
      typable Ra f1 -> typable Rb f2 ->
      NDProof Pa (nd_write f1) ->
      NDProof Pa (nd_trust f2) ->
      NDProof (profile_merge Pa (singleton_profile f2)) (nd_write f1)
	(* contraction rule covered by profile things *)
  (* exchange rule covered by set stuff. *)
  | nd_cut: forall Ra Rb Pa Pb f1 f2, typable_profile Ra Pa -> typable_profile Rb Pb -> repository_leq Ra Rb ->
      typable Rb f1 -> typable Rb f2 ->
      NDProof Pa f1 ->
      NDProof (profile_merge Pb (singleton_profile f1)) f2 ->
      NDProof (profile_merge Pa Pb) f2.

Axiom profile_extension: forall Ra Rb Pa Pb f g, 
	typable_profile Ra Pa -> typable_profile Rb Pb -> repository_leq Ra Rb ->
	typable Ra f -> typable Rb g ->
  NDProof (profile_merge Pa (singleton_profile f)) g ->
	is_valid_aux (ordered Pa ++ [f; g]).

(* Properties of dominance *)
Axiom typable_1_read: forall Ra Pa f, typable_profile Ra Pa ->
  typable Ra f -> NDProof Pa (nd_read f).
Axiom typable_1_write: forall Ra Pa f, typable_profile Ra Pa ->
  typable Ra f -> NDProof Pa (nd_write f).
Axiom typable_2_read: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_leq Ra Rb ->
  typable Rb f -> NDProof Pa (nd_read f).
Axiom typable_3_write: forall Ra Rb Pa f, typable_profile Ra Pa -> repository_leq Ra Rb ->
  typable Rb f ->
  (NDProof Pa (nd_write f) <->
     NDProof Pa (nd_read f) /\
     NDProof Pa (nd_trust f)).

Axiom proof_eq: forall P1 P2 f1 f2, profile_eq P1 P2 -> Resource.eq f1 f2 ->
  NDProof P1 f1 -> NDProof P2 f2.

End NDC_definition.

Add Morphism NDProof with signature profile_eq ==> Resource.eq ==> Logic.iff as ndproof_m.
Proof.
  intros; split; intros;
  [ apply proof_eq with x x0
  | apply proof_eq with y y0; try symmetry
  ]; assumption.
Qed.
