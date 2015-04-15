Require Import SecureND.
Require Import Program.

Variable Ra: Repository.t.
Variable Rb: {x: Repository.t | Repository.lt Ra x}.

Variable Pa: {x | typable_profile Ra x}.
Variable Pb: {x | typable_profile (`Rb) x}.

(* The TrMinInst function. This has to be defined in this way,
 * because it is not possible to eliminate a Prop (which is NDProof) to
 * result in a Set (nat). 
 *)

Parameter TrMinInst: forall P f, NDProof Ra Rb Pa Pb P f -> nat.

Axiom TMI_atom_mess: forall b Hwf Ht, 
      TrMinInst _ _ (nd_atom_mess Ra Rb Pa Pb b Hwf Ht) = 0.
Axiom TMI_and_intro: forall n m f1 f2 D1 D2 Ht1 Ht2,
      TrMinInst _ _ D1 = n -> TrMinInst _ _ D2 = m ->
      TrMinInst _ _ (nd_and_intro Ra Rb Pa Pb f1 f2 D1 Ht1 D2 Ht2) = n + m.  
Axiom TMI_and_elim_l: forall n f1 f2 D Ht1 Ht2,
      TrMinInst _ _ D = n ->
      TrMinInst _ _ (nd_and_elim_l Ra Rb Pa Pb f1 f2 D Ht1 Ht2) = n.
Axiom TMI_and_elim_r: forall n f1 f2 D Ht1 Ht2,
      TrMinInst _ _ D = n ->
      TrMinInst _ _ (nd_and_elim_r Ra Rb Pa Pb f1 f2 D Ht1 Ht2) = n.
Axiom TMI_or_intro_l: forall n f1 f2 D1 Ht1 Ht2,
      TrMinInst _ _ D1 = n ->
      TrMinInst _ _ (nd_or_intro_l Ra Rb Pa Pb f1 f2 D1 Ht1 Ht2) = n.
Axiom TMI_or_intro_r: forall n f1 f2 D2 Ht1 Ht2,
      TrMinInst _ _ D2 = n ->
      TrMinInst _ _ (nd_or_intro_r Ra Rb Pa Pb f1 f2 D2 Ht1 Ht2) = n.
Axiom TMI_or_elim: forall p n m f f1 f2 D D1 D2 Ht Ht1 Ht2,
      TrMinInst _ _ D = p -> TrMinInst _ _ D1 = n -> TrMinInst _ _ D2 = m ->
      TrMinInst _ _ (nd_or_elim Ra Rb Pa Pb f f1 f2 D Ht Ht1 D1 D2 Ht2) = p + (max n m).
Axiom TMI_nd_impl_intro: forall n f1 f2 D Ht1 Ht2,
      TrMinInst _ _ D = n ->
      TrMinInst _ _ (nd_impl_intro Ra Rb Pa Pb f1 f2 D Ht1 Ht2) = n.
Axiom TMI_impl_elim: forall n m f1 f2 D1 D2 Ht1 Ht2,
      TrMinInst _ _ D1 = n -> TrMinInst _ _ D2 = m ->
      TrMinInst _ _ (nd_impl_elim Ra Rb Pa Pb f1 f2 D1 Ht1 Ht2 D2) = min n m.
Axiom TMI_read_intro: forall f Hwf Ht,
      TrMinInst _ _ (nd_read_intro Ra Rb Pa Pb f Hwf Ht) = 0.
Axiom TMI_trust_intro: forall n f D Hwf,
      TrMinInst _ _ D = n ->
      TrMinInst _ _ (nd_trust_intro Ra Rb Pa Pb f D Hwf) = n + 1.
Axiom TMI_write_intro: forall n m f D1 D2 Ht,
      TrMinInst _ _ D1 = n -> TrMinInst _ _ D2 = m ->
      TrMinInst _ _ (nd_write_intro Ra Rb Pa Pb f D1 D2 Ht) = n + m.

