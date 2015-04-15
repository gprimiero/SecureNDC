Require Import SecureND.
Require Import List.
Require Import Program.

Variable Ra: Repository.t.
Variable Rb: {x: Repository.t | Repository.lt Ra x}.

Variable Pa: {x | typable_profile Ra x}.
Variable Pb: {x | typable_profile (`Rb) x}.

(* down  cut *)    
Inductive NDDCProof: list P.t -> P.E.t -> Prop :=
  | dc_normal_proof: forall D f, NDProof Ra Rb Pa Pb D f -> NDDCProof D f
  | down_cut: forall f x,
      typable (`Rb) f -> typable (`Rb) x ->
      NDDCProof (`Pa::nil) f -> NDDCProof (P.add f (`Pb)::nil) x ->
      NDDCProof (`Pa::`Pb::nil) x.

Theorem down_cut_elimination: forall P f,
  NDDCProof P f -> NDProof Ra Rb Pa Pb P f.
Proof.
  intros G f Hder; induction Hder;
  [ apply H
  | apply nd_atom_mess;
    [ intros EMPTY; apply EMPTY with f; apply -> proof_in; apply IHHder1
    | apply H0
    ] 
  ].
Qed.
    
(* up cut *)     
Inductive NDUCProof: list P.t -> P.E.t -> Prop :=
  | uc_normal_proof: forall P f, NDProof Ra Rb Pa Pb P f -> NDUCProof P f
  | up1_cut: forall f x,
      typable Ra f -> typable (`Rb) x -> P.In f (`Pa) ->
      NDUCProof (`Pa::nil) f -> NDUCProof (`Pb::singleton f::nil) x ->
      NDUCProof (`Pa::`Pb::nil) x
  | up2_cut: forall f x,
      typable (`Rb) f -> typable Ra x -> P.In f (`Pb) ->
      NDUCProof (`Pb::nil) f -> NDUCProof (`Pa::singleton f::nil) x ->
      NDUCProof (`Pb::`Pa::nil) x.

Theorem up_cut_elimination: forall P f,
  NDUCProof P f -> NDProof Ra Rb Pa Pb P f.
Proof.
  intros; induction H;
  [ apply H
  | apply nd_atom_mess;
    [ intros EMPTY; apply EMPTY with f; apply -> proof_in; apply IHNDUCProof1
    | apply H0
    ]
  | destruct Pa as [Pa HPa]; induction Pa using set_induction;
    [ apply add_empty_protocol;
      [
      | apply H4
      ]
    |
    ]
  ].
 
 