Require Import SecureND.
Require Import Program.

Variable Ra Rb Rn: Repository.t.
Axiom HRb: repository_lt Ra Rb.
Axiom HRn: repository_lt Rb Rn.

Variable Pa Pb: list Resource.t.
Axiom HPa: typable_profile Ra Pa.
Axiom HPb: typable_profile Rb Pb.

Lemma distrust: forall f g, typable Rb f -> typable Rn g ->
  NDProof Pa (nd_impl (nd_not (nd_trust f)) g) <->
  NDProof (Pa ++ [nd_not f]) g.
Proof.
  intros f g Hf Hg; split; intros H.
  apply nd_impl_elim with Ra Rb Rn; [ apply HPa | apply HRb | apply typable_not | apply Hg | | ].
    [
    | apply nd_exec with Ra Rb; [ apply HPa | apply HRb | apply typable_not |
        apply nd_write_intro with Ra Rb; [ apply HPa | apply HRb | apply typable_not |
          apply nd_read_intro with Ra Rb; [ apply HPa | apply HRb | apply HPa | apply typable_not ] |
          apply nd_trust_distrib with Ra Rb; [ apply HPa | apply HRb | apply Hf | apply Hf ]
        ]
      ]
    ]
  |
  ].
  Focus 2. apply nd_write_intro.
    
Qed.

      apply nd_impl_intro with Ra Rb Rn; [ apply HPa | apply HRb | apply typable_not | apply Hg | ].
        apply nd_cut with Ra Rn (nd_impl (nd_not (nd_trust f)) g); [ apply HPa |
          intros x Hx; destruct Hx as [ eq | false ]; [ rewrite <- eq; apply typable_not | contradiction ]
        | apply repository_lt_trans with Rb; [ apply HRb| apply HRn ] | apply typable_impl; intros _; apply Hg | apply Hg
        | apply H | |].
        apply nd_impl_elim with Ra Rb Rn; [ apply HPa | apply HRb | apply typable_not | apply Hg | | ].
          
      apply HRb.
      apply typable_not.
      apply Hg.
      apply nd_impl_intro with Ra Rb Rn. apply HPa. apply HRb. apply typable_not. apply Hg.
apply nd_exec with Ra Rn.
        apply HPa.
        apply repository_lt_trans with Rb; [ apply HRb | apply HRn ].
        apply typable_impl. intros _; apply Hg.
        apply nd_write_intro with Ra Rn. 
          apply HPa.
          apply repository_lt_trans with Rb; [ apply HRb | apply HRn ].
          apply typable_impl. intros _; apply Hg.
          apply nd_read_intro with Ra Rn.
            apply HPa.
            apply repository_lt_trans with Rb; [ apply HRb | apply HRn ].
            apply HPa.
            apply typable_impl; intros _; apply Hg.
          
          
  
