Section CC2.

Inductive EE : Set :=
  | F : EE
  | U : EE -> EE
  | D : EE -> EE -> EE 
.

Theorem induction_EE : forall P : EE -> Prop,
     P(F)
  -> (forall e: EE, P e -> P (U e))
  -> (forall e1 e2:EE, P e1 -> P e2 -> P (D e1 e2))
  -> forall e :EE, P e.
Proof.
intros; apply EE_ind; auto.
Restart.
intros P HF FU HD e. induction e; auto.
Qed.

Context (I J: Prop).
Context (H : I -> J). 

Lemma exo : (I \/ J) -> J.
Proof.
intros H1.
destruct H1.
 - apply H. exact H0.
 - exact H0.
Qed.

End CC2.

Check exo.
(* exo : forall A B : Prop, A \/ B -> (A -> B) -> B *)