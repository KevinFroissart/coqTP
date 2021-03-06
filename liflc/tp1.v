
(* On introduit les variables propositionnelles avec lesquelles 
   on va travailler par la suite *)
Context (P Q R A Z J F M S T: Prop).

(**********************************************************************)
(* Exercice 1 LA FLÈCHE  ***********************)
(* - axiome : assumption
   - introduction de la flèche : intro [nom qu'on donne à l'hypothèse] 
   - élimination de la flèche : apply [nom de l'hypothèse utilisée] *)
Theorem exercice_1a: P -> (P -> Q) -> Q.
Proof.
  intro Hp.
  intro Hpq.
  apply Hpq.
  assumption.
Qed.


Theorem exercice_1b: (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intro Hpq.
  intro Hqr.
  intro Hp.
  apply Hqr.
  apply Hpq.
  assumption.
Qed.

(* Exercice 2 LE ET  ***********************)
(* Une variante de la question précédente avec /\ *)
(* - décomposition du /\ en hypothèse : destruct [nom de l'hypothèse avec /\]
*)
Theorem exercice_2a: (P -> Q) /\ (Q -> R) -> (P -> R).
Proof.
  intro H.
  intro HP.
  destruct H as [H1 H2].
  apply H2.
  apply H1.
  assumption.
Qed.

(* - introduction du /\ : split *)
(* On obtient bien deux sous-buts *)
Theorem exercice_2b : P -> Q -> P /\ Q.
Proof.
  intro Hp.
  intro Hq.
  split.
  - apply Hp.
  - apply Hq.
Qed.
  
(* Exercice 3 LE OU  ***********************)
(* introduction du ou :
   - depuis la droite : right
   - depuis la gauche : left

   decomposition du \/ en hypothèse : destruct *)

Theorem exercice_3a: (P \/ Q) -> (Q \/ P).
Proof.
  intro Hpq.
  destruct Hpq.
  - right.
    assumption.
  - left.
    assumption.
Qed.

(* ---------------------------------------------------------------------*)


(* zéro constructeur *)
Print False. 
(* un seul constructeur car une seule règle d'intro *)
Print and.
(* deux constructeurs car deux règles d'intro*)
Print or.  

(* destruct donne bien un sous but par constructeur *)
(* On remarque que comme False n'a aucun constructeur : le destruct
résoud le but *)
Theorem ex_falso_quodlibet : False ->  P.
Proof.
intros H.
destruct H.
Qed.

(** un peu difficile **)
(* Plus généralement, la tactique exfalso remplace tout but par False. *)
(* Si on peut déduire False des hypothèses, c'est alors gagné ! *)

Theorem ex_falso_quodlibet_Q : (A -> False) -> A -> (P \/ (Q -> Z /\ J) -> F).
Proof.
  intro hafalse.
  intro ha.
  (* ces hypothèses permettent clairement de produire False *)
  (* on simplifie tout puisque le but ne sert plus à rien *)
  exfalso.
  (* et on produit False *)
  apply hafalse.
  assumption.
Qed.
  

(* À partir de maintenant on peut penser à nommer les hypothèses qui
apparaissent dans les destruct avec "as" et suivant le nombre de sous-buts *)
(* ---------------------------------------------------------------------*)


(* Exercice 4 PREMIÈRE MODÉLISATION  ***********************)
(* Modéliser l'exercice de TD "Zoé va à Paris", prouver que Zoé va à Paris *)
(* - introduction du /\ : split
*)
Theorem zoe_va_a_paris : (A /\ J -> Z) -> (J -> A) -> (J \/ Z) -> Z.
Proof.
  intro Hajz.
  intro Hja.
  intro Hjz.
  destruct Hjz.  
  - apply Hajz.
    split.
    + apply Hja. assumption.
    + assumption.
  - assumption.
Qed.

Theorem zoe_va_a_paris' : (A /\ J -> Z) /\ (J -> A) /\ (J \/ Z) -> Z.
Proof.
  intro.
  destruct H.
  destruct H0.
  destruct H1.
  - apply H.
    split.
    + apply H0. assumption.
    + assumption.
  - assumption.
Qed.

(* Exercice 5 LE NOT *************************)

(* - la notation not : unfold not
   - la notation not en hypothèse : unfold not in [nom de l'hypothèse avec ~]
*)
Theorem exercice_5a : (~P \/ ~Q) -> ~(P /\ Q).
Proof.
  intro Hnpnq.
  unfold not in Hnpnq.
  intro.
  destruct Hnpnq.
  - destruct H. apply H0. assumption.
  - destruct H. apply H0. assumption.
Qed.

(* Si on a toto et ~toto dans les hypothèses, alors le but est résolu avec "contradiction." *)

Theorem exercice_5b : P -> ~P -> Q.
Proof.
  intro hp.
  intro hnp.
  contradiction.
Qed.

(**********************************************************************)
(* Exercice 6 LE TIERS-EXCLU *)

(* On introduit la règle de tiers-exclu. *)
Context (Tiers_exclus: forall X: Prop, X \/ ~X).

(* Pour l'utiliser, c'est-à-dire pour avoir deux sous buts, un avec toto en hypothèse, l'autre avec ~toto, on invoquera :
   destruct (Tiers_exclus toto).
*)


(* Deuxième modélisation *)
(* Modéliser l'exercice de TD "Frodon va au Mordor", prouver que Frodon est triste
- Si Frodon ne va pas au Mordor, Sauron prend le pouvoir ; (~M -> S)
- Si Sauron prend le pouvoir, Frodon est triste ; (S -> T)
- Si Frodon va au Mordor, il ne possède pas l'anneau ; (M -> ~A)
- Si Frodon ne possède pas l'anneau, il est triste ; (~A -> T)
*)
Theorem exercice_6b : (~M -> S) -> (S -> T) -> (M -> ~A) -> (~A -> T) -> T.
Proof.
intros H1 H2 H3 H4.
(*
supposons {H1 H2 H3 H4} et prouvons que T
- soit I(M)=1 comme (M -> ~A)=1 alors I(~A)=1
  comme I(~A)=1, comme I(~A -> T)=1 alors I(T)=1
- soit I(M)=0 comme I(~M -> S)=1 alors I(S)=1
  comme I(S)=1, comme I(S -> T)=1 alors I(T)=1
Dans tous les cas T est vrai Qed.
*)
assert (M \/ ~M).
apply (Tiers_exclus M).
destruct H.
- apply H4.
  apply H3.
  assumption.
- apply H2.
  apply H1.
  assumption.
Qed.


(* Quid de ~~P et P ? *)
Theorem exercice_6c: (~~P -> P) /\ (P -> ~~P).
(* Pour l'un des deux sens on aura besoin du tiers-exclu et, en remarquant qu'on peut déduire False des hypothèses, de la simplification "exfalso". *)
Proof.
  split.
  intros.
  - unfold not in H.
    destruct(Tiers_exclus P).
    assumption.
    exfalso.
    unfold not in H0.
    apply H.
    assumption.
  - intros H.
    intros H1.
    unfold not in H1.
    apply H1.
    assumption.
Qed.

Theorem execirce_bonus: (~~~P -> ~P).
Proof.
  intros.
  unfold not in H.
  unfold not.
  intros H1.
  apply H.
  intros.
  apply H0.
  assumption.
Qed.

Definition si_cest_vrai_cest_pas_faux := P -> ~~P.

Theorem scvcpf: si_cest_vrai_cest_pas_faux /\ (~~P -> P).
Proof.
split.
- unfold si_cest_vrai_cest_pas_faux.
  intros H2.
  intros H3.
  apply H3.
  assumption.
- intros H. 
  assert (P \/ ~P).
  exact (Tiers_exclus P).
  destruct H0.
  * assumption.
  * exfalso. apply H. assumption.
Qed.
  














