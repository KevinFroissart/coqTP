Require Import String.
Require Import List.
Import ListNotations.

Section TD6.

(****************************************************************************************
On va montrer que ce qu'on a fait dans le TD6 sur le mini language est faisable en coq :
 - on représente le langage par un inductif EX
 - on écrit un petit interpréteur comme on le ferait en OCaml ou Haskell
 - on représente la spécification du langage par un inductif, qui mime fidèlement les
   règles d'inférences données
 - on montre que notre interpréteur est fidèle pour la spécification
 - on montre quelques propriétés (théorème) du langage
*****************************************************************************************)


(***************** Un premier langage EX1, sans definition de variables *****************)
(*****************         c'est un cas simplifié, pour l'exemple       *****************)

(* Le langage, ici sans définition de variable 'Let'.
   Technique dite du 'shallow embedding' : un langage c'est un inductive produit
    à partir de sa grammaire *)
Inductive EX1 : Set :=
  | Var1 (x:string): EX1
  | Cte1 (n:nat): EX1
  | Plus1 (e1 e2: EX1) : EX1
  | Mult1 (e1 e2: EX1) : EX1
.

(* Pour évaluer, on a besoin de connaitre la valeur des variables, c'est le contexte *)
(* On triche un peu : on dit que le contexte est uen fonction TOTALE, qui à chaque 
   variable nous donne sa valeur en "nat". On fera  *)
Definition Ctxt1 := string -> nat.

(* L'interpréteur : donnez moi un contexte, une expression et je vous calcule sa valeur "nat" *)
Fixpoint eval1 (ctxt : Ctxt1) (e:EX1) : nat :=
match e with
 | Var1 x       => ctxt x  (* on lit la valeur de la variable dans le contexte *)
 | Cte1 n       => n       (* une constante est un entier, donc un "nat" *)
 | Plus1 e1 e2  => (eval1 ctxt e1) + (eval1 ctxt e2)   (* le Plus du langage c'est l'addition *)
 | Mult1 e1 e2  => (eval1 ctxt e1) * (eval1 ctxt e2)   (* le Mult du langage c'est la multiplication *)
end.

(* Le premier exemple du TD6 *)
Definition ex1 := Mult1 (Plus1 (Cte1 1) (Cte1 2)) (Cte1 3).
(* on suppose 'magiquement' que chaque variable vaut 0, l'évaluation donne 9 *)
Goal (eval1 (fun x => 0) ex1) = 9.
Proof.
auto.
Qed.

(* un autre exemple avec une variable libre 'x' et un contexte ou tout vaut 9 *)
Definition ex1' := Mult1 (Plus1 (Cte1 1) (Var1 "x")) (Cte1 3).
Goal (eval1 (fun x => 9) ex1') = 30.
Proof.
auto.
Qed.


(***************** Un second langage EX2, AVEC definition de variables ******************)
(*****************         c'est un cas simplifié, sans fonctions       *****************)

(* Comme "EX1", mais avec un cas de plus pour "Let" *)
Inductive EX2 : Set :=
  | Var2 (x:string): EX2
  | Cte2 (n:nat): EX2
  | Plus2 (e1 e2: EX2) : EX2
  | Mult2 (e1 e2: EX2) : EX2
  | Let2 (x:string) (e1:EX2) (e2:EX2) : EX2
.

(* maintenant le contexte va être une liste de paires (variable, valeur), et
  l'interpréteur peut 'planter' si on utilise une variable indéfinie. *)
Definition Ctxt2 := list (string * nat).

(* On cherche dans la liste de paire, voir le TP LIFLF *)
Fixpoint lookup (ctxt : Ctxt2) (x:string) : option nat :=
match ctxt with
 | []           => None
 | (v,n)::ctxt' => if (eqb x v) then Some n else (lookup ctxt' x)
end.

(* une petite fonction outil qui permet de transformer une fonction totale sur les 
   "nat" en une fonction qui prend des "option nat" et renvoie un "option nat" *)
Definition lift2 (f : nat -> nat -> nat) (n1 n2:option nat) : option nat :=
match n1, n2 with
  | Some v1, Some v2 => Some (f v1 v2)
  | _, _             => None
end.

(* L'interpréteur du nouveau langage *)
Fixpoint eval2 (ctxt : Ctxt2) (e:EX2) : option nat :=
match e with
 | Var2 x       => lookup ctxt x
 | Cte2 n       => Some n
 | Plus2 e1 e2  => (lift2 plus) (eval2 ctxt e1) (eval2 ctxt e2)
 | Mult2 e1 e2  => (lift2 mult) (eval2 ctxt e1) (eval2 ctxt e2)
 | Let2 x e1 e2 => match eval2 ctxt e1 with 
                    | None   => None
                    | Some v => let ctxt' := (x,v)::ctxt in eval2 ctxt' e2
                   end
end.

Goal eval2 [] (Var2 "x") = None.
Proof.
auto.
Qed.

Definition ex2 := Let2 ("n") (Cte2 2) (Let2 "m"  (Plus2 (Var2 "n") (Cte2 1))  (Plus2 (Var2 "m") (Var2 "n")) ).
Definition ex3 := Let2 ("n") (Cte2 2) (Plus2 (Let2 "n" (Plus2 (Var2 "n") (Cte2 2)) (Var2 "n")) (Var2 "n")).

Goal eval2 [] ex2 = Some 5.
Proof.
auto.
Qed.

Goal eval2 [] ex3 = Some 6.
Proof.
auto.
Qed.

(***************** On va maitenant modéliser la sépcification de EX2,  ******************)
(*****************      c'est-à-dire les règles de l'évaluation       *****************)

(* Correspond directement aux règles de la feuille de TD *)
Inductive Inter (ctxt : Ctxt2) : EX2 -> nat -> Prop :=
  IVar2  : forall x v, (lookup ctxt x) = Some v -> Inter ctxt (Var2 x ) v
| ICte2  : forall n, Inter ctxt (Cte2 n) n
| IPlus2 : forall e1 v1 e2 v2, (Inter ctxt e1 v1) -> (Inter ctxt e2 v2) -> Inter ctxt (Plus2 e1 e2) (v1 + v2)
| IMult2 : forall e1 v1 e2 v2, (Inter ctxt e1 v1) -> (Inter ctxt e2 v2) -> Inter ctxt (Mult2 e1 e2) (v1 * v2)
| ILet2  : forall e1 v1 x e2 v2, (Inter ctxt e1 v1) -> (Inter ((x,v1)::ctxt) e2 v2) -> Inter ctxt (Let2 x e1 e2) v2
.

(* on va prendre un notation pour ressembler au TD *)
Notation "ctxt '|-' e '~>' v"       := (Inter ctxt e v)(at level 40).

(* là, on fait en coq, l'équivalent de l'arbre de dérivation fait en TD *)
(* ca suit directement la dérivation, mais c'est un peu laborieux car on
   doit expliciter les sommes (resp. produits) pour appliquer IPlus2
   (resp. IMult2). On doit aussi utilise "apply ... with" pour expliciter
    les variables qui apparaissent à gauche du constructeur mais pas à droite *)
(* NB : on utilise la tactique "constructor" qui recherche automatiquement
   le constructeur applicable *)
Goal [] |- ex2 ~> 5.
Proof.
apply ILet2 with (v1 := 2). 
* constructor.
* apply ILet2 with (v1 := 3).
  - assert (3 = 2 + 1) by auto with arith.
    rewrite H; repeat constructor; auto.
  - assert (5 = 3 + 2) by auto with arith.
    rewrite H; repeat constructor; auto.
Qed.

(* là, on fait en coq, l'équivalent de l'arbre de dérivation fait en TD *)
Goal [] |- ex3 ~> 6.
Proof.
apply ILet2 with (v1 := 2); try constructor.
assert (6 = 4 + 2) as H1 by auto with arith. rewrite H1.
constructor; try constructor; auto.
assert (4 = 2 + 2) as H2 by auto with arith. rewrite H2.
apply ILet2 with (v1 := 4).
- rewrite H2.  constructor; constructor; auto.
- constructor. trivial.
Qed.

(**************** On a maintenant DEUX façons de donner du sens à EX2  ******************)
(********* la spect "Inter" et l'implem "eval2" : montrons qu'elles coincident  *********)


(* On va prouver notre théorème de correction, la 'coincidence' : notre interpréteur
   retourne une valeur **si et seulement si** la spécification nous donne cette valeur *)

(* Un lemme technique : si on a évalué "f", on peut retrouver les valeurs utilisées *)
(* c'est facile si on pense à utiliser "destruct ... eqn:H" pour mémoriser le cas
    qu'on a analysé avec "destruct" *)
Lemma plus_inv : forall f ctxt e1 e2 v, (lift2 f) (eval2 ctxt e1) (eval2 ctxt e2) = Some v -> exists v1 v2, (eval2 ctxt e1) = Some v1 /\ (eval2 ctxt e2) = Some v2 /\ f v1 v2 = v.
Proof.
intros.
destruct (eval2 ctxt e1) as [v1 |] eqn:H1; destruct (eval2 ctxt e2) as [v2 |] eqn:H2.
- exists v1, v2. simpl in H. injection H; intros. repeat split; auto.
- simpl in H; discriminate.
- simpl in H; discriminate.
- simpl in H; discriminate.
Qed.

(* Le premier sens : si on évalue, alors la valeur est correcte *)
Lemma eval_is_sound : forall e ctxt v, eval2 ctxt e = Some v -> (ctxt |- e ~> v).
Proof.
induction e; intros.
- (* cas e = Var2 x *)
  constructor; trivial.
- (* cas e = Cte2 n *)
  injection H; intros; subst n; constructor; trivial.
- (* cas e = e1 + e2 *)
  apply plus_inv in H. destruct H as [v1 [v2 [H1 [H2 H]]]].
  rewrite <- H. constructor; auto.
- (* cas e = e1 * e2, idem précédent *)
  apply plus_inv in H. destruct H as [v1 [v2 [H1 [H2 H]]]].
  rewrite <- H. constructor; auto.
- (* cas e = (let x = e1 in e2) *)
  simpl in H. 
  (* analyse par cas sur l'évaluation de e1 *)
  destruct (eval2 ctxt e1) eqn:He1.
  * apply ILet2 with (v1 := n); auto.
  * discriminate.
Qed.


(* Le second sens, plus facile ici c'est une induction directe :
   si une valeur est prévue, l'évaluateur donne bien celle-ci *)
Lemma eval_is_complete : forall e ctxt v, (ctxt |- e ~> v) -> eval2 ctxt e = Some v.
Proof.
(* noter ici : par induction sur "H", pas sur "e" *)
intros. induction H; simpl.
- trivial.
- trivial.
- rewrite IHInter1, IHInter2. trivial.
- rewrite IHInter1, IHInter2. trivial.
- rewrite IHInter1. rewrite IHInter2. trivial.
Qed.

(* Le théorème principal *)
Theorem eval_is_correct : forall e ctxt v, (ctxt |- e ~> v) <-> eval2 ctxt e = Some v.
Proof.
split; auto using eval_is_complete, eval_is_sound.
Qed.

(* Donc maintenant, on a une méthode beaucoup plus simple pour prouver
   des buts de la forme "ctxt |- e ~> v" : on calcule avec "eval2" *)
(* C'est une technique générale en Coq, appellée 'reflexion' *)
Goal [] |- ex2 ~> 5.
Proof.
apply eval_is_correct.
trivial.
Qed.
Goal [] |- ex3 ~> 6.
Proof.
apply eval_is_correct.
trivial.
Qed.


(********************* Prouver d'auters choses sur nos programmes  **********************)
(******** on voit que ça 'plante' en cas d'utilsiation d'un variable indéfinie  *********)
(************* c'est vrai et en un sens c'est 'la seule façon de planter'       *********)


(* Maintenant, on va prouver que l'évaluation 'échoue' en renvoyant None ssi
   le programme utilise une variable indéfinie *)

(* Une conversion de "option" dans bool *)
Definition is_none {A:Type} (x : option A) : bool :=
match x with
 | None => true
 | _    => false
end.

(* et son lemme d'inversion *)
Lemma is_none_inv : forall A (x:option A), is_none x = true <-> x = None.
Proof.
destruct x; split; intros H; simpl in H; auto; discriminate.
Qed.

(* On commence par la fonction qui dit si une variable "v" est libre *)
(* C'est calculatoire, donc on pourra vérifier 'sans l'exécuter' si un programme plante *)
Fixpoint free (ctxt : Ctxt2) (e:EX2) (v:string) : bool :=
match e with
 | Var2 x => (eqb x v) && (is_none (lookup ctxt x))
 | Cte2 n => false
 | Plus2 e1 e2 => (free ctxt e1 v) || (free ctxt e2 v)
 | Mult2 e1 e2 => (free ctxt e1 v) || (free ctxt e2 v)
 | Let2 x e1 e2 => (free ctxt e1 v) || (negb (eqb x v) && (free ctxt e2 v)) 
end.

(****** des exemples, car cette définition n'est pas évidente ******)

Goal (free [] ex2 "x") = false.
Proof.
trivial.
Qed.

Goal (free [] ex2 "n") = false.
Proof.
trivial.
Qed.

(* un cas dur où "n" est libre dans "e1" mais liée dans "e2" *)
Definition ex_free x := Let2 "n" (Plus2 (Var2 x) (Cte2 2)) (Var2 "n").

Goal (free [] (ex_free "n") "n") = true.
Proof.
trivial.
Qed.
Goal (free [] (ex_free "x") "n") = false.
Proof.
trivial.
Qed.
Goal (free [] (ex_free "x") "x") = true.
Proof.
trivial.
Qed.
Goal (free [] (Var2 "n") "n") = true.
Proof.
trivial.
Qed.
Goal (free [("n"%string, 0)] (Var2 "n") "n") = false.
Proof.
trivial.
Qed.


(* On va commencer par quelques lemmes d'inversion *)

(* l'évaluation échoue sur une opération "+" ou "*" SSI l'éval d'un des 2 membres échoue *)
Lemma none_lift2_inv : forall f c e1 e2, lift2 f (eval2 c e1) (eval2 c e2) = None <-> (eval2 c e1)=None \/ (eval2 c e2)=None.
Proof.
intros f c e1 e2; split; intros H.
- destruct (eval2 c e1) eqn:H1; destruct (eval2 c e2) eqn:H2.
     * simpl in H. discriminate.
     * right; trivial.
     * left; trivial.
     * left; trivial.
-  destruct H.
   * rewrite H; trivial.
   * rewrite H; simpl. destruct (eval2 c e1) eqn:H'; simpl; auto.
Qed.


(* si une variable "y" est libre dans le contexte (x,v)::c, alors on sait que
   "x<>y" et que "y" est aussi libre dans "c" *)
(* c'est très laborieux à cause de la conversion (\/ <=> orb) et (/\ <=> andb) *)
Lemma free_none_inv : forall (x:string) (v:nat) (c:Ctxt2) (e:EX2) (y:string),
                      free ((x,v)::c) e y = true -> (x <> y /\ free c e y = true).
Proof.
intros. split; induction e.
(* cas -> *)
- intros Hn. subst x.
  simpl in H. rewrite Bool.andb_true_iff in H. destruct H. rewrite H in H0. simpl in H0. discriminate.
- simpl in H; discriminate.
- simpl in H. rewrite Bool.orb_true_iff in H. destruct H; auto.
- simpl in H. rewrite Bool.orb_true_iff in H. destruct H; auto.
- simpl in H. rewrite Bool.orb_true_iff in H. destruct H.
  + apply IHe1. assumption.
  + rewrite Bool.andb_true_iff in H. destruct H.
    apply IHe2. assumption.
(* cas <- *)
- simpl in H. rewrite Bool.andb_true_iff in H. destruct H as [H0 H1].
  apply eqb_eq in H0. subst x0.
  simpl.
  destruct (string_dec y x). subst. 
  + rewrite eqb_refl in H1. simpl in H1. discriminate.
  + apply Bool.andb_true_iff. split; auto. apply eqb_refl.
    apply eqb_neq in n. rewrite n in H1. trivial.
- simpl in H; discriminate.
- simpl in H. rewrite Bool.orb_true_iff in H. destruct H.
  + apply IHe1 in H. simpl. apply Bool.orb_true_iff. left. trivial.
  + apply IHe2 in H. simpl. apply Bool.orb_true_iff. right. trivial.
- simpl in H. rewrite Bool.orb_true_iff in H. destruct H.
  + apply IHe1 in H. simpl. apply Bool.orb_true_iff. left. trivial.
  + apply IHe2 in H. simpl. apply Bool.orb_true_iff. right. trivial.
-  simpl in H. simpl. apply Bool.orb_true_iff.
   apply Bool.orb_true_iff in H. destruct H.
  + left. apply IHe1. trivial.
  + right. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
   apply Bool.andb_true_iff; split; auto.
Qed.

(* tout aussi laborieux, dans l'autre sens *)
Lemma free_none : forall (x:string) (v:nat) (c:Ctxt2) (e:EX2) (y:string),
                  (x <> y /\ free c e y = true) -> free ((x,v)::c) e y = true.
Proof.
induction e; intros; destruct H; auto.
- apply Bool.andb_true_iff in H0. apply Bool.andb_true_iff. destruct H0; split; auto.
  destruct (eqb x0 x) eqn:Heq.
  * simpl in * |- *.
    apply eqb_eq in H0. apply eqb_eq in Heq. subst x0. symmetry in Heq. contradiction.
  * simpl. rewrite Heq. trivial.
- simpl. apply Bool.orb_true_iff.
  simpl in H0. apply Bool.orb_true_iff in H0.
  destruct H0.
  * left. apply IHe1. split; auto. 
  * right. apply IHe2. split; auto.
- simpl. apply Bool.orb_true_iff.
  simpl in H0. apply Bool.orb_true_iff in H0.
  destruct H0.
  * left. apply IHe1. split; auto. 
  * right. apply IHe2. split; auto.
- simpl. apply Bool.orb_true_iff.
  simpl in H0. apply Bool.orb_true_iff in H0.
  destruct H0.
  *  left. apply IHe1; auto.
  *  right. apply Bool.andb_true_iff. apply Bool.andb_true_iff in H0. destruct H0.
     split; auto.
Qed.

(* Donc là on a le théorème utile : y est libre dans e avec le context ((x,v)::c) SSI
   x <> y (car (x,y) dans le contexte aurait donné une valeur) et que y est libre dans c *)
Lemma free_none_iff : forall (x:string) (v:nat) (c:Ctxt2) (e:EX2) (y:string),
                  (x <> y /\ free c e y = true) <-> free ((x,v)::c) e y = true.
Proof.
intros.
split; eauto using free_none, free_none_inv.
Qed.


(* Le théorème 'BUG FREE' : ça plante SSI on utilise une variable indéfinie *)
Theorem none_iff_free : forall e ctxt,
                        eval2 ctxt e = None <-> exists v, (free ctxt e v) = true.
Proof.
induction e; split; intros H. 
- (* (->) cas : e = (Var2 x) *) 
  exists x. simpl. simpl in H. rewrite H. rewrite eqb_refl. trivial.
- (* (<-) cas : e = (Var2 x) *) 
  destruct H. simpl in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  rewrite eqb_eq in H1. subst x0. simpl. apply is_none_inv. trivial.
- (* (->) cas : e = (Cte2 n) *)
  discriminate.
- (* (<-) cas : e = (Cte2 n) *)
  destruct H. discriminate.
- (* (->) cas : e = (Plus2 e1 e2) *)
  apply none_lift2_inv in H.
  destruct H.
   + apply IHe1 in H. destruct H. exists x. simpl. rewrite H. trivial.
   + apply IHe2 in H. destruct H. exists x. simpl. rewrite H. rewrite Bool.orb_comm.
     trivial.
- (* (<-) cas : e = (Plus2 e1 e2) *)
   destruct H. apply Bool.orb_true_iff in H. destruct H.
   + simpl. apply none_lift2_inv. left. apply IHe1. exists x. trivial.
   + simpl. apply none_lift2_inv. right. apply IHe2. exists x. trivial.
- (* (->) cas : e = (Mult2 e1 e2) IDEM cas Plus2 *)
  apply none_lift2_inv in H.
  destruct H.
   + apply IHe1 in H. destruct H. exists x. simpl. rewrite H. trivial.
   + apply IHe2 in H. destruct H. exists x. simpl. rewrite H. rewrite Bool.orb_comm.
     trivial.
- (* (<-) cas : e = (Mult2 e1 e2) IDEM cas Plus2 *)
  destruct H. apply Bool.orb_true_iff in H. destruct H.
   + simpl. apply none_lift2_inv. left. apply IHe1. exists x. trivial.
   + simpl. apply none_lift2_inv. right. apply IHe2. exists x. trivial.
- (* (->) cas : e = (Let2 x e1 e2) le cas marrant *)
  simpl in H.
  destruct (eval2 ctxt e1) eqn:H1.
   + (* eval2 ctxt e1 = Some n *)
     simpl.
     apply IHe2 in H.
     destruct H as [x2 H].
     exists x2.
     rewrite Bool.orb_true_iff.
     right.
     rewrite Bool.andb_true_iff.
     split.
     * apply free_none_inv in H. 
       rewrite Bool.negb_true_iff.
       apply eqb_neq. destruct H; auto.
     * apply free_none_inv in H. destruct H; trivial.
   + (* eval2 ctxt e1 = None *)
     apply IHe1 in H1. destruct H1 as [x1 H1]. exists x1.  simpl. rewrite H1. trivial. 
- (* (<-) cas : e = (Let2 x e1 e2) le cas marrant bis, laborieux en fait *)
   destruct H.  simpl in H. 
   apply Bool.orb_true_iff in H. 
   destruct H.
   + (* soit "x0" est libre dans "e1" "free ctxt e1 x0 = true" *)
     assert (exists v : string, free ctxt e1 v = true).
     { exists x0. trivial. }
     apply IHe1 in H0.
     simpl.
     rewrite H0. trivial.
   + (* soit "x0" est libre dans "e2" en qq sorte
        "(negb (x =? x0)%string && free ctxt e2 x0)%bool = true" *)
     apply Bool.andb_true_iff in H. destruct H. 
     assert (exists v : string, free ctxt e2 v = true).
     { exists x0. trivial. }
     apply IHe2 in H1.
     destruct (eval2 ctxt e1) eqn:Heq; trivial.
      * apply Bool.negb_true_iff in H.
        apply eqb_neq in H.
        assert (free ((x, n) :: ctxt) e2 x0 = true).
        { apply (free_none x n ctxt e2 x0). split; auto. }
        simpl. rewrite Heq.
        apply IHe2. exists x0. trivial.
      * simpl. rewrite Heq. trivial.
Qed.

End TD6.



