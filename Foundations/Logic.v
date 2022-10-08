Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Foundations Require Export Tactics.

Check (3 = 3) : Prop.

Check (forall n m : nat, n + m = m + n) : Prop.

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof.
  simpl. reflexivity.
Qed.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true : plus_claim.
Proof.
  reflexivity.
Qed.

Definition is_three (n : nat) : Prop := n = 3.

Check is_three : nat -> Prop.

Definition injective {A B} (f : A -> B) := 
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  unfold injective. intros. injection H as H1. apply H1.
Qed.

Check @eq : forall A : Type, A -> A -> Prop.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros. split.
  - apply H.
  - apply H0.
Qed.

Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros. split.
  - destruct n as [| n'].
    * reflexivity.
    * simpl in H. discriminate H.
  - destruct m.
    * reflexivity.
    * rewrite add_comm in H. simpl in H. discriminate H.
Qed.

Lemma and_example2 : forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros.
  destruct H as [H1 H2].
  rewrite -> H1. rewrite -> H2. simpl. reflexivity.
Qed.

Lemma and_example2' : forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [H1 H2].
  rewrite -> H1. rewrite -> H2. simpl. reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 : forall n m : nat,
  n + m = 0 -> n * m = 0.
Proof.
  intros.
  apply and_exercise in H.
  destruct H as [H1 H2].
  rewrite H1. simpl. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros.
  destruct H as [H1 _].
  apply H1.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros.
  destruct H as [_ H2].
  apply H2.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [H1 H2]. split.
  - apply H2.
  - apply H1.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [H1 [H2 H3]]. split.
  - split.
    * apply H1.
    * apply H2.
  - apply H3.
Qed.

Check and : Prop -> Prop -> Prop.
Check or : Prop -> Prop -> Prop.

Lemma factor_is_O : forall n m : nat,
  n = O \/ m = 0 -> n * m = 0.
Proof.
  intros n m [H1 | H2].
  - rewrite -> H1. simpl. reflexivity.
  -  rewrite -> H2. apply mul_comm.
Qed.

Lemma or_intro_l : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros.
  left.
  apply H.
Qed.

Lemma zero_or_succ : forall n : nat,
  n = 0 \/ n = S (pred n).
Proof.
  intros [| n'].
  - left. reflexivity.
  - right. simpl. reflexivity. 
Qed.

Lemma mult_is_O : forall n m : nat,
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros. 
  destruct n as [| n'].
  - left. reflexivity.
  - destruct m as [| m'].
    * right. reflexivity.
    * simpl in H. discriminate H.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [H1 | H2].
  - right. apply H1.
  - left. apply H2.
Qed.

Module NotPlayground.

Definition not (P : Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not : Prop -> Prop.

End NotPlayground.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros.
  destruct H.
Qed.

Theorem not_implies_our_not' : forall P Q : Prop,
  ~P -> (P -> Q).
Proof.
  intros. unfold not in H. destruct H. apply H0.
Qed.


(*destruct on A -> B will assume B, but we will then need to show A*)
Theorem not_implies_our_not : forall P : Prop,
  ~P -> (forall Q : Prop, P -> Q).
Proof.
  unfold not. intros. destruct H. apply H0.
Qed.

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not. intro H. discriminate H.
Qed.

Theorem not_False : ~False.
Proof.
  unfold not. intro H. destruct H.
Qed.

Theorem true_and_false : forall P : Prop,
  (P /\ ~P) -> False.
Proof.
  intros P [H1 H2]. unfold not in H2. destruct H2. apply H1. 
Qed.

Theorem contradiction_implies_anything' : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q H. apply true_and_false in H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [H1 H2].
  unfold not in H2. destruct H2. apply H1.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros. unfold not. intro H2. destruct H2. apply H.
Qed.

(*Let P be any proposition and suppose P. We must show that this implies ~~P
  By definition we are to show that (P->False) -> False. Suppose P -> False, If
  we had P then we would be supposing false. Lets suppose we can get P somehow and
  take false. Then what we want to show which is false is shown by vacuous truth. now
  show P from our original hypothesis. Qed*)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2.
  unfold not. unfold not in H2. intro H3. apply H2. apply H1. apply H3.
Qed.

Theorem not_both_true_and_false : forall P Q : Prop,
  ~(P /\ ~P).
Proof.
  intros. unfold not. intros [H1 H2]. destruct H2. apply H1.
Qed.

(* the best way to give an informal proof would be a simpl truth table*)

 Theorem de_morgan_not_or : forall (P Q : Prop),
  ~ (P \/ Q) -> ~P /\ ~Q.
 Proof.
  intros P Q H. unfold not in H. split.
  - unfold not. intro H2. destruct H. left. apply H2.
  - unfold not. intro H2. destruct H. right. apply H2.
 Qed.

 Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
 Proof.
  intros.
  destruct b.
  - unfold not in H. apply ex_falso_quodlibet. apply H. reflexivity.
  - reflexivity.
 Qed.

 Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
 Proof.
  intros.
  destruct b.
  - unfold not in H. exfalso. apply H. reflexivity.
  - reflexivity.
 Qed.
 
Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Definition disc_fn (n : nat) : Prop := 
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n : nat,
  ~ (O = S n).
Proof.
  intros n H.
  assert (H2 : disc_fn O). {simpl. apply I. }
  rewrite -> H in H2. simpl in H2. apply H2.
Qed.

Module IffPlayground.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End IffPlayground.


Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. Qed.


Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. unfold not. intros H'. discriminate H'.
Qed.

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
  intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
  intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. split.
  - intro H. split.
    * destruct H as [H2 | H3].
      + left. apply H2.
      + destruct H3 as [H2 H3]. right. apply H2.
    * destruct H as [H2 | H3].
      + left. apply H2.
      + destruct H3 as [H4 H5]. right. apply H5.
  - intro H. destruct H as [[H2 | H3] [H4 | H5]].
    * left. apply H2.
    * left. apply H2.
    * left. apply H4.
    * right. split.
      + apply H3.
      + apply H5.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

Definition Even (x : nat) : Prop := exists n : nat, x = double n.

Lemma four_is_even : Even 4.
Proof.
  unfold Even. exists 2. simpl. reflexivity.
Qed.

Theorem exists_example_2 : forall n : nat,
  (exists m : nat, n = 4 + m) -> (exists o : nat, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m). simpl in Hm. simpl. apply Hm. 
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~(exists x, ~ P x).
Proof.
  intros X P H1. 
  unfold not. intro H2. destruct H2 as [x H2]. 
  destruct H2. apply H1.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x1 H]. destruct H as [H | H].
    * left. exists (x1). apply H.
    * right. exists (x1). apply H.
  - intros H. destruct H as [H | H].
    * destruct H as [x1 H]. exists (x1). left. apply H.
    * destruct H as [x1 H]. exists (x1). right. apply H.
Qed.

(*Lemma plus_minus_assoc : forall n m : nat,
  n <=? m = true -> n + (m - n) = (n + m) - n.
Proof.
  
Qed.*)

Theorem leb_plus_exists : forall n m : nat,
  n <=? m = true -> exists x, m = n + x.
Proof.
  intros. exists (m - n). generalize dependent n.
  induction m as [| k IH].
  - destruct n as [| n']. 
    * simpl. reflexivity.
    * simpl. discriminate.
  - destruct n as [| n'].
    * simpl. reflexivity.
    * simpl. intros H. f_equal. apply IH. apply H.
Qed.

Lemma leb_n_plus : forall n m : nat,
  n <=? n + m = true.
Proof.
  intros n m.
  induction n as [| k IH].
  - simpl. reflexivity.
  - rewrite add_comm. rewrite <- plus_n_Sm. simpl. rewrite add_comm. apply IH.
Qed.

Theorem plus_exists_leb : forall n m : nat,
  (exists x, m = n + x) -> n <=? m = true.
Proof.
  intros n m [x H].
  rewrite -> H. destruct x as [| x'].
  - rewrite -> add_0_r. apply leb_refl.
  - rewrite -> add_comm. simpl. destruct x' as [| x''].
    * simpl. apply NatList.leb_n_Sn.
    * simpl. rewrite -> add_comm. rewrite plus_n_Sm. rewrite plus_n_Sm. apply leb_n_plus.
Qed.

