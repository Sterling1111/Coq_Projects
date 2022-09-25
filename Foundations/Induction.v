From Foundations Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat, n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.

Theorem add_0_r_secondtry : forall n:nat, n + 0 = n.
Proof.
  intros [].
  reflexivity.
  simpl.
Abort.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| k IH].
  reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem minus_n_n : forall n:nat, n - n = 0.
Proof.
  intros n.
  induction n as [| k IH].
  reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem mul_0_r: forall(n:nat), n * 0 = 0.
Proof.
  induction n as [| k IH].
  reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S(n+m) = n + (S m).
Proof.
  intros n m.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| k IH].
  simpl. rewrite -> add_0_r. reflexivity.
  simpl. rewrite -> IH. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| k IH].
  simpl. rewrite -> add_comm. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Fixpoint  double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat, (n =? n) = true.
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. assumption.
Qed.

Theorem even_S : forall n : nat, even (S n) = negb (even n).
Proof.
  induction n as [|k IH].
  simpl. reflexivity.
  rewrite -> IH. simpl. rewrite -> negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat, (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    {rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H. reflexivity.
  Qed.
