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

Theorem add_assoc' : forall n m p : nat, 
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| k IH].
  reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem add_assoc'' : forall n m p : nat, 
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| k IH].
  (*n = 0*)
  reflexivity.
  (*n = S k*)
  simpl. rewrite IH. reflexivity. 
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  assert (n + m = m + n) as H.
    { rewrite -> add_comm. reflexivity. }
  rewrite -> H. rewrite <- add_assoc. reflexivity.
Qed.

Theorem mul_1_r : forall n : nat, n * 1 = n.
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem mult_a_Sb : forall a b : nat, 

  a * S b = a + a * b.
Proof.
  intros a b.
  induction a as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. rewrite <- add_shuffle3. reflexivity.
Qed.

Theorem mul_comm : forall m n : nat, m * n = n * m.
Proof.
  intros m n.
  induction n as [| k IH].
  simpl. rewrite -> mul_0_r. reflexivity.
  simpl. rewrite <- IH. rewrite <- mult_a_Sb. reflexivity.
Qed.

Check leb.

Theorem plus_leb_compat_1 : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H.
  induction p as [| k IH].
  simpl. rewrite -> H. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem leb_refl : forall n:nat, (n <=? n) = true.
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat, 0 =? (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof.
  intros [].
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem S_neqb_0 : forall n : nat, (S n) =? 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_1 : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite -> add_0_r.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool, 
  orb
    (andb b c)
    (orb (negb b)
          (negb c)) = true .
Proof.
  intros [][].
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat, 
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. rewrite <- add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat, 
  n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> add_assoc.
  replace (n + m) with (m + n).
  rewrite -> add_assoc.
  reflexivity.
  rewrite -> add_comm.
  reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin, 
  bin_to_nat (incr b) = bin_to_nat b + 1.
Proof.
  induction b as [| k IH1 | k' IH2].
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite -> add_0_r. rewrite -> add_0_r. rewrite -> IH2.
  rewrite -> add_assoc.
  assert (bin_to_nat k' + 1 + bin_to_nat k' = bin_to_nat k' + bin_to_nat k' + 1) as H.
    { rewrite <- add_assoc. replace (1 + bin_to_nat k') with (bin_to_nat k' + 1). 
      rewrite -> add_assoc. reflexivity. rewrite -> add_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

