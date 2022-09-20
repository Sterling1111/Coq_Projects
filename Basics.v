Inductive bool : Type := 
| true
| false.

Definition negb (b:bool) : bool:= 
    match b with
    | true => false
    | false => true
    end.

Definition andb (b1:bool) (b2:bool) : bool := 
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.

Definition negb' (b:bool) : bool :=
    if b then false
    else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
    if b1 then b2
    else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
    if b1 then true
    else b2.
    
Definition nandb  (b1:bool) (b2:bool) : bool :=
    match b1 with
    | false => true
    | true => (negb b2)
    end.
    
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
    
Example test_orb1: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: true && false = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
    match b1 with
    | false => false
    | true => (andb b2 b3) 
    end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed. 
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check true : bool.
Check (negb true) : bool.
Check negb : bool -> bool.

Theorem negb_negb : forall (b:bool), negb (negb b) = b.
Proof.
    intros b.
    destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Inductive day : Type :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.

Definition next_weekday (d:day) : day :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

Compute (next_weekday (next_weekday friday)).
Compute (next_weekday friday).

Example test_next_weekday:
    (next_weekday (next_weekday saturday)) = tuesday.

Proof.
    simpl.
    reflexivity.
Qed.

Inductive rgb : Type :=
    | red
    | green
    | blue.

Inductive color : Type := 
    | black
    | white
    | primary (p : rgb).

Definition monochrome (c:color) : bool := 
    match c with
    | black => true
    | white => true
    | primary p => false
    end.

Definition isred (c:color) : bool :=
    match c with
    | black => true
    | white => true
    | primary red => true
    | primary _ => false
    end.

Module Playground.
    Definition b : rgb := blue.
End Playground.
    
Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.

Module TuplePlayground.
    Inductive bit : Type :=
        | B0
        | B1.

    Inductive nybble : Type :=
        | bits (b0 b1 b2 b3 : bit).

    Check (bits B1 B0 B1 B0) : nybble.

    Definition all_zero (nb:nybble) : bool :=
        match nb with
        | (bits B0 B0 B0 B0) => true
        | (bits _ _ _ _) => false
        end.

    Compute (all_zero (bits B1 B1 B0 B0)).
    Compute (all_zero (bits B0 B0 B0 B0)).
    
End TuplePlayground.

Module Type NatPlayground.
    Inductive nat : Type :=
        | O
        | S (n : nat).

    Definition pred (n:nat) : nat := 
        match n with
        | O => O
        | S n' => n'
        end.
End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n:nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

Compute (minustwo 4).

Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.

Fixpoint even (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

Definition odd (n:nat) : bool :=
    negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
    Fixpoint plus (n:nat) (m:nat) : nat := 
        match n with
        | O => m
        | S n' => S (plus n' m)
        end.

    Compute plus 3 2.

    Fixpoint mult (n m : nat) : nat :=
        match n with
        | O => O
        | S n' => plus m (mult n' m)
        end.
    
    Example test_mult1: (mult 3 3) = 9.
    Proof. simpl. reflexivity. Qed.    
End NatPlayground2.
