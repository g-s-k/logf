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

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type := true | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b_1:bool) (b_2:bool) : bool :=
  match b_1 with
  | true => b_2
  | false => false
  end.

Definition orb (b_1:bool) (b_2:bool) : bool :=
  match b_1 with
  | true => true
  | false => b_2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b_1:bool) (b_2:bool) : bool :=
  negb (andb b_1 b_2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b_1:bool) (b_2:bool) (b_3:bool) : bool :=
  b_1 && b_2 && b_3.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p:rgb).

Definition monochrome (c:color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.

Definition isred (c:color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Inductive bit : Type := B0 | B1.

Inductive nybble : Type :=
  | bits ( b0 b1 b2 b3 : bit ).

Check (bits B1 B0 B1 B0).

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute all_zero (bits B1 B0 B1 B0).
Compute all_zero (bits B0 B0 B0 B0).

Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute minustwo 4.

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
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

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: factorial 3 = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: factorial 5 = mult 10 12.
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1).

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, _ => false
  | S _, O => false
  | S n', S m' => eqb n' m'
  end.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, _ => true
  | S _, O => false
  | S n', S m' => leb n' m'
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  match n, m with
  | _, O => false
  | O, _ => true
  | S _, S m' => leb n m'
  end.

Example test_ltb1: ltb 2 2 = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: ltb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: ltb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n: forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l: forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l: forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example: forall n m : nat,
  n = m ->
  n + n = m + m.

Proof.
  (* move both quantifiers into ctx *)
  intros n m.
  (* move hypothesis into ctx *)
  intros H.
  (* rewrite goal using hypothesis *)
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.

Proof.
  intros n m o.
  intros H I.
  rewrite -> H.
  rewrite -> I.
  reflexivity.
Qed.

Theorem mult_0_plus: forall n m : nat,
  (0 + n) * m = n * m.

Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_S_l: forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.

Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry: forall n : nat,
  (n + 1) =? 0 = false.

Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neq_0: forall n : nat,
  (n + 1) =? 0 = false.

Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive: forall b : bool,
  negb (negb b) = b.

Proof.
  intros b.
  destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative: forall b c,
  andb b c = andb c b.

Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb3_exchange: forall b c d,
  andb (andb b c) d = andb (andb b d) c.

Proof.
  intros b c d.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0': forall n : nat,
  (n + 1) =? 0 = false.

Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'': forall b c,
  andb b c = andb c b.

Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2: forall b c : bool,
  andb b c = true -> c = true.

Proof.
  intros [] [] H.
  - reflexivity.
  - rewrite <- H.
    reflexivity.
  - reflexivity.
  - rewrite <- H.
    reflexivity.
Qed.

Theorem zero_nbeq_plus_1: forall n : nat,
  0 =? (n + 1) = false.

Proof.
  intros [| n'].
  - reflexivity.
  - reflexivity.
Qed.
