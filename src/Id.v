(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Omega.

Inductive id : Type :=
  Id : nat -> id.

Reserved Notation "m i<= n" (at level 70, no associativity).
Reserved Notation "m i>  n" (at level 70, no associativity).
Reserved Notation "m i<  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) i<= (Id m)
where "n i<= m" := (le_id n m).   

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) i< (Id m)
where "n i< m" := (lt_id n m).   

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) i> (Id m)
where "n i> m" := (gt_id n m).   

Notation "n i<= m" := (le_id n m).
Notation "n i>  m" := (gt_id n m).
Notation "n i<  m" := (lt_id n m).

Ltac prove_with th :=
  intros; 
  repeat (match goal with H: id |- _ => destruct H end); 
  match goal with n: nat, m: nat |- _ => set (th n m) end;
  repeat match goal with H: _ + {_} |- _ => inversion_clear H end;
  try match goal with H: {_} + {_} |- _ => inversion_clear H end;
  repeat
    match goal with 
      H: ?n <  ?m |-  _                + {Id ?n i< Id ?m}  => right
    | H: ?n <  ?m |-  _                + {_}               => left
    | H: ?n >  ?m |-  _                + {Id ?n i> Id ?m}  => right
    | H: ?n >  ?m |-  _                + {_}               => left
    | H: ?n <  ?m |- {_}               + {Id ?n i< Id ?m}  => right
    | H: ?n <  ?m |- {Id ?n i< Id ?m}  + {_}               => left
    | H: ?n >  ?m |- {_}               + {Id ?n i> Id ?m}  => right
    | H: ?n >  ?m |- {Id ?n i> Id ?m}  + {_}               => left
    | H: ?n =  ?m |-  _                + {Id ?n =  Id ?m}  => right
    | H: ?n =  ?m |-  _                + {_}               => left
    | H: ?n =  ?m |- {_}               + {Id ?n =  Id ?m}  => right
    | H: ?n =  ?m |- {Id ?n =  Id ?m}  + {_}               => left
    | H: ?n <> ?m |-  _                + {Id ?n <> Id ?m}  => right
    | H: ?n <> ?m |-  _                + {_}               => left
    | H: ?n <> ?m |- {_}               + {Id ?n <> Id ?m}  => right
    | H: ?n <> ?m |- {Id ?n <> Id ?m}  + {_}               => left

    | H: ?n <= ?m |-  _                + {Id ?n i<= Id ?m} => right
    | H: ?n <= ?m |-  _                + {_}               => left
    | H: ?n <= ?m |- {_}               + {Id ?n i<= Id ?m} => right
    | H: ?n <= ?m |- {Id ?n i<= Id ?m} + {_}               => left
    end;
  try (constructor; assumption); congruence.

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 i< id2} + {id1 = id2} + {id2 i< id1}.
Proof.
  intros.
  destruct id1. destruct id2.
  pose proof (lt_eq_lt_dec n n0) as [[H1 | H2] | H3].
  - left. left. constructor. apply H1.
  - left. right. auto.
  - right. constructor. apply H3.
Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 i> id2} + {id1 = id2} + {id2 i> id1}.
Proof.
  intros.
  destruct id1. destruct id2.
  pose proof (gt_eq_gt_dec n n0) as [[H1 | H2] | H3].
  - right. constructor. apply H1.
  - left. right. auto.
  - left. left. constructor. apply H3.
Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 i<= id2} + {id1 i> id2}.
Proof.
  intros.
  destruct id1. destruct id2.
  pose proof (le_gt_dec n n0) as [H1 | H2].
  - left. constructor. apply H1.
  - right. constructor. apply H2.
Qed.

Lemma id_eq_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. 
  intros.
  destruct id1. destruct id2.
  pose proof (eq_nat_dec n n0) as [H1 | H2].
  - left. auto.
  - right. injection. apply H2.
Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof.
  intros.
  destruct x.
  destruct id_eq_dec.
  - reflexivity.
  - contradiction.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof. 
  intros.
  destruct x. destruct y.
  destruct id_eq_dec.
  - contradiction.
  - reflexivity.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof.  
  intros.
  destruct id1. destruct id2.
  assert (n > n0). { inversion H. apply H3. }
  assert (n < n0). { inversion H0. apply H4. }
  apply Nat.lt_asymm in H1.
  contradiction.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof. 
  intros.
  destruct id1. destruct id2.
  inversion H. inversion H0.
  assert (~ n0 <= n). { omega. }
  contradiction.
Qed.
  
Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof. 
  intros [n1] [n2] Hle.
  pose proof (le_lt_eq_dec n1 n2) as [Hlt | Heq].
  - inversion Hle. assumption.
  - right. apply gt_conv. apply Hlt.
  - left. apply f_equal. assumption.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof.
  intros [n1] [n2] Hne.
  pose proof (gt_eq_gt_dec n1 n2) as [[H1 | H2] | H3].
  - right. apply gt_conv. assumption.
  - apply f_equal with (B:=id) (f:=Id) in H2.
    apply Hne in H2. contradiction.
  - left. apply gt_conv. assumption.
Qed.

Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof.
  intros [n1] [n2] HeqId HgtId.
  inversion HeqId as [Heq].
  inversion HgtId as [n1e n2e Hgt Heq1 Heq2].
  rewrite <- Heq in Hgt.
  pose proof (gt_irrefl n1) as H.
  contradiction.
Qed.