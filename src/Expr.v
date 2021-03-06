From Bignums Require Export BigZ.
Require Import List.
Import ListNotations.
Require Export Id.
Require Export State.
Require Import ZArith.

From hahn Require Import HahnBase.

(* Type of binary operators *)
Inductive bop : Type :=
| Add : bop
| Sub : bop
| Mul : bop
| Div : bop
| Mod : bop
| Le  : bop
| Lt  : bop
| Ge  : bop
| Gt  : bop
| Eq  : bop
| Ne  : bop
| And : bop
| Or  : bop.

(* Type of arithmetic expressions *)
Inductive expr : Type :=
| Nat : Z -> expr
| Var : id  -> expr              
| Bop : bop -> expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Bop Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Bop Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Bop Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Bop Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Bop Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Bop Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Bop Lt  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Bop Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Bop Gt  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Bop Eq  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Bop Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (Bop And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Bop Or  x y) (at level 38, left associativity).

Definition zbool (x : Z) : Prop := x = Z.one \/ x = Z.zero.
  
Definition zor (x y : Z) : Z :=
  if Z_le_gt_dec (Z.of_nat 1) (x + y) then Z.one else Z.zero.
   
Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

(* Big-step evaluation relation *)
Inductive eval : expr -> state Z -> Z -> Prop := 
  bs_Nat  : forall (s : state Z) (n : Z), [| Nat n |] s => n

| bs_Var  : forall (s : state Z) (i : id) (z : Z) (VAR : s / i => z),
    [| Var i |] s => z

| bs_Add  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb),
    [| a [+] b |] s => (za + zb)

| bs_Sub  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb),
    [| a [-] b |] s => (za - zb)

| bs_Mul  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb),
    [| a [*] b |] s => (za * zb)

| bs_Div  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (NZERO : ~ zb = Z.zero),
  [| a [/] b |] s => (Z.div za zb)

| bs_Mod  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (NZERO : ~ zb = Z.zero),
             [| a [%] b |] s => (Z.modulo za zb)

| bs_Le_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.le za zb),
    [| a [<=] b |] s => Z.one

| bs_Le_F : forall (s : state Z) (a b : expr) (za zb : Z) 
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.gt za zb),
  [| a [<=] b |] s => Z.zero

| bs_Lt_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.lt za zb),
    [| a [<] b |] s => Z.one

| bs_Lt_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.ge za zb),
    [| a [<] b |] s => Z.zero

| bs_Ge_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.ge za zb),
    [| a [>=] b |] s => Z.one

| bs_Ge_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.lt za zb),
    [| a [>=] b |] s => Z.zero

| bs_Gt_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.gt za zb),
  [| a [>] b |] s => Z.one

| bs_Gt_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.le za zb),
    [| a [>] b |] s => Z.zero

| bs_Eq_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.eq za zb),
    [| a [==] b |] s => Z.one

| bs_Eq_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : ~ Z.eq za zb),
    [| a [==] b |] s => Z.zero

| bs_Ne_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : ~ Z.eq za zb),
    [| a [/=] b |] s => Z.one

| bs_Ne_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.eq za zb),
    [| a [/=] b |] s => Z.zero

| bs_And  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (BOOLA : zbool za)
                   (BOOLB : zbool zb),
  [| a [&] b |] s => (za * zb)

| bs_Or   : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (BOOLA : zbool za)
                   (BOOLB : zbool zb),
    [| a [\/] b |] s => (zor za zb)
where "[| e |] st => z" := (eval e st z). 

Hint Constructors eval.

Module SmokeTest.

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof.
    apply bs_Nat.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH.
    inversion VALB.
    assert ((za * 2%Z)%Z = (za + za)%Z). { omega. }
    rewrite H.
    apply bs_Add.
    auto. auto.
  Qed.
  
End SmokeTest.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Bop : forall (id : id) (a b : expr) (op : bop), id ? a \/ id ? b -> id ? (Bop op a b)
where "x ? e" := (V e x).

(* If an expression is defined in some state, then each its' variable is
   defined in that state
 *)
Lemma defined_expression
      (e : expr) (s : state Z) (z : Z) (id : id)
      (RED : [| e |] s => z)
      (ID  : id ? e) :
  exists z', s / id => z'.
Proof.
  generalize dependent z.
  induction e.
  - intros. inversion ID. 
  - intros. inversion RED.
    assert (id = i). { inversion ID. auto. }
    rewrite H.
    exists z. auto.
  - inversion_clear ID. destruct H.
    + intros.
      inversion RED; apply (IHe1 H za); auto.
    + intros.
      inversion RED; apply (IHe2 H zb); auto.
Qed.
       
(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros.
  pose proof (defined_expression e s z id) as H1.
  intro H.
  pose proof (H1 H ID) as H2.
  inversion H2.
  contradiction (UNDEF x).
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z1.
  generalize dependent z2.
  induction e; intros.
  - intros. inversion E1. inversion E2.
    rewrite <- H2. auto.
  - intros. inversion E1. inversion E2.
    eapply state_deterministic.
    + apply VAR.
    + apply VAR0.
  - destruct b;
      inversion_clear E1; inversion_clear E2; 
        pose proof (IHe1 za VALA za0 VALA0) as H1;
        pose proof (IHe2 zb VALB zb0 VALB0) as H2;
        try (subst; reflexivity).
        all: (subst; contradict OP; auto).
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z :Z, s1 /id => z <-> s2 / id => z.

Ltac inversion_eval :=
  match goal with
  | H: ([| _ |] _ => _) |- _ => inversion_clear H
  end.

Ltac par_eval H b za zb :=
  intros H; destruct b; inversion H; [
         apply bs_Add |
         apply bs_Sub |
         apply bs_Mul |
         apply bs_Div |
         apply bs_Mod |
         apply bs_Le_T with (za) (zb) |
         apply bs_Le_F with (za) (zb) |
         apply bs_Lt_T with (za) (zb) |
         apply bs_Lt_F with (za) (zb) |
         apply bs_Ge_T with (za) (zb) |
         apply bs_Ge_F with (za) (zb) |
         apply bs_Gt_T with (za) (zb) |
         apply bs_Gt_F with (za) (zb) |
         apply bs_Eq_T with (za) (zb) |
         apply bs_Eq_F with (za) (zb) |
         apply bs_Ne_T with (za) (zb) |
         apply bs_Ne_F with (za) (zb) |
         apply bs_And |
         apply bs_Or
       ].

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :

  [| e |] s2 => z.
Proof.
  generalize dependent z;
  induction e.
  - intros. inversion EV. auto.
  - intros.
    pose proof (FV i (v_Var i)) as H1.
    apply bs_Var.
    unfold equivalent_states in H1.
    inversion EV.
    destruct (H1 z). auto.
  - assert (forall id : id, (id ? e1) -> equivalent_states s1 s2 id).
    { intros. apply FV. apply v_Bop. auto. }
    assert (forall id : id, (id ? e2) -> equivalent_states s1 s2 id).
    { intros. apply FV. apply v_Bop. auto. }
    intros. destruct b. inversion EV. 
    (*par_eval EV b za zb.
    auto.*)
Abort.
           
Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  constructor.
  auto. auto.
Qed.
   
Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent. intros.
  apply iff_sym. auto.
Qed.
  
Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent.
  unfold equivalent in EQ1.
  unfold equivalent in EQ2.
  intros.

  apply (iff_trans (EQ1 n s) (EQ2 n s)).
Qed.

Inductive Context : Type :=
| Hole : Context
| BopL : bop -> Context -> expr -> Context
| BopR : bop -> expr -> Context -> Context.

Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | BopL b C e1 => Bop b (plug C e) e1
  | BopR b e1 C => Bop b (plug C e) e1
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

Definition contextual_equivalent (e1 e2 : expr) : Prop :=
  forall (C : Context), (C <~ e1) ~~ (C <~ e2).
Notation "e1 '~c~' e2" := (contextual_equivalent e1 e2)
                            (at level 42, no associativity).

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  unfold contextual_equivalent. unfold equivalent.
  split; intros H.                
  - induction C.                                           
    + unfold plug. auto.
    + intros n s. simpl. split.
       * par_eval H1 b za zb; apply IHC in VALA; auto.
       * par_eval H1 b za zb; apply IHC in VALA; auto.
    + intros n s. simpl. split.
       * par_eval H1 b za zb; apply IHC in VALA; auto.
       * par_eval H1 b za zb; apply IHC in VALA; auto.
  - specialize (H Hole). auto.
Qed.

Module SmallStep.

  Inductive is_value : expr -> Prop :=
    isv_Intro : forall n, is_value (Nat n).

  Reserved Notation "st |- e --> e'" (at level 0).

  Inductive ss_eval : state Z -> expr -> expr -> Prop :=
    ss_Var   : forall (s   : state Z)
                      (i   : id)
                      (z   : Z)
                      (VAL : s / i => z), (s |- (Var i) --> (Nat z))
  | ss_Left  : forall (s      : state Z)
                      (l r l' : expr)
                      (op     : bop)
                      (LEFT   : s |- l --> l'), (s |- (Bop op l r) --> (Bop op l' r))
  | ss_Right : forall (s      : state Z)
                      (l r r' : expr)
                      (op     : bop)
                      (RIGHT  : s |- r --> r'), (s |- (Bop op l r) --> (Bop op l r'))
  | ss_Bop   : forall (s       : state Z)
                      (zl zr z : Z)
                      (op      : bop)
                      (EVAL    : [| Bop op (Nat zl) (Nat zr) |] s => z), (s |- (Bop op (Nat zl) (Nat zr)) --> (Nat z))      
  where "st |- e --> e'" := (ss_eval st e e').

  Lemma no_step_from_value (e : expr) (HV: is_value e) : ~ forall s, exists e', (s |- e --> e').
  Proof.
    unfold not.
    intros.
    destruct HV.
    pose (nil : state Z) as e_list.
    simpl in e_list.
    specialize (H e_list).
    destruct H.
    inversion H.
  Qed.
    
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    unfold not.
    intros.

    pose (Id 1) as x.
    pose (Id 2) as y.
    pose ([(x, 1%Z) ; (y, 2%Z)]) as st.
    pose (Bop Add (Var x) (Var y)) as bop.

    assert ([| Var x |] st => 1).
    { constructor. unfold x. unfold st. constructor. }

    pose proof id_eq_dec x y as [H1 | H2].
    - pose (gt_conv 2 1) as kek.
      assert (2 > 1). { omega. }
                      specialize (kek H2).
      unfold x in H1. unfold y in H1.
      pose proof (eq_gt_id_false (Id 2) (Id 1)).
      symmetry in H1.
      specialize (H3 H1 kek).
      auto.
    - unfold x in H2. unfold y in H2.
      assert ([| Var y |] st => 2).
      { constructor. unfold x. unfold st. constructor.
        unfold x. unfold y. auto. constructor. }

      specialize (H bop (Bop Add (Nat 1) (Var y)) (Bop Add (Var x) (Nat 2)) st).

      assert ((st) |- bop --> (Nat 1 [+] Var y)).
      { constructor. constructor. constructor. }
      assert ((st) |- bop --> (Var x [+] Nat 2)).
      { constructor. constructor. constructor.
        unfold x. unfold y. auto. constructor. }
      
      specialize (H H3 H4).
      contradict H.
      unfold y. unfold x.
      
      firstorder.
  Qed.
  
  Lemma state_z_deterministic (st : state Z) (x : id) (n m : Z)
        (SN : st / x => n)
        (SM : st / x => m) :
    n = m.
  Proof.
    induction SN.
    - inversion SM.
      + reflexivity.
      + contradiction.
    - assert ((st) / id => (m)) as LIHSN.
      {
        inversion SM.
        - contradict H. auto.
        - apply H6.
      }
      apply IHSN. apply LIHSN.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    generalize dependent s.
    induction e; intros.
    + 
      
    
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (e = Nat z \/ s |- e --> (Nat z)).
  Proof.
    split.
    - intros.
      destruct e.
      + inversion H.
        left. auto.
      + right.
        inversion H.
        apply (ss_Var s i z VAR).
      + right.        
   Abort.


(*
  s |- e -> .... -> Nat z
       \
        \-> .... -> Nat z

  s |- e -> .... -> e'  
*)
  
End SmallStep.

