Require Import List.
Import ListNotations.
Require Import Omega.

From Bignums Require Export BigZ.
Require Export Id.
Require Export State.
Require Export Expr.

From hahn Require Import HahnBase.

(* AST for statements *)
Inductive stmt : Type :=
| SKIP  : stmt
| Assn  : id -> expr -> stmt
| READ  : id -> stmt
| WRITE : expr -> stmt
| Seq   : stmt -> stmt -> stmt
| If    : expr -> stmt -> stmt -> stmt
| While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf :=  (state Z * list Z * list Z)%type.

(* Big-step evaluation relation *)
Reserved Notation "c1 '==' s '==>' c2" (at level 0).

Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
| bs_Skip        : forall (c : conf),
    c == SKIP ==> c 
| bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
    (s, i, o) == x ::= e ==> (s [x <- z], i, o)
| bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
    (s, z::i, o) == READ x ==> (s [x <- z], i, o)
| bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
    (s, i, o) == WRITE e ==> (s, i, z::o)
| bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt)
                          (STEP1 : c == s1 ==> c') (STEP2 : c' == s2 ==> c''),
    c ==  s1 ;; s2 ==> c''
| bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                     (CVAL : [| e |] s => Z.one)
                     (STEP : (s, i, o) == s1 ==> c'),
    (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                     (CVAL : [| e |] s => Z.zero)
                     (STEP : (s, i, o) == s2 ==> c'),
    (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt)
                          (CVAL  : [| e |] st => Z.one)
                          (STEP  : (st, i, o) == s ==> c')
                          (WSTEP : c' == WHILE e DO s END ==> c''),
    (st, i, o) == WHILE e DO s END ==> c''
| bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt)
                          (CVAL : [| e |] st => Z.zero),
    (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

(* Big step equivalence *)
Definition bs_equivalent (s1 s2 : stmt) :=
  forall (c c' : conf),
    c == s1 ==> c' <-> c == s2 ==> c'.

Notation "s1 '~~~' s2" := (bs_equivalent s1 s2) (at level 0).

Ltac seq_inversion :=
  match goal with
    H: _ == _ ;; _ ==> _ |- _ => inversion_clear H
  end.

Ltac seq_apply :=
  match goal with
  | H: _   == ?s1 ==> ?c' |- _ == (?s1 ;; _) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  | H: ?c' == ?s2 ==>  _  |- _ == (_ ;; ?s2) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  end.

Module SmokeTest.

  (* Associativity of sequential composition *)
  Lemma seq_assoc (s1 s2 s3 : stmt) :
    ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof.
    unfold bs_equivalent.
    intros.
    split; intros;
    seq_inversion;
    seq_inversion;
    seq_apply.
Qed.
      
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.    
    unfold bs_equivalent.
    intros. split;
    intros.
    - inversion H.
      + apply bs_If_True. auto. seq_apply.
      + apply bs_If_False. auto. apply bs_Skip.
    - inversion H.
      + seq_inversion. apply bs_While_True with (c' := c'1).
        auto. auto. auto.
      + inversion STEP. apply bs_While_False. auto.
  Qed.
       
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as e2.
    remember (st, i, o) as c2.
    induction EXE; try inversion Heqe2.
    apply (IHEXE2 Heqe2 Heqc2).
    inversion Heqc2.
    rewrite <- H0. rewrite <- H2.
    auto.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    intros. split; intros.
    - destruct c'. destruct p.
      apply while_false in H. inversion H.
    - destruct c.
      inversion H; inversion CVAL.
  Qed.

  Lemma bs_eq_symmetry (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
    s2 ~~~ s1.
  Proof.
    unfold bs_equivalent.
    unfold bs_equivalent in EQ.
    intros.
    symmetry.
    auto.
  Qed.

  Lemma while_impl (e : expr) (c c' : conf) (s s' : stmt)
        (EQ : s ~~~ s') :
    c == WHILE e DO s END ==> c' -> c == WHILE e DO s' END ==> c'.
  Proof.
      intros. 
      remember (WHILE e DO s END).
      induction H; inversion Heqs0.
      - subst. apply bs_While_True with (c'). auto. 
        unfold bs_equivalent in EQ. apply EQ. auto.
        apply IHbs_int2. auto.
      - subst. apply bs_While_False. auto.
  Qed.
            
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent.
    split; intros H.
    - apply while_impl with (s1). auto. auto.
    - apply while_impl with (s2).
      apply bs_eq_symmetry. auto. auto.
  Qed.         
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    unfold not.
    intros H.
    remember (WHILE Nat 1 DO s END) as inf_loop.
    induction H; inversion Heqinf_loop.
    - apply IHbs_int2. auto.
    - assert (Heval: [|e|] st => (Z.one)). {subst. apply bs_Nat. }
      pose proof eval_deterministic. 
      pose proof (eval_deterministic e st Z.zero Z.one CVAL Heval).
      inversion H2.
  Qed.
 
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent. unfold bs_equivalent in EQ.
  intros.
  split; intros; seq_inversion;
    apply EQ in STEP2; seq_apply.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent. unfold bs_equivalent in EQ.
  intros.
  split; intros; seq_inversion;
    apply EQ in STEP1; seq_apply.
Qed.


  Lemma if_else_impl (e : expr) (c c' : conf) (s s' s'' : stmt)
        (EQ : s' ~~~ s'') :
    c == COND e THEN s ELSE s' END ==> c' -> c == COND e THEN s ELSE s'' END ==> c'.
  Proof.
    intros.
    unfold bs_equivalent in EQ.
    remember (COND e THEN s ELSE s' END).
    induction H; inversion Heqs0.
    - subst. apply bs_If_True. auto. auto.
    - subst. apply bs_If_False. auto. 
      apply EQ in H. auto.
  Qed.

  Lemma if_then_impl (e : expr) (c c' : conf) (s s' s'' : stmt)
        (EQ : s' ~~~ s'') :
    c == COND e THEN s' ELSE s END ==> c' -> c == COND e THEN s'' ELSE s END ==> c'.
  Proof.
    intros.
    unfold bs_equivalent in EQ.
    remember (COND e THEN s' ELSE s END).
    induction H; inversion Heqs0.
    - subst. apply bs_If_True. auto.
      apply EQ in H. auto.
    - subst. apply bs_If_False. auto. auto.
  Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent. split; intros.
  - apply if_else_impl with (s1). auto. auto.
  - apply if_else_impl with (s2). apply SmokeTest.bs_eq_symmetry.
    auto. auto.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent. split; intros.
  - apply if_then_impl with (s1). auto. auto.
  - apply if_then_impl with (s2). apply SmokeTest.bs_eq_symmetry.
    auto. auto.
Qed.

Lemma eq_congruence_while
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  apply SmokeTest.while_eq. auto.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split. apply eq_congruence_seq_r. auto.
  split. apply eq_congruence_seq_l. auto.
  split. apply eq_congruence_cond_else. auto.
  split. apply eq_congruence_cond_then. auto.
  apply eq_congruence_while. auto. auto.
Qed.

(* Big-step semantics is deterministic *)
Ltac by_eval_deterministic :=
   match goal with
    H1: [|?e|]?s => ?z1, H2: [|?e|]?s => ?z2 |- _ => 
     apply (eval_deterministic e s z1 z2) in H1; [subst z2; reflexivity | assumption]
  end.

Ltac eval_zero_not_one :=
  match goal with
    H : [|?e|] ?st => (Z.one), H' : [|?e|] ?st => (Z.zero) |- _ =>
    assert (Z.zero = Z.one) as JJ; [ | inversion JJ];
    eapply eval_deterministic; eauto
  end.

Lemma bs_int_deterministic (c c1 c2 : conf) (s : stmt)
      (EXEC1 : c == s ==> c1) (EXEC2 : c == s ==> c2) :
  c1 = c2.
Proof.
  generalize dependent c.
  generalize dependent c1.
  generalize dependent c2.
  induction s ; intros.
  - inversion EXEC1. inversion EXEC2.
    subst. auto.
  - inversion EXEC1. inversion EXEC2.
    subst. inversion H6. subst.
    assert (z = z0). { apply (eval_deterministic e s); auto. }
    subst. auto.
  - inversion EXEC1. inversion EXEC2. 
    subst. inversion H4. auto.
  - inversion EXEC1. inversion EXEC2. 
    subst. inversion H4. subst.
    assert (z = z0). { apply (eval_deterministic e s); auto. }
    subst. auto.
  - inversion EXEC1. inversion EXEC2.
    specialize (IHs1 c' c'0 c STEP0 STEP1). subst.
    specialize (IHs2 c1 c2 c' STEP3 STEP2). auto.
  - inversion EXEC1; inversion EXEC2;
      subst; inversion H8; subst.
    + specialize (IHs1 c2 c1 (s, i, o) STEP STEP0). auto.
    + eval_zero_not_one.
    + eval_zero_not_one.
    + specialize (IHs2 c2 c1 (s, i, o) STEP STEP0). auto.
  - remember (WHILE e DO s END) as H1.
    induction EXEC1; auto; inversion HeqH1; subst.
    + apply IHEXEC1_2; auto.
      assert (c'' = c2).
      { inversion_clear EXEC2.
        - apply IHEXEC1_2. auto.
          assert (c'0 = c'). { apply (IHs c' c'0 (st, i, o)); auto. }
          subst. auto.
        - eval_zero_not_one. }
      subst. auto.
    + inversion EXEC2.
      * eval_zero_not_one.
      * auto.
Qed.

(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Definition contextual_equivalent (s1 s2 : stmt) :=
  forall (C : Context), (C <~ s1) ~~~ (C <~ s2).
Notation "s1 '~c~' s2" := (contextual_equivalent s1 s2)
                            (at level 42, no associativity).

(* Contextual equivalence is equivalent to the semantic one *)
(* TODO: no longer needed *)
Ltac by_eq_congruence e s s1 s2 H :=
  remember (eq_congruence e s s1 s2 H) as Congruence;
  match goal with H: Congruence = _ |- _ => clear H end;
  repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end); assumption.
    
Lemma eq_eq_ceq s1 s2: s1 ~~~ s2 <-> s1 ~c~ s2.
Proof.
  unfold contextual_equivalent.
  unfold bs_equivalent.
  split.
  pose (Nat 1) as E_true.
  - induction C; try (simpl; auto);
      try (apply eq_congruence); try (auto; auto).
  - intros.
    specialize (H Hole).
    auto.
Qed.       
      
(* Small-step semantics *)
Module SmallStep.
  
  Reserved Notation "c1 '--' s '-->' c2" (at level 0).

  Inductive ss_int_step : stmt -> conf -> option stmt * conf -> Prop :=
  | ss_Skip        : forall (c : conf), c -- SKIP --> (None, c) 
  | ss_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z) 
                            (SVAL : [| e |] s => z),
      (s, i, o) -- x ::= e --> (None, (s [x <- z], i, o))
  | ss_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
      (s, z::i, o) -- READ x --> (None, (s [x <- z], i, o))
  | ss_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                            (SVAL : [| e |] s => z),
      (s, i, o) -- WRITE e --> (None, (s, i, z::o))
  | ss_Seq_Compl   : forall (c c' : conf) (s1 s2 : stmt)
                            (SSTEP : c -- s1 --> (None, c')),
      c -- s1 ;; s2 --> (Some s2, c')
  | ss_Seq_InCompl : forall (c c' : conf) (s1 s2 s1' : stmt)
                            (SSTEP : c -- s1 --> (Some s1', c')),
      c -- s1 ;; s2 --> (Some (s1' ;; s2), c')
  | ss_If_True     : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.one),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s1, (s, i, o))
  | ss_If_False    : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.zero),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s2, (s, i, o))
  | ss_While       : forall (c : conf) (s : stmt) (e : expr),
      c -- WHILE e DO s END --> (Some (COND e THEN s ;; WHILE e DO s END ELSE SKIP END), c)
  where "c1 -- s --> c2" := (ss_int_step s c1 c2).

  Reserved Notation "c1 '--' s '-->>' c2" (at level 0).

  Inductive ss_int : stmt -> conf -> conf -> Prop :=
    ss_int_Base : forall (s : stmt) (c c' : conf),
                    c -- s --> (None, c') -> c -- s -->> c'
  | ss_int_Step : forall (s s' : stmt) (c c' c'' : conf),
                    c -- s --> (Some s', c') -> c' -- s' -->> c'' -> c -- s -->> c'' 
  where "c1 -- s -->> c2" := (ss_int s c1 c2).

  Lemma ss_int_step_deterministic (s : stmt)
        (c : conf) (c' c'' : option stmt * conf) 
        (EXEC1 : c -- s --> c')
        (EXEC2 : c -- s --> c'') :
    c' = c''.
  Proof.
    generalize dependent c.
    generalize dependent c'.
    generalize dependent c''.
    induction s; intros; try (inversion EXEC1; inversion EXEC2);
      try (subst).
    - auto.
    - inversion H6.
      rewrite -> H0 in SVAL0.
      pose proof (eval_deterministic e s z0 z SVAL0 SVAL).
      rewrite H. auto.
    - inversion H4.
      subst. auto.
    - inversion H4. rewrite -> H0 in SVAL0.
      pose proof (eval_deterministic e s z0 z SVAL0 SVAL).
      rewrite H. auto.
    - specialize (IHs1 (None, c'0) (None, c'1) c SSTEP0 SSTEP) as H1;
      inversion H1; rewrite <- H0; auto.
    - specialize (IHs1 (None, c'0) (Some s1', c'1) c SSTEP0 SSTEP).
      inversion IHs1.
    - specialize (IHs1 (Some s1', c'0) (None, c'1) c SSTEP0 SSTEP).
      inversion IHs1.
    - specialize (IHs1 (Some s1', c'0) (Some s1'0, c'1) c SSTEP0 SSTEP).
      inversion IHs1.
      auto.
    - inversion H8. auto.
    - inversion H8; subst;
      pose proof (eval_deterministic e s Z.one Z.zero SCVAL SCVAL0);
      inversion H. 
    - inversion H8. subst.
      pose proof (eval_deterministic e s Z.one Z.zero SCVAL0 SCVAL).
      inversion H.
    - inversion H8. auto.
    - auto.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c'.
    induction STEP2; intros; inversion STEP1.
      - apply ss_int_step_deterministic with (c':=(None, c'0)) in H.
        inversion H. auto. auto.
      - apply ss_int_step_deterministic with (c':=(Some s', c'1)) in H.
        inversion H. auto.
      - apply ss_int_step_deterministic with (c':=(None, c'0)) in H.
        inversion H. auto.
      - apply ss_int_step_deterministic with (c':=(Some s'0, c'1)) in H.
        inversion H. subst.
        specialize (IHSTEP2 c'0). specialize (IHSTEP2 H1).
        auto. auto.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    remember (None, c') as c'0.
    induction STEP; inversion Heqc'0.
    - subst. apply bs_Skip.
    - subst. apply bs_Assign. auto.
    - subst. apply bs_Read.
    - subst. apply bs_Write. auto.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    generalize dependent c'.
    induction STEP1; intros.
    - apply ss_int_Step with (s2) (c'). apply ss_Seq_Compl.
      auto. auto.
    - apply ss_int_Step with (s';; s2) (c').
      specialize (IHSTEP1 c'0 STEP2).
      apply ss_Seq_InCompl. auto.
      auto.
  Qed.
    
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent s'.
    generalize dependent c'.
    generalize dependent c''.
    induction s; intros; inversion STEP.
    - apply ss_bs_base in SSTEP.
      apply bs_Seq with (c':=c'). auto. auto.
    - subst. inversion_clear EXEC.
      apply bs_Seq with (c' := c'0).
      + specialize (IHs1 c'0 c' s1' SSTEP STEP1).
        auto.
      + auto.
    - subst. apply bs_If_True. auto. auto.
    - subst. apply bs_If_False. auto. auto.
    - subst. apply SmokeTest.while_unfolds. auto.
  Qed.        
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; intros.
    - induction H.
      + constructor. apply ss_Skip.
      + constructor. apply ss_Assign. auto.
      + constructor. apply ss_Read.
      + constructor. apply ss_Write. auto.
      + pose proof (ss_ss_composition c c'' c' s1 s2 IHbs_int1 IHbs_int2).
        auto.
      + apply ss_int_Step with (s1) ((s, i, o)). 
        apply ss_If_True. auto. auto.
      + apply ss_int_Step with (s2) ((s, i, o)).
        apply ss_If_False. auto. auto.
      + pose proof
             (ss_ss_composition (st, i, o) c'' c' s (WHILE e DO s END) IHbs_int1 IHbs_int2).
        apply ss_int_Step with
            (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) ((st, i, o)).
        apply ss_While.
        apply ss_int_Step with (s;; (WHILE e DO s END)) (st, i, o).
        apply ss_If_True. auto. auto.
      + (* TODO Make easier proof ??*)
        apply ss_int_Step
          with (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (st, i, o).
        apply ss_While.
        apply ss_int_Step with (SKIP) (st, i, o).
        apply ss_If_False. auto.
        apply ss_int_Base. apply ss_Skip.
    - induction H.
      + apply ss_bs_base. auto.
      + apply ss_bs_step with (c') (s'). auto. auto.
  Qed.      
End SmallStep.

(* CPS semantics *)
Inductive cont : Type := 
| KEmpty : cont
| KStmt  : stmt -> cont.
 
Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty  , _       ) => r
  | (_       , _       ) => l
  end.

Notation "'!' s" := (KStmt s) (at level 0).
Notation "s1 @ s2" := (Kapp s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : cont -> cont -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), KEmpty |- c -- KEmpty --> c
| cps_Skip        : forall (c c' : conf) (k : cont)
                           (CSTEP : KEmpty |- c -- k --> c'),
    k |- c -- !SKIP --> c'
| cps_Assign      : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (x : id) (e : expr) (n : Z)
                           (CVAL : [| e |] s => n)
                           (CSTEP : KEmpty |- (s [x <- n], i, o) -- k --> c'),
    k |- (s, i, o) -- !(x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (x : id) (z : Z)
                      (CSTEP : KEmpty |- (s [x <- z], i, o) -- k --> c'),
    k |- (s, z::i, o) -- !(READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (z : Z)
                      (CVAL : [| e |] s => z)
                      (CSTEP : KEmpty |- (s, i, z::o) -- k --> c'),
    k |- (s, i, o) -- !(WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : cont) (s1 s2 : stmt)
                           (CSTEP : !s2 @ k |- c -- !s1 --> c'),
    k |- c -- !(s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s1 s2 : stmt)
                      (CVAL : [| e |] s => Z.one)
                      (CSTEP : k |- (s, i, o) -- !s1 --> c'),
    k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s1 s2 : stmt)
                      (CVAL : [| e |] s => Z.zero)
                      (CSTEP : k |- (s, i, o) -- !s2 --> c'),
    k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s : stmt)
                      (CVAL : [| e |] st => Z.one)
                      (CSTEP : !(WHILE e DO s END) @ k |- (st, i, o) -- !s --> c'),
    k |- (st, i, o) -- !(WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s : stmt)
                      (CVAL : [| e |] st => Z.zero)
                      (CSTEP : KEmpty |- (st, i, o) -- k --> c'),
    k |- (st, i, o) -- !(WHILE e DO s END) --> c'                
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

Ltac cps_bs_gen_helper k H HH :=
  destruct k eqn:K; subst; inversion H; subst;
  [inversion EXEC; subst | eapply bs_Seq; eauto];
  apply HH; auto.

Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof.
  generalize dependent S.
  induction EXEC; intros.
  - inversion DEF.
  - cps_bs_gen_helper k DEF bs_Skip.
  - cps_bs_gen_helper k DEF bs_Assign.
  - cps_bs_gen_helper k DEF bs_Read.
  - cps_bs_gen_helper k DEF bs_Write.
  - destruct k.
    + apply (IHEXEC S). apply DEF.
    + inversion DEF.
      apply SmokeTest.seq_assoc.
      apply IHEXEC. auto.
  - destruct k; inversion DEF.
    + subst. apply bs_If_True.
      auto. auto.
    + assert ((s, i, o) == s1 ;; s0 ==> (c')).
      { apply IHEXEC. auto. }
      inversion H. subst.
      apply bs_Seq with (c'0). apply bs_If_True.
      auto. auto. auto.
  - destruct k; inversion DEF.
    + subst. apply bs_If_False. auto. auto.
    + assert ((s, i, o) == s2 ;; s0 ==> (c')).
      { apply IHEXEC. auto. }
      inversion H. subst.
      apply bs_Seq with (c'0). apply bs_If_False.
      auto. auto. auto.
  - destruct k; inversion DEF.
    + subst.
      assert ((st, i, o) == s ;; (WHILE e DO s END) ==> c').
      { auto. }
      inversion H. subst.
      apply bs_While_True with (c'0).
      auto. auto. auto.
    + subst.
      assert ((st, i, o) == s ;; (WHILE e DO s END) ;; s0 ==> c').
      { auto. }
      inversion H. subst.
      inversion_clear STEP2. apply bs_Seq with (c'1).
      apply bs_While_True with (c'0).
      auto. auto. auto. auto.
  - cps_bs_gen_helper k DEF bs_While_False.
Qed.
        
Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  apply (cps_bs_gen (s1 ;; s2) c c' !(s1) !(s2) STEP).
  auto.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof.
  apply (cps_bs_gen (s) c c' !(s) KEmpty STEP).
  auto.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  destruct k1; destruct k2; unfold Kapp.
  - auto.
  - destruct k3; unfold Kapp in STEP; inversion STEP.
  - unfold Kapp in STEP. auto.
  - apply cps_Seq. auto.
Qed.
             
Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  generalize dependent k.
  induction EXEC; intros.
  - auto.
  - apply cps_Assign with (z). auto.
    inversion STEP. auto.
  - apply cps_Read.
    inversion STEP.
    auto.
  - apply cps_Write with (z). auto.
    inversion STEP. auto.
  - apply cps_Seq. apply IHEXEC1.
    apply cps_Skip.
    apply cps_cont_to_seq.
    apply IHEXEC2.
    destruct k. auto. auto.
  - apply cps_If_True. auto. auto.
  - apply cps_If_False. auto. auto.
  - apply cps_While_True. auto.
    apply IHEXEC1.
    apply cps_Skip. apply cps_cont_to_seq. 
    destruct k. auto. auto.
  - apply cps_While_False. auto.
    inversion_clear STEP. auto.
Qed.
    
Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  induction EXEC.
  - constructor. constructor.
  - econstructor. apply VAL. constructor.
  - constructor. constructor.
  - econstructor. apply VAL. constructor.
  - constructor.
    apply bs_int_to_cps_int_cont with (c').
    auto. constructor. auto.
  - constructor. auto. auto.
  - apply cps_If_False. auto. auto.
  - constructor. auto.
    apply bs_int_to_cps_int_cont with (c').
    auto. constructor. auto.
  - apply cps_While_False. auto.
    constructor.
Qed.  
    
(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
