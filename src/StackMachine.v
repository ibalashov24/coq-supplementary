Require Import List.
Import ListNotations.
Require Import Omega.

From Bignums Require Export BigZ.
Require Export Id.
Require Export State.
Require Export Expr.
Require Export Stmt.

(* Configuration *)
Definition conf := (list Z * state Z * list Z * list Z)%type.

(* Straight-line code (no if-while) *)
Module StraightLine.

  (* Straigh-line statements *)
  Inductive StraightLine : stmt -> Set :=
  | sl_Assn  : forall x e, StraightLine (x ::= e)
  | sl_Read  : forall x  , StraightLine (READ x)
  | sl_Write : forall e  , StraightLine (WRITE e)
  | sl_Skip  : StraightLine SKIP
  | sl_Seq   : forall s1 s2 (SL1 : StraightLine s1) (SL2 : StraightLine s2),
      StraightLine (s1 ;; s2).

  (* Instructions *)
  Inductive insn : Type :=
  | R  : insn
  | W  : insn
  | C  : Z -> insn
  | L  : id -> insn
  | S  : id -> insn
  | B  : bop -> insn.

  (* Program *)
  Definition prog := list insn.

  (* Big-step evaluation relation*)
  Reserved Notation "c1 '--' q '-->' c2" (at level 0).
  Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

  Inductive sm_int : conf -> prog -> conf -> Prop :=
  | sm_End   : forall (p : prog) (c : conf),
      c -- [] --> c

  | sm_Read  : forall (q : prog) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (z::s, m, i, o) -- q --> c'),
      (s, m, z::i, o) -- R::q --> c'

  | sm_Write : forall (q : prog) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (s, m, i, z::o) -- q --> c'),
      (z::s, m, i, o) -- W::q --> c'

  | sm_Load  : forall (q : prog) (x : id) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (VAR : m / x => z)
                      (EXEC : (z::s, m, i, o) -- q --> c'),
      (s, m, i, o) -- (L x)::q --> c'
                   
  | sm_Store : forall (q : prog) (x : id) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (s, m [x <- z], i, o) -- q --> c'),
      (z::s, m, i, o) -- (S x)::q --> c'
                      
  | sm_Add   : forall (p q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : ((x + y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Add)::q --> c'
                         
  | sm_Sub   : forall (p q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : ((x - y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Sub)::q --> c'
                         
  | sm_Mul   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : ((x * y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Mul)::q --> c'
                         
  | sm_Div   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (NZERO : ~ y = Z.zero)
                      (EXEC : ((Z.div x y)::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Div)::q --> c'
                         
  | sm_Mod   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (NZERO : ~ y = Z.zero)
                      (EXEC : ((Z.modulo x y)::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Mod)::q --> c'
                         
  | sm_Le_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.le x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Le)::q --> c'
                         
  | sm_Le_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.gt x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Le)::q --> c'
                         
  | sm_Ge_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.ge x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ge)::q --> c'
                         
  | sm_Ge_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.lt x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ge)::q --> c'
                         
  | sm_Lt_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.lt x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Lt)::q --> c'
                         
  | sm_Lt_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.ge x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Lt)::q --> c'
                         
  | sm_Gt_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.gt x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Gt)::q --> c'
                         
  | sm_Gt_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.le x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Gt)::q --> c'
                         
  | sm_Eq_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.eq x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Eq)::q --> c'
                         
  | sm_Eq_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : ~ Z.eq x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Eq)::q --> c'
                         
  | sm_Ne_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : ~ Z.eq x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ne)::q --> c'
                         
  | sm_Ne_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.eq x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ne)::q --> c'
                         
  | sm_And   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (BOOLX : zbool x)
                      (BOOLY : zbool y)
                      (EXEC : ((x * y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B And)::q --> c'
                         
  | sm_Or    : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (BOOLX : zbool x)
                      (BOOLY : zbool y)
                      (EXEC : ((zor x y)::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Or)::q --> c'
                         
  | sm_Const : forall (q : prog) (n : Z) (m : state Z)
                      (s i o : list Z) (c' : conf) 
                      (EXEC : (n::s, m, i, o) -- q --> c'),
      (s, m, i, o) -- (C n)::q --> c'
  where "c1 '--' q '-->' c2" := (sm_int c1 q c2).
  
  (* Expression compiler *)
  Fixpoint compile_expr (e : expr) :=
  match e with
  | Var  x       => [L x]
  | Nat  n       => [C n]
  | Bop op e1 e2 => compile_expr e1 ++ compile_expr e2 ++ [B op]
  end.

  (* Partial correctness of expression compiler *)
  Lemma compiled_expr_correct_cont
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (p : prog) (c : conf)
        (VAL : [| e |] st => n)
        (EXEC: (n::s, st, i, o) -- p --> c) :        
    (s, st, i, o) -- (compile_expr e) ++ p --> c.
  Proof.
    generalize dependent o.
    generalize dependent i.
    generalize dependent s.
    generalize dependent p.

    induction VAL; intros; simpl.
    1: apply sm_Const. auto.
    1: apply sm_Load with (z). auto. auto.
    all:
      simpl; rewrite <- app_assoc; apply IHVAL1;
      rewrite <- app_assoc; apply IHVAL2;
      [> apply sm_Add |
         apply sm_Sub |
         apply sm_Mul |
         apply sm_Div |
         apply sm_Mod |
         apply sm_Le_T |
         apply sm_Le_F |
         apply sm_Lt_T |
         apply sm_Lt_F |
         apply sm_Ge_T |
         apply sm_Ge_F |
         apply sm_Gt_T |
         apply sm_Gt_F |
         apply sm_Eq_T |
         apply sm_Eq_F |
         apply sm_Ne_T |
         apply sm_Ne_F |
         apply sm_And |
         apply sm_Or]; auto; auto.
  Qed.
           
  Hint Resolve compiled_expr_correct_cont.
  
  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof.
    induction e.
    - constructor. inversion VAL. constructor. exact [].
    - econstructor. inversion VAL. apply VAR. constructor. exact [].
    - simpl.
      inversion_clear VAL.
      all:
        apply compiled_expr_correct_cont with (za); auto;
        apply compiled_expr_correct_cont with (zb); auto;
        try (econstructor; try econstructor; auto; exact []);
        econstructor; auto; econstructor; exact [].
  Qed.
  
  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof.
    generalize dependent s.
    generalize dependent i.
    generalize dependent o.
    generalize dependent p.

    induction e; intros.
    - inversion EXEC. exists z. split. auto. auto.
    - inversion EXEC. exists z. split. auto. auto.
    - simpl in EXEC.
      rewrite <- app_assoc in EXEC. rewrite <- app_assoc in EXEC.
      apply IHe1 in EXEC. destruct EXEC as [z1 [VAL1 EXEC2]].
      apply IHe2 in EXEC2. destruct EXEC2 as [z2 [VAL2 EXEC_BOP]].
      simpl in EXEC_BOP.
      inversion EXEC_BOP; subst.
      all:
        try (exists Z.one; split; auto; econstructor; try (apply VAL1); try (apply VAL2); auto).
      all:
        try (exists Z.zero; split; auto; econstructor; try (apply VAL1); try (apply VAL2); auto).
      + exists (z1 + z2)%Z. auto.
      + exists (z1 - z2)%Z. auto.
      + exists (z1 * z2)%Z. auto.
      + exists (Z.div z1 z2)%Z. auto.
      + exists (Z.modulo z1 z2)%Z. auto.
      + exists (z1 * z2)%Z. auto.
      + exists (zor z1 z2)%Z. auto.
  Qed.
     
  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof.
    generalize dependent s.
    generalize dependent o.
    generalize dependent i.
    generalize dependent st.
    generalize dependent n.

    induction e; intros.
    - simpl in EXEC. inversion_clear  EXEC.
      inversion_clear EXEC0. subst. auto.
    - simpl in EXEC. inversion_clear EXEC.
      inversion EXEC0. subst. constructor. auto.
    - simpl in EXEC;
      apply compiled_expr_not_incorrect_cont in EXEC;
      destruct EXEC; destruct H;
      apply compiled_expr_not_incorrect_cont in H0;
      destruct H0; destruct H0;
      destruct b;
      inversion H1; inversion EXEC; subst;
        econstructor; auto; auto; try (apply H);
          try (apply H0); auto.
  Qed.
      
  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o) <-> [| e |] st => n.
  Proof.
    split; intros.
    - apply (compiled_expr_not_incorrect e st s i o n H).
    - apply compiled_expr_correct. auto.
  Qed.
  
  Fixpoint compile (s : stmt) (H : StraightLine s) : prog :=
    match H with
    | sl_Assn x e          => compile_expr e ++ [S x]
    | sl_Skip              => []
    | sl_Read x            => [R; S x]
    | sl_Write e           => compile_expr e ++ [W]
    | sl_Seq s1 s2 sl1 sl2 => compile s1 sl1 ++ compile s2 sl2
    end.

  Lemma compiled_straightline_correct_cont
        (p : stmt) (Sp : StraightLine p) (st st' : state Z)
        (s i o s' i' o' : list Z)
        (H : (st, i, o) == p ==> (st', i', o')) (q : prog) (c : conf)
        (EXEC : ([], st', i', o') -- q --> c) :
    ([], st, i, o) -- (compile p Sp) ++ q --> c.
  Proof.
    generalize dependent q.
    generalize dependent o'.
    generalize dependent i'.
    generalize dependent st'.
    generalize dependent o.
    generalize dependent i.
    generalize dependent st.
    
    induction Sp; intros; simpl.
    - rewrite <- app_assoc. simpl.
      inversion H. subst.
      apply compiled_expr_correct_cont with (z).
      auto. constructor. auto.
    - inversion H. subst.
      constructor. constructor. auto.
    - inversion H. subst.
      rewrite <- app_assoc.
      apply compiled_expr_correct_cont with (z).
      auto. constructor. auto.
    - inversion H. subst. auto.
    - inversion H.
      rewrite <- app_assoc.
      destruct c'. destruct p.
      apply IHSp1 with (s4) (l0) (l).
      auto.
      apply IHSp2 with (st') (i') (o').
      auto. auto.
  Qed.   
     
  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    generalize dependent st.
    generalize dependent i.
    generalize dependent o.
    
    induction Sp; simpl; intros.
    - inversion EXEC. subst.
      apply compiled_expr_correct_cont with (z).
      auto. constructor. constructor. exact [].
    - inversion EXEC. subst.
      constructor. constructor. constructor. exact [].
    - inversion EXEC. subst.
      apply compiled_expr_correct_cont with (z).
      auto. constructor. constructor. exact [].
    - inversion EXEC. constructor. exact [].
    - inversion EXEC. subst. destruct c'. destruct p.
      apply compiled_straightline_correct_cont with (s) (l0) (l).
      exact []. exact []. auto. auto.
  Qed.
     
  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof.
    generalize dependent st.
    generalize dependent i.
    generalize dependent o.
    generalize dependent q.
    
    induction Sp; simpl; intros.
    - rewrite <- app_assoc in EXEC.
      apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC. destruct H.
      exists st [x <- x0]. exists i. exists o.
      split. 
      constructor. auto.
      inversion H0. auto.
    - inversion EXEC. subst.
      inversion EXEC0. subst.
      exists st [x <- z]. exists i0. exists o.
      split.
      constructor. auto.
    - rewrite <- app_assoc in EXEC.
      apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC. destruct H.
      exists st. exists i. exists (x :: o).
      split.
      + constructor. auto.
      + inversion H0. auto.
    - exists st. exists i. exists o.
      split. constructor. auto.
    - rewrite <- app_assoc in EXEC.
      apply IHSp1 in EXEC.
      destruct EXEC.
      destruct H. destruct H. destruct H.
      apply IHSp2 in H0.
      destruct H0. destruct H0. destruct H0. destruct H0.
      exists x2. exists x3. exists x4.
      split.
      econstructor. apply H. auto.
      auto.
  Qed.
      
  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof.
    generalize dependent st.
    generalize dependent i.
    generalize dependent o.
    
    induction Sp; intros; simpl in EXEC.
    - apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC. destruct H.
      inversion H0. inversion EXEC.
      constructor. auto.
    - inversion EXEC. subst.
      inversion EXEC0. subst.
      inversion EXEC1. subst.
      constructor.
    - apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC. destruct H.
      inversion H0. inversion EXEC. subst.
      constructor. auto.
    - inversion EXEC. constructor.
    - apply compiled_straightline_not_incorrect_cont in EXEC.
      destruct EXEC. destruct H. destruct H. destruct H.
      apply IHSp2 in H0. auto.
      econstructor. apply H. auto.
  Qed.
      
  Theorem straightline_compiler_correct
          (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z) :
    (st, i, o) == p ==> (st', i', o') <-> ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof. 
    split; intros.
    - apply compiled_straightline_correct. auto.
    - apply compiled_straightline_not_incorrect with (Sp). auto.
  Qed.
      
End StraightLine.

