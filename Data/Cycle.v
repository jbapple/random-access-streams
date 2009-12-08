Set Implicit Arguments.

Require Import Setoid.
Require Import List.
Require Import Coq.Init.Wf.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.Div2.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Euclid.
Require Import Recdef.

Section type.

CoInductive CoList (A:Set) : Set :=
| Nil : CoList A
| Cons : A -> CoList A -> CoList A.

CoInductive cleq (A:Set) : CoList A -> CoList A -> Prop :=
| nileq : cleq (@Nil _) (@Nil _)
| conseq : forall x y xs ys,
           x = y ->
           cleq xs ys ->
           cleq (Cons x xs) (Cons y ys).

Inductive FiniteCoList (A:Set) : CoList A -> nat -> Prop :=
| FiniteNil : FiniteCoList (Nil A) 0
| FiniteCons : forall hed tyl n, 
  FiniteCoList tyl n
  -> FiniteCoList (Cons hed tyl) (S n).

CoInductive InfiniteCoList (A:Set) : CoList A -> Prop :=
| InfiniteCons : forall hed tyl,
  InfiniteCoList tyl -> InfiniteCoList (Cons hed tyl).

CoInductive Stream (A:Set) : Set :=
| More : A -> Stream A -> Stream A.

CoFixpoint streamCycle' (A:Set) (x:A) (xs:CoList A) (rest:CoList A)
  : Stream A :=
  match rest with
    | Nil => More x (streamCycle' x xs xs)
    | Cons y ys => More y (streamCycle' x xs ys)
  end.

Definition streamCycle (A:Set) (x:A) (xs:CoList A) : Stream A :=
  streamCycle' x xs (Cons x xs).

CoInductive Braun (A:Set) : Set :=
| Conb : A -> Braun A -> Braun A -> Braun A.

Definition frobb n (x:Braun n) : Braun n :=
  match x with
    | Conb h o e => Conb h o e
  end.

Lemma frobbeq : forall A (x:Braun A), x = frobb x.
Proof.
  destruct x; simpl; reflexivity.
Qed.


Fixpoint applyn (A:Set) (n:nat) (f:A->A) (x:A) : A :=
  match n with
    | 0 => x
    | S m => f (applyn m f x)
  end.

Fixpoint bat (A:Set) (x:Braun A) (b:list bool) {struct b} 
  : A :=
  match x with
    | Conb h o e =>
      match b with
        | nil => h
        | true  :: r => bat o r
        | false :: r => bat e r
      end
  end.

Fixpoint ord (x:list bool) : nat :=
  match x with
    | nil => 0
    | true::r  => 1 + 2*(ord r)
    | false::r => 2 + 2*(ord r)
  end.

Variable iterate: forall (A:Set), (A->A) -> A -> Braun A.

Variable iterp : 
  forall (A:Set) f (x:A) b, 
    applyn (ord b) f x
    = bat (iterate f x) b.


CoFixpoint repcl (A:Set) (x:A) :=
  Cons x (repcl x).

Definition frobcl (A:Set) (x:CoList A) : CoList A :=
  match x with
    | Nil => Nil _
    | Cons h t => Cons h t
  end.

Lemma frobeqcl :
  forall A (x:CoList A), frobcl x = x.
Proof.
  destruct x; simpl; reflexivity.
Qed.

Lemma infinf :
  forall (A:Set) (x:A), InfiniteCoList (repcl x).
Proof.
  clear.
  intros.
  cofix.
  remember (repcl x) as y.
  rewrite Heqy in infinf.
  Guarded.
  destruct y.
  rewrite <- frobeqcl in Heqy.
  simpl in Heqy.
  inversion Heqy.
  rewrite <- frobeqcl in Heqy.
  simpl in Heqy.
  inversion Heqy.
  subst.
  apply InfiniteCons.
  Guarded.
  apply infinf.
  Guarded.
Qed.

CoInductive BraunRef (A:Set) : Set :=
| Conr : A -> BraunRef A -> BraunRef A -> BraunRef A
| Ref : nat -> BraunRef A.

Inductive FiniteBraun (A:Set) : BraunRef A -> nat -> Prop :=
| FiniteRef : forall b, FiniteBraun (Ref A b) 1
| FiniteSum : forall h o e l r, 
  FiniteBraun o l ->
  FiniteBraun e r ->
  FiniteBraun (@Conr A h o e) (l+r).

CoInductive InfiniteBraun (A:Set) : BraunRef A -> Prop :=
| InfiniteConr : forall h o e,
  InfiniteBraun o ->
  InfiniteBraun e ->
  InfiniteBraun (Conr h o e).

CoFixpoint repbr (A:Set) (x:A) :=
  let r := repbr x in
  Conr x r r.


Definition frob n (x:BraunRef n) : BraunRef n :=
  match x with
    | Conr h o e => Conr h o e
    | Ref b => Ref _ b
  end.

Lemma frobeq : forall n (x:BraunRef n), x = frob x.
Proof.
  destruct x; simpl; reflexivity.
Qed.

Lemma infbr :
  forall (A:Set) (x:A), InfiniteBraun (repbr x).
Proof.
  clear.
  intros.
  cofix.
  remember (repbr x) as y.
  rewrite Heqy in infbr.
  Guarded.
  destruct y.
  rewrite frobeq in Heqy.
  simpl in Heqy.
  inversion Heqy.
  subst.
  clear Heqy.
  apply InfiniteConr.
  apply infbr.
  apply infbr.
  Guarded.
  rewrite frobeq in Heqy.
  simpl in Heqy.
  inversion Heqy.
  Guarded.
Qed.

Fixpoint concrete A (b:BraunRef A) (l:list bool) : Prop :=
  match b with
    | Conr _ o e =>
      match l with
        | nil => True
        | true::tl => concrete o tl
        | false::tl => concrete e tl
      end
    | _ => False
  end.

Variable riterate: forall (A:Set), (A->A) -> A -> BraunRef A.

Fixpoint upto' A (x:BraunRef A) r b :=
  match b with
    | nil => (x,(rev r,nil))
    | c::d => 
      match x with
        | Conr h o e =>
          match c with
            | true  => upto' o (c::r) d
            | false => upto' e (c::r) d
          end
        | Ref v => (x,(rev r,b))
      end
  end.
(*
Fixpoint uptoo A (x:BraunRef A) r b :=
  match b with
    | nil => 
      match x with
        | Conr h _ _ => inl h
        | Ref v => inr (v,(rev r,nil))
    | c::d => 
      match x with
        | Conr h o e =>
          match c with
            | true  => upto' o (c::r) d
            | false => upto' e (c::r) d
          end
        | Ref v => (x,(rev r,b))
      end
  end.
*)
Definition upto A x b := @upto' A x nil b.

Require Import List.

Lemma appnil :
  forall A x (y:A) z,
    (x ++ y::nil)++z = x ++ y::z.
Proof.
  clear; induction x; intros.
  simpl. auto.
  simpl.
  erewrite IHx. auto.
Qed.

Lemma revapp :
  forall A y (x:A) z,
    rev (x :: y) ++ z = rev y ++ x::z.
Proof.
  clear; induction y; intros.
  simpl. auto.
  simpl.
  erewrite <- IHy.
  rewrite appnil. auto.
Qed.

Lemma uptoAppend :
  forall A b c x, 
    let (_,ht) := @upto' A x c b in
      let (hed,tyl) := ht in
        hed++tyl = (rev c)++b.
Proof.
  clear.
  intros.
  remember (upto' x c b) as uxb.
  destruct uxb.
  destruct p.

  generalize dependent l0.
  generalize dependent x.
  generalize dependent b0.
  generalize dependent c.
  generalize dependent b.
  induction l; induction b; destruct x; intros; unfold upto in Hequxb; unfold upto' in Hequxb; simpl in *; inversion Hequxb; auto.
  fold (upto' x2 (a::c) b) in *.
  fold (upto' x1 (a::c) b) in *.
  destruct a.
  transitivity (rev (true::c) ++ b).
  eapply IHb. apply Hequxb.
  apply revapp.
  transitivity (rev (false::c) ++ b).
  eapply IHb. apply Hequxb.
  apply revapp.
  fold (upto' x2 (a0::c) b) in *.
  fold (upto' x1 (a0::c) b) in *.
  destruct a0.
  transitivity (rev (true::c) ++ b).
  eapply IHb. apply Hequxb.
  apply revapp.
  transitivity (rev (false::c) ++ b).
  eapply IHb. apply Hequxb.
  apply revapp.
Qed.

(*
Fixpoint rbat (A:Set) (x:BraunRef A) (b:list bool) {struct b} 
  : option (A + nat) :=
  match x with
    | Conr h o e =>
      match b with
        | nil => Some (inl _ h)
        | true  :: r => rbat o r
        | false :: r => rbat e r
      end
    | Ref n =>
      match b with
        | nil => Some (inr _ n)
        | _ => None
      end
  end.
*)
Fixpoint evenp (n:nat) : nat+nat :=
  match n with
    | 0 => inl _ 0
    | 1 => inr _ 0
    | S (S m) => 
      match evenp m with
        | inl a => inl _ (S a)
        | inr a => inr _ (S a)
      end
  end.

Lemma evenis : let P n :=
  match evenp n with
    | inl x => x+x = n
    | inr x => 1+x+x = n
  end
  in forall n, P n.
Proof.
  clear.
  intros.
  apply lt_wf_ind.
  intros.
  unfold P in *.
  clear P.
  destruct n0.
  simpl; auto.
  simpl.
  destruct n0.
  auto.
  remember (evenp n0) as en.
  destruct en.
  assert (n1+n1 = n0).
  assert (match evenp n0 with
            | inl z => z + z = n0
            | inr z => 1 + z + z = n0
          end).
  apply H.
  auto.
  rewrite <- Heqen in H0.
  auto.
  auto with arith.
  omega.
  assert (match evenp n0 with
            | inl z => z + z = n0
            | inr z => 1 + z + z = n0
          end).
  apply H.
  auto.
  rewrite <- Heqen in H0.
  omega.
Qed.

Lemma evenleft : forall n x, 
  evenp n = inl _ x -> x+x = n.
Proof.
  clear.
  intros.
  assert (match evenp n with
            | inl x => x+x = n
            | inr x => 1+x+x = n
          end).
  apply evenis.
  rewrite H in H0. auto.
Qed.

Lemma evenright : forall n x, 
    evenp n = inr _ x -> 1+x+x = n.
Proof.
  clear.
  intros.
  assert (match evenp n with
            | inl x => x+x = n
            | inr x => 1+x+x = n
          end).
  apply evenis.
  rewrite H in H0. auto.
Qed.

Function unord (x:nat) {measure id x} : list bool :=
  match x with
    | 0 => nil
    | S y => 
      match evenp y with
        | inl a => true :: unord a
        | inr a => false :: unord a
      end
  end.
clear; intros.
unfold id.
induction y.
simpl in teq0.
inversion teq0.
auto.
simpl in teq0.
clear IHy.
destruct y.
inversion teq0.
remember (evenp y) as ey.
destruct ey.
Check evenleft.
inversion teq0.
subst.
clear teq0.
Check evenleft.
assert (n+n=y).
apply evenleft. auto.
omega.
inversion teq0.
intros.
unfold id.
subst.
assert (1 + a + a = y).
apply evenright.
auto.
omega.
Defined.

Lemma eventwo : forall x, evenp (x+x) = inl _ x.
Proof.
  clear.
  induction x.
  auto.
  remember (S x + S x) as y.
  assert (y = S (S (x+x))).
  omega.
  subst.
  rewrite H.
  unfold evenp.
  simpl.
  fold (evenp (x + x)).
  rewrite IHx.
  reflexivity.
Qed.

Lemma eventhree : forall x, evenp (S (x+x)) = inr _ x.
Proof.
  clear.
  induction x.
  auto.
  remember (S (S x + S x)) as y.
  assert (y = S (S (S (x+x)))).
  omega.
  subst.
  rewrite H.
  unfold evenp.
  simpl.
  fold (evenp (S (x + x))).
  rewrite IHx.
  reflexivity.
Qed.

Lemma unt : forall x, unord (ord x) = x.
Proof.
  clear.
  induction x.
  auto.
  destruct a.
  simpl.
  assert (forall y, y + y = y + (y + 0)).
  intros.
  omega.
  rewrite <- H.
  simpl.
  rewrite unord_equation.
  rewrite eventwo.
  f_equal. auto.
  simpl.
  assert (forall y, y + y = y + (y + 0)).
  intros.
  omega.
  rewrite <- H.
  rewrite unord_equation.
  rewrite eventhree.
  f_equal. auto.
Qed.

Lemma tun : let P x := ord (unord x) = x in 
  forall x, P x.
Proof.
  clear.
  intros.
  apply lt_wf_ind.
  intros.
  unfold P in *.
  clear P.
  destruct n.
  auto.
  rewrite unord_equation.
  remember (evenp n) as en.
  destruct en.
  simpl.
  rewrite H.
  f_equal.
  transitivity (n0 + n0).
  omega.
  apply evenleft. auto.
  Check evenleft.
  assert (n0 + n0 = n).
  apply evenleft.
  auto.
  omega.
  simpl.
  f_equal.
  rewrite H.
  transitivity (S (n0 + n0)).
  auto with arith.
  transitivity (1 + n0 + n0).
  auto with arith.
  apply evenright.
  auto.
  assert (1 + n0 + n0 = n).
  apply evenright. auto.
  omega.
Qed.

Definition WellBraun A (x:BraunRef A) :=
  forall b,
    let (res,ht) := upto x b in
      let (hed,tyl) := ht in 
        match res with
          | Ref v => v < (ord hed)
          | _ => True
        end.
(*
      | ( => True
      | Some (inl _) => True
      | Some (inr n) => n < (ord b) (*
        match rbat x (unord n) with
          | Some (inl _) => True
          | _ => False
        end *)
    end.
*)
Print BraunRef.

Print rev.

Locate "_ ++ _".
(*
Print rbat.

Lemma uptorbat : 
  forall A b (x:BraunRef A),
    match rbat x b with
      | None => exists t, exists v, upto x b = (Ref _ v, t)
      | Some (inl h) => exists o, exists e, upto x b = (Conr h o e, nil)
        =>(Ref= Some (inr _ v) <-> exists t, upto x b = (Ref _ v, t).
Proof.
  clear; induction b; intros.
  simpl. split; intros.
  destruct x.
  inversion H.
  inversion H. exists nil. auto.
  destruct H. inversion H. auto.
  destruct a; split; intros;  destruct x.
  apply (IHb x1 v); auto.
  inversion H. 
  apply (IHb x1 v); auto.
  destruct H; inversion H; subst; clear H.
  transitivity (rbat (Ref A v) nil).
  simpl.
  eapply (IHb (Ref A v)
*)  
  

Fixpoint pow x y :=
  match y with
    | 0 => 1
    | S z => x * pow x z
  end.

Eval compute in ord(unord 4 ++ true :: nil).
Eval compute in ord(unord 40 ++ true :: nil).
Eval compute in ord(unord 6 ++ true :: nil).
Eval compute in ord(unord 8 ++ true :: nil).
Eval compute in unord 8.
Eval compute in length(unord 40).
Eval compute in length(unord 38).
Eval compute in ord(unord 38 ++ true :: nil).
Eval compute in length(unord 5).
Eval compute in ord(unord 5 ++ true :: nil).
Eval compute in 
  let f a b :=
    (ord (unord a ++ b::nil),
      a + pow 2 (length (unord a)) + if b then 0 else a)
    in 
    f 0 true :: f 1 true :: f 2 true :: f 3 true :: f 4 true  ::
    f 0 false :: f 1 false :: f 2 false :: f 3 false :: f 4 false ::
    nil.

Lemma ordAppendOne :
  forall a b, ord (a ++ b::nil) = 
    ord a 
    + pow 2 (length a) * ord (b::nil).
Proof.
  clear.
  induction a; intros.
  simpl. destruct b; auto.
  simpl. destruct a; destruct b; simpl; try rewrite IHa; simpl; try omega.
Qed.
  
Lemma ordLengthMax :
  forall a, S (ord a) < pow 2 (S (length a)).
Proof.
  clear; induction a; simpl.
  omega.
  destruct a; simpl.
  unfold pow in IHa; fold (pow 2 (length a0)) in *; try omega.
  unfold pow in IHa; fold (pow 2 (length a0)) in *; try omega.
Qed.

Lemma ordLengthMin :
  forall a, S (ord a) >= pow 2 (length a).
Proof.
  clear; induction a; simpl.
  omega.
  destruct a; simpl; omega.
Qed.

Lemma powMono :
  forall x y, x <= y -> pow 2 x <= pow 2 y.
Proof.
  clear.
  intros.
  induction H. auto.
  unfold pow; fold (pow 2 x); fold (pow 2 m). omega.
Qed.


Lemma ordLength :
  forall a b, ord a < ord b ->
    length a <= length b.
Proof.
  clear.
  intros.
  remember (lt_eq_lt_dec (length a) (length b)) as ll.
  destruct ll as [[alb|aeb]|bla]; try omega.
  clear Heqll.
  assert (ord b < ord a).
  assert (S (ord b) < pow 2 (S (length b))); try apply ordLengthMax.
  assert (pow 2 (length a) <= S (ord a)); try apply ordLengthMin.
  assert (pow 2 (S (length b)) <= pow 2 (length a)).
  apply powMono. omega. omega. omega.
Qed.

Lemma multLess :
  forall a b c,
    a <= b -> a*c <= b*c.
Proof.
  clear; intros.
  induction H. auto.
  simpl. omega.
Qed.

Lemma ordAppend :
  forall d b c,
    ord b < ord c -> ord (b ++ d) < ord (c ++ d).
Proof.
  clear.
  induction d; simpl; intros.
  ssimpl_list; auto.
  assert (ord ((b ++ a::nil)++d) < ord ((c ++ a::nil)++d)).
  apply IHd.
  rewrite ordAppendOne.
  rewrite ordAppendOne.
  assert (length b <= length c); try apply ordLength; auto.
  assert (pow 2 (length b) <= pow 2 (length c)). eapply powMono. auto.
  assert (pow 2 (length b) * ord (a::nil) <= pow 2 (length c) * ord (a::nil)).
  apply multLess. auto.
  omega.
  rewrite appnil in H0.
  rewrite appnil in H0.
  apply H0.
Qed.

Print Assumptions ordAppend.

Function find (A:Set) (x:BraunRef A) (p:WellBraun x) (b:list bool) 
  {measure ord b} : A :=
  let (ans,ht) := upto x b in
    let (hed,tyl) := ht in
      match ans with
        | Conr h _ _ => h
        | Ref v => find p ((unord v)++tyl)
      end.
clear; intros.
unfold WellBraun in p.
pose (p b).
rewrite teq in y.
assert (hed ++ tyl = b).
transitivity (rev nil ++ b).
pose (@uptoAppend A b nil x) as I.
fold (upto x b) in I.
rewrite teq in I. auto.
simpl. auto.
subst.
apply ordAppend.
rewrite tun. auto.
Defined.

Print find.
Print find_tcc.
Check find_tcc.
Check find_terminate.
Check find_ind.
(*
Print find_rec
Print find_rect
Print R_find_correct
Print R_find_complete
*)
Print find_equation.
Check find_equation.


Print Assumptions find.



(*

Definition WellBraun A (b:BraunRef A) := forall l,
  FiniteBraun b l -> fold_left and (map (concrete b) (map unord l)) True.
*)
Check (1,2).
Print option.

Check (inl (list nat) (inl bool 0)).

Check modulo.
(*
Program Fixpoint sub (n:nat) (m:nat) (p:m<n) :=
  match n with
    | 0 => 0
    | S n' => 
      match m with
        | 0 => n
        | S m' => @sub n' m' _
      end
  end.
Next Obligation.
  auto with arith.
Defined.

Locate "{ _ } + { _ }".
Print sumbool.
Print sumor.

Program Fixpoint mymod (n:nat) (m:nat) {measure id n} := 
  match lt_eq_lt_dec n m with
    | inleft (left _) => n
    | inleft (right _) => 0
    | inright p => mymod () m
  end.
Next Obligation.
  unfold id.
  generalize dependent m.
  induction n.
  intros.
  inversion p.
  intros.
  unfold sub.
  unfold sub
  simpl.
*)

Locate "{ _ | _ }".
Check modulo.
Print sig.
Check modulo.
(*
Definition mymod : nat -> nat -> nat.
refine ( fun m n =>
  match n with 
    | 0 => 0
    | S j => 
      match modulo (S j) _ m with
        | exist r _ => r
      end
  end).
auto with arith.
Defined.
*)

Function mymod (n:nat) (m:nat) {measure id n} : nat :=
  match m with
    | 0 => 0
    | _ =>
      match nat_compare n m with
        | Lt => n
        | Eq => 0
        | Gt => mymod (n-m) m
      end
  end.
clear.
intros.
unfold id.
apply lt_minus.
subst.
unfold nat_compare in teq0.
remember (lt_eq_lt_dec n (S n0)) as ll.
destruct ll.
destruct s.
inversion teq0.
inversion teq0.
auto with arith.
auto with arith.
Defined.

Check mymod_equation.

Lemma mymodUnder : forall x y, x < y -> mymod x y = x.
  clear; induction x; induction y; intros.
  inversion H.
  rewrite mymod_equation.
  remember (nat_compare 0 (S y)).
  destruct c.
  auto. auto.
  inversion Heqc.
  omega.
  rewrite mymod_equation.
  Locate "_ - _".
Admitted.


Lemma mymodUnderMe : forall x y, mymod x y <= x.
Admitted.


Lemma mymodUnderYou : forall x y, mymod x (S y) < (S y).
Admitted.

  

(*
Program Definition mymod (m:nat) (n:nat) :=
  match n with 
    | 0 => 0
    | _ => 
      match modulo n _ m with
        | r => r
      end
  end.
Next Obligation.
  auto with arith.
Defined.
*)
Print mymod.

Print mymod.
Print modulo.
Check modulo.

Fixpoint is2pow' (n:nat) i := 
  match i with
    | 0 => 
      match n with
        | 1 => Some i
        | _ => None
      end
    | S j =>
      match nat_compare n (pow 2 i) with
        | Lt => is2pow' n j
        | Eq => Some i
        | Gt => None
      end
  end.

Definition is2pow n := 
  match is2pow' n n with
    | Some _ => true
    | _ => false
  end.

Lemma is2c :
  let P n := forall m j, is2pow' n m = Some j 
      -> exists i, pow 2 i = n
        in forall n, P n.
Proof.
  clear.
  
  intros.
  (*apply lt_wf_ind.*)
  intros.
  unfold P in *.
  clear P.
  induction m; induction j; intros.
  exists 0.
  simpl in H. simpl.
  destruct n. inversion H.
  destruct n. auto.
  inversion H.
  simpl in H.
  destruct n. inversion H.
  destruct n. inversion H. inversion H.
  simpl in H.
  remember (nat_compare n (pow 2 m + (pow 2 m + 0))) as z.
  destruct z.
  inversion H.
  apply IHm in H. auto.
  inversion H.
  simpl in H.
  remember (nat_compare n (pow 2 m + (pow 2 m + 0))) as z.
  destruct z.
  inversion H. subst. clear H.
  exists (S j).
  simpl.
  unfold nat_compare in Heqz.
  remember (lt_eq_lt_dec n (pow 2 j + (pow 2 j + 0))) as q.
  destruct q.
  destruct s.
  inversion Heqz.
  auto.
  inversion Heqz.
  eapply IHm.
  apply H.
  inversion H.
Qed.

Lemma is2cc : forall n,
  is2pow n = true 
      -> exists i, pow 2 i = n.
Proof.
  clear.
  unfold is2pow.
  intros n.
  remember (is2pow' n n) as m.
  destruct m.
  intros.
  Check is2c.
  Check (is2c n).
  Check (is2c n n).
  Check (@is2c n n n0).
  apply (@is2c n n n0).
  auto.
  intros.
  inversion H.
Qed.

(*
Fixpoint incrof (n:nat) := n.
*)
Program Fixpoint floorlg x {measure id x} :=
  match div2 x with
    | 0 => 0
    | y => S (floorlg y)
  end.
Next Obligation.
  apply lt_div2.
  induction x.
  simpl in H. 
  auto with arith.
  unfold id.
  auto with arith.
Defined.

Function floorlg2 (x:nat) {measure id x} :nat :=
  match div2 x with
    | 0 => 0
    | y => S (floorlg2 y)
  end.
clear; intros; destruct x.
unfold div2 in teq; inversion teq.
unfold id. 
rewrite <- teq.
apply lt_div2. 
auto with arith.
Defined.

Print floorlg2_equation.
Check floorlg2_equation.

Eval compute in (floorlg2 0).
Eval compute in (floorlg2 1).
Eval compute in (floorlg2 2).
Eval compute in (floorlg2 3).
Eval compute in (floorlg2 4).
Eval compute in (floorlg2 7).
Eval compute in (floorlg2 8).

Definition myincr real mod := mymod (pow 2 (floorlg2 (S real))) mod.

Print myincr.

Definition memo (n:nat) (pi : nat*nat) := 
  let (p,i) := pi in
    match (nat_compare p n,
           nat_compare i (myincr p n)) with
      | (Lt,Eq) => Some p
      | _ => None
    end.

Eval compute in (memo 4 (3,0)).
Eval compute in (memo 40 (3,0)).
Eval compute in (memo 40 (3,1)).
Eval compute in (memo 9 (3,2)).
Eval compute in (memo 9 (3,4)).
Eval compute in (memo 9 (8,8)).

Definition action 
  (A:Set) 
  (x:(nat*nat*(nat*nat->option nat))
    +(A * CoList A * nat))
  : (nat*nat*(nat*nat->option nat))
    +(A * CoList A * nat) :=
  match x with
    | inl (real,mod,f) => 
      inl _ 
      (S real,
       mod,
       match f (mymod real mod,myincr real mod) with
         | Some v => f
         | None => fun pi =>
           match pi with
             | (p,i) => 
               match (nat_compare p (mymod real mod),
                 nat_compare i (myincr real mod)) with
                 | (Eq,Eq) => Some real
                 | _ =>  f pi
               end
           end
       end)
    | inr (v,rem,sofar) =>
      match rem with
        | Nil => inl _ (S sofar,S sofar,memo (S sofar))
        | Cons hed tl => inr _ (hed,tl,S sofar)
      end
  end.

Definition BackAll f m n :=
  forall j, match f (mymod j m, myincr j m) with
              | None => j >= n
              | Some k => k <= j
            end.

Check applyn.

Locate "_ && _".

Lemma BackAllAction :
  forall (A:Set) (x:A) xs n,
  match applyn n (@action A) (inr _ (x,xs,0)) with
    | inl (r,m,f) => and (n = r) (and (r >= m) (BackAll f m r))
    | inr (y,ys,m) => m = n
  end.
Proof.
  clear; induction n.
  simpl. auto.
  intros.
  remember (applyn n (@action _) (inr _ (x,xs,0))) as s.
  destruct s.
  destruct p.
  destruct p.
  destruct IHn.
  destruct H0.
  simpl.
  rewrite <- Heqs.
  simpl. split.
  omega.
  split.
  auto with arith.
  remember (o (mymod n0 n1, myincr n0 n1)) as p.
  destruct p.
  unfold BackAll in *; intros.
  remember (o (mymod j n1, myincr j n1)) as q.
  destruct q;
    remember (lt_eq_lt_dec  j (n0)) as jn;
      destruct jn.
  destruct s.
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  apply H1.
  rewrite <- Heqq in H2.
  auto.
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  apply H1.
  rewrite <- Heqq in H2.
  auto.
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  apply H1.
  rewrite <- Heqq in H2.
  auto.
  destruct s.
  
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  apply H1.
  rewrite <- Heqq in H2.
  auto with arith.
  omega.
  clear Heqjn.
  subst.
  rewrite <- Heqq in Heqp.
  inversion Heqp.
  auto with arith.
  unfold BackAll in *.
  intros.
  subst.
  remember (lt_eq_lt_dec (mymod j n1) (mymod n0 n1)) as jn0.
  destruct jn0.
  destruct s.
  unfold nat_compare.
  rewrite <- Heqjn0.
  remember (o (mymod j n1, myincr j n1)) as oj.
  destruct oj.
  
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  apply H1.
  rewrite <- Heqoj in H.
  auto.
  assert (j >= n0).
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  
  apply H1.
  rewrite <- Heqoj in H.
  auto.
  destruct H.
  inversion l.
  omega.
  omega. omega.
  unfold nat_compare.
  rewrite <- Heqjn0.
  remember (lt_eq_lt_dec (myincr j n1) (myincr n0 n1)) as jn0.
  destruct jn0.
  destruct s.
  remember (o (mymod j n1, myincr j n1)) as oj.
  destruct oj.
  
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  apply H1.
  rewrite <- Heqoj in H.
  auto.
  assert (j >= n0).
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  
  apply H1.
  rewrite <- Heqoj in H.
  auto.
  destruct H.
  inversion l.
  omega. omega. omega.
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  
  apply H1.
  rewrite e in H.
  rewrite e0 in H.
  rewrite <- Heqp in H.
  auto.
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  
  apply H1.
  remember (o (mymod j n1, myincr j n1)) as oj.
  destruct oj.
  auto. auto with arith.
  destruct H.
  inversion l. omega. omega. omega.
  unfold nat_compare.
  rewrite <- Heqjn0.
  assert (match o (mymod j n1, myincr j n1) with
            | Some k => k <= j
            | None => j >= n0
          end).
  
  apply H1.
  remember (o (mymod j n1, myincr j n1)) as oj.
  destruct oj.
  auto. auto with arith.
  destruct H.
  inversion l. omega. omega. omega.
  simpl in IHn.
  destruct p.
  destruct p.
  subst.
  simpl.
  rewrite <- Heqs.
  simpl.
  destruct c. split. auto. split. auto.
  Print memo.
  unfold BackAll.
  unfold memo.
  intros.
  remember (lt_eq_lt_dec (mymod j (S n)) (S n)) as jsn.
  destruct jsn.
  destruct s.
  unfold nat_compare.
  rewrite <- Heqjsn.
  remember (lt_eq_lt_dec (myincr j (S n)) (myincr (mymod j (S n)) (S n))) as jj.
  destruct jj.
  destruct s.
  remember (lt_eq_lt_dec j (S n)) as jsn.
  destruct jsn.
  destruct s.
  assert ((mymod j (S n)) = j).
  apply mymodUnder. auto.
  inversion l0.
  rewrite H in H1.
  omega.
  rewrite H in H0.
  rewrite <- H0 in H1.
  omega.
  auto.
  auto with arith.
  omega.
  omega.
  apply mymodUnderMe.
  remember (lt_eq_lt_dec j (S n)) as jsn.
  destruct jsn.
  destruct s.
  
  assert (mymod j (S n) = j).
  apply mymodUnder.
  auto.
  inversion l0.
  rewrite H in H1.
  omega.
  rewrite H in H1.
  rewrite <- H0 in H1.
  omega.
  auto.
  omega.
  omega.
  unfold nat_compare.
  rewrite <- Heqjsn.
  assert (mymod j (S n) < (S n)).
  apply mymodUnderYou.
  omega.
  unfold nat_compare.
  rewrite <- Heqjsn.
  assert (mymod j (S n) < (S n)).
  apply mymodUnderYou.
  omega.
  auto.
Qed.

Print Assumptions BackAllAction.

Check BackAllAction.
Print BackAll.
(*
Lemma actionless :
  let P n := forall (A:Set) (x:A) xs,
    match applyn n (@action _) (inr _ (x,xs,0)) with
      | inl (r,m,f) =>
        forall s,
          match f (mymod s m, myincr s m) with
            | None => True
            | Some v => v <= s
          end
      | _ => True
    end
    in forall n, P n.
Proof.
  clear.
  intros.
  apply lt_wf_ind.
  intros.
  unfold P in *; clear P.
  destruct n0.
  simpl. intros.
  auto.
  simpl; intros.
  remember (applyn n0 (@action _)
          (inr (nat * nat * (nat * nat -> option nat)) (x, xs, 0))) as an.
  destruct an.
  destruct p.
  destruct p.
  simpl.
  intros.
  remember (o (mymod n1 n2, myincr n1 n2)) as on.
  destruct on.
  Check H.
  remember (o (mymod s n2, myincr s n2)) as os.
  destruct os.
  
  case (s <= n4).
  elim ns.
  
        
  forall r m f, 
    (forall s, s < r -> 
      match f (mymod s m, myincr s m) with
        | None => True
        | Some v => v < r
      end) ->
    match action (inl (r,m,f)) with
      | inl (t,u,g) ->
        match g (mymod r m, myincr s m) with
        | None => True
        | Some v => v < r
      end
*)
Print BraunRef.

Fixpoint mat' (A:Set) (whole:A * CoList A) (rem:CoList A) (n:nat) : A :=
  match n with
    | 0 => 
      match rem with
        | Nil => let (ans,_) := whole in ans
        | Cons ans _ => ans
      end
    | S m =>
      match rem with
        | Nil => mat' whole (let (_,rest) := whole in rest) m
        | Cons _ rest => mat' whole rest m
      end
  end.

Definition mat (A:Set) (whole:A * CoList A) (n:nat) : A :=
  mat' whole (let (hed,tyl) := whole in Cons hed tyl) n.
(*
Definition trunk (A:Set) (whole:A * CoList A)
  (x:((nat*nat*(nat*nat->option nat))+(A * CoList A * nat)))
    : nat+nat :=
    match x with 
      | inl (real,mod,f) =>
        match f (mymod real mod,myincr real mod) with
          | realNone => Conr 
            (mat whole real)
            (truncate whole od)
            (truncate whole ev)
          | Some bak => Ref _ bak
        end
      |inr (hed, _, _) =>
        Conr hed
        (truncate whole od)
        (truncate whole ev)
    end.
*)
CoFixpoint truncate (A:Set) (whole:A * CoList A)
  (x:Braun ((nat*nat*(nat*nat->option nat))+(A * CoList A * nat)))
    : BraunRef A :=
    match x with
      | Conb v od ev =>
        match v with 
          | inl (real,mod,f) =>
            match f (mymod real mod,myincr real mod) with
              | None => Conr 
                        (mat whole real)
                        (truncate whole od)
                        (truncate whole ev)
              | Some bak => Ref _ bak
            end
          |inr (hed, _, _) =>
            Conr hed
            (truncate whole od)
            (truncate whole ev)
        end
    end.

Check iterate.
Check fun A => iterate (@action A).
Definition cycle A hed tyl :=
       truncate (hed,tyl) (iterate (@action A) (inr _ (hed,tyl,0))).

Check cycle.

Definition bacc x y := ord x < ord y.

Hint Unfold bacc.

Lemma bwf : well_founded bacc.
Proof.
  apply well_founded_ltof.
Qed.

CoInductive coeq A : Braun A -> Braun A -> Prop :=
| co : forall x y od od' ev ev',
        (x = y) -> coeq od od' -> coeq ev ev'
        -> coeq (Conb x od ev) (Conb y od' ev').


Check bat.
Check find.

Definition cofull A (x:BraunRef A) (y:Braun A) :=
  exists xp,
    forall b,
      @find _ x xp b = bat y b.

CoFixpoint iterateSlow (A:Set) F (x:A) : Braun A :=
  let g := fun z => F (F z) in
    let y := F x in
      Conb x (iterateSlow g y)
             (iterateSlow g (F y)).

Variable iterSlow : forall (A:Set) b f (x:A), bat (iterateSlow f x) b = applyn (ord b) f x.

Definition beq (A:Set) (x:Braun (nat * nat * (nat * nat -> option nat) + A * CoList A * nat)) y :=
  forall b, 
    match (bat x b, bat y b) with
      | (inl (x,y,f), inl (p,q,g)) => 
        and (x=p) (and (y=q) (forall z, f z = g z))
      | (inr (x,xs,v),inr (y,ys,w)) =>
        and (x=y) (and (cleq xs ys) (v=w))
      | _ => False
    end.
    
Definition weq (A:Set) (x:A * CoList A) y :=
  match (x,y) with
    | ((p,ps),(q,qs)) =>
      and (p = q) (cleq ps qs)
  end.
  
CoInductive rcoeq A : BraunRef A -> BraunRef A -> Prop :=
| cor : forall x y, x = y -> rcoeq (Ref _ x) (Ref _ y)
| coc : forall x y od od' ev ev',
        (x = y) -> rcoeq od od' -> rcoeq ev ev'
        -> rcoeq (Conr x od ev) (Conr y od' ev').

(*

Add Parametric Morphism A : (@truncate A) with
  signature (@weq A) ==> 
  (@beq A) ==> 
  (@rcoeq A) as trunmor.
Proof.
  clear; intros.
  unfold weq in *; unfold beq in *.
  destruct x; destruct y.
  destruct H.
  cofix.
  remember (truncate (a,c) x0) as d;
    remember (truncate (a0,c0) y0) as e;
      destruct d; destruct e.
  apply coc.
  Check frobeq.
  rewrite frobeq in Heqd;
    rewrite frobeq in Heqe.
  destruct x0; destruct y0; simpl in *. 
  destruct s; destruct s0; simpl in *.
  destruct p; destruct p0; simpl in *.
  destruct p; destruct p0; simpl in *.
  remember (o (mymod n n0, myincr n n0)) as oo;
    remember (o0 (mymod n1 n2, myincr n1 n2)) as zz;
      destruct oo; destruct zz; simpl in *;
        inversion Heqd; inversion Heqe.
  subst; simpl in *.
  clear Heqd Heqe.
  Print mat.
  Print mat'.
  f_equal.
  f_equal.
    rew

unfold truncate in *; simpl.


  intros ? ? ? b; 
    generalize dependent x;
      generalize dependent y;
        induction b; intros ? ? xy;
          destruct x; destruct y; 
            inversion xy; subst.

  reflexivity.

  destruct a; apply IHb; assumption.
Qed.
*)

Lemma cycleTrue :
  forall (A:Set) (x:A) xs, 
    WellBraun (cycle x xs).
Proof.
  unfold WellBraun.
  intros.
  remember (upto (cycle x xs) b) as ucb.
  destruct ucb. destruct p.
  unfold cycle in *.
  
Admitted.

Check head.
Check Stream.
Print Stream.

Definition shead (A:Set) (x:Stream A) :=
  match x with
    | More y _ => y
  end.

Definition stail (A:Set) (x:Stream A) :=
  match x with
    | More _ ys => ys
  end.


CoFixpoint fmap A B F (x:Braun A) : Braun B :=
match x with
  | Conb h od ev => Conb (F h) (fmap _ F od) (fmap _ F ev) 
end.


Check fmap.

Check (fun (A:Set) (xs:Stream A) => fmap (@shead _) (iterate (@stail A) xs)).

Definition fromStream (A:Set) (xs:Stream A) :=
  fmap (@shead _) (iterate (@stail A) xs).

Check streamCycle.
Check cycle.


Lemma cycleAccurate :
  forall (A:Set) (x:A) xs,
    cofull 
      (cycle x xs)
      (fromStream (streamCycle x xs)).
Proof.
Admitted.

Check FiniteCoList.
Check FiniteBraun.
Check max.
Print max_type.

Print nat_compare.


Definition larger n m :=
  match nat_compare n m with
    | Gt => n
    | _ => m
  end.

Lemma cycleSmall :
  forall (A:Set) (xs:CoList A) n, 
    FiniteCoList xs n ->
    exists m, m <= 2*(larger (n*(n-1)) (2*n-1))+1.
Proof.
Admitted.





         ()


  destruct l.
  unfold upto in *.
  destruct b0. auto.
  unfold cycle in *.
  Check coeq.
  
  unfold upto' in *.

  unfold cycle in *.
  


  generalize dependent A.
  assert (let P b := forall (A : Set) (x : A) (xs : CoList A),
   let (res, ht) := upto (cycle x xs) b in
   let (hed, _) := ht in
   match res with
   | Conr _ _ _ => True
   | Ref v => v < ord hed
   end in forall b, P b).
  apply (well_founded_ind bwf).
  intros.
  unfold bacc in H.
  remember (upto (cycle x0 xs) x) as xxx.
  destruct xxx.
  destruct p.
  destruct b0.
  auto.
  induction x.
  simpl in *.
  unfold cycle in Heqxxx.
  unfold upto in Heqxxx.
  Check upto'.
  unfold upto' in Heqxxx.
  inversion Heqxxx.
  subst.
  Check frob.
  Check frobeq.
  rewrite (@frobeq A) in H1.
  simpl in H1.
  Check frobb.
  Check action.
  Check frobbeq.
  remember ((iterate (@action _)
             (inr (nat * nat * (nat * nat -> option nat)) (x0, xs, 0)))) as iax.
  destruct iax.
  destruct s.
  destruct p.
  destruct p.
  remember (o (mymod n0 n1, myincr n0 n1)) as ann.
  destruct ann.
  inversion H1. subst. clear H1.

  rewrite (@frobbeq (nat * nat * (nat * nat -> option nat) + A * CoList A * nat) (iterate (@action _)
             (inr (nat * nat * (nat * nat -> option nat)) (x0, xs, 0)))) in H1.
  simpl in H1.
  Check truncate.
  inversion Heqxxx.
  
  rewrite frob
  unfold truncate in Heqxxx.
  simpl in Heqxxx.














  induction x.
  simpl.
  remember (iterate (@action A)
      (inr (nat * nat * (nat * nat -> option nat)) (x0, xs, 0))) as y.
  destruct y.
  simpl in Heqy.
(*
  Check frobbeq.
  rewrite frobbeq in Heqy.
*)  simpl in Heqy.
  Check s.
  assert (s = inr _ (x0,xs,0)).
  Check bat.
  transitivity (bat (Conb s y1 y1) nil).
  simpl. reflexivity.
  transitivity (bat (iterate (@action A)
      (inr (nat * nat * (nat * nat -> option nat)) (x0, xs, 0))) nil).
  rewrite <- Heqy. reflexivity.
  rewrite <- iterp.
  simpl. reflexivity.
  subst.
  auto.
  destruct a.
  destruct xs.
  simpl.
  remember (iterate (@action A)
      (inr (nat * nat * (nat * nat -> option nat)) (x0, Nil A, 0))) as y.
  destruct y.
  assert (s = inr _ (x0,Nil A,0)).
  Check bat.
  transitivity (bat (Conb s y1 y1) nil).
  simpl. reflexivity.
  transitivity (bat (iterate (@action A)
      (inr (nat * nat * (nat * nat -> option nat)) (x0, Nil A, 0))) nil).
  rewrite <- Heqy. reflexivity.
  rewrite <- iterp.
  simpl. reflexivity.
  subst.
  



  unfold cycle.
  simpl.
  simpl.
  simpl.
  apply H.
  apply IHx.
  simpl.



  inversion Heqy.

  unfold truncate in Heqy.
  rewrite (frobbeq 
    (iterate (@action A)
      (inr (nat * nat * (nat * nat -> option nat)) (x, xs, 0)))) in Heqy.
  
  simpl in Heqy.
  Check frobb.
  Check truncate.
  unfold truncate in Heqy.
  unfold iterate in Heqy.
  
  generalize dependent xs.
  
  induction xs.
  induction H.
  simpl.
  unfold concrete.
  simpl.
  


Lemma cycleTrue :
  forall (A:Set) (x:A) xs, 
    WellBraun (cycle x xs).
Proof.
  intros.
  unfold WellBraun.
  intros.
  remember (cycle x xs) as y.
  generalize dependent x.
  generalize dependent xs.
  induction H; intros xs x Heqy.
  Print cycle.
  Print truncate.
  unfold cycle in Heqy.
  Check cycle.
  remember (iterate (@action A)
      (inr (nat * nat * (nat * nat -> option nat)) (x, xs, 0))) as y.
  destruct y.
  simpl in Heqy.
  rewrite frobeq in Heqy.
  simpl in Heqy.
  Check s.
  assert (s = inr _ (x,xs,0)).
  Check bat.
  transitivity (bat (Conb s y1 y1) nil).
  simpl. reflexivity.
  transitivity (bat (iterate (@action A)
      (inr (nat * nat * (nat * nat -> option nat)) (x, xs, 0))) nil).
  rewrite <- Heqy0. reflexivity.
  rewrite <- iterp.
  simpl. reflexivity.
  subst.
  inversion Heqy.

  unfold truncate in Heqy.
  rewrite (frobbeq 
    (iterate (@action A)
      (inr (nat * nat * (nat * nat -> option nat)) (x, xs, 0)))) in Heqy.
  
  simpl in Heqy.
  Check frobb.
  Check truncate.
  unfold truncate in Heqy.
  unfold iterate in Heqy.
  
  generalize dependent xs.
  
  induction xs.
  induction H.
  simpl.
  unfold concrete.
  simpl.
                        

(*
Definition action 
  (A:Set) 
  (x:(nat*nat*nat*nat*(nat*nat->option nat))+(CoList A* nat))
  : (nat*nat*nat*nat*(nat*nat->option nat))+(CoList A* nat) :=
  match x with
    | inl (real,place,incr,mod,f) => 
      inl _ (real+1,
        mymod (place+1) mod,
        if is2pow (place+2) then mymod (incr*2) mod else incr,
          mod,
          match f (place,incr) with
            | Some v => f
            | None => fun pi =>
              match pi with
                | (p,i) => 
                  match (nat_compare p place,
                        nat_compare i incr) with
                    | (Eq,Eq) => Some real
                    | _ =>  f pi
                  end
              end
          end)
    | inr (rem,sofar) =>
      match rem with
        | Nil => inl _ (sofar,0,incrof sofar,sofar,memo sofar)
        | Cons _ tl => inr _ (tl,sofar+1)
      end
  end.
*)
(*
Scheme fbis := Minimality for FiniteBraun Sort Prop.

Check FiniteBraun_ind.
Check fbis.
*)
(*
Scheme Equality for FiniteBraun.

Scheme Equality for list.
Scheme Equality for BraunRef.
*)
Derive Inversion bri with (forall n, BraunRef n) Sort Prop.
Check bri.


Fixpoint concrete n (b:BraunRef n) (l:list bool) : Prop :=
  match b with
    | Conr _ o e =>
      match l with
        | nil => True
        | true::tl => concrete o tl
        | false::tl => concrete e tl
      end
    | _ => False
  end.

Definition WellBraun (b:BraunRef 0) := forall l,
  FiniteBraun b l -> fold_left and (map (concrete b) l) True.
  
CoFixpoint Repeat v n : BraunRef n := 
 Conr v (Repeat v _) (Repeat v _).

Derive Inversion fbi with (forall v n l, @FiniteBraun n (Repeat v n) l) Sort Set.
Check fbi.

Definition RepeatSmall v : BraunRef 0 := 
  Conr v (Ref _ nil) (Ref _ nil).

Lemma rpeatSmall : 
  forall v, WellBraun (RepeatSmall v).
Proof.
  unfold WellBraun.
  intros.
  dependent induction H.
  clear IHFiniteBraun2. 
  clear IHFiniteBraun1.
  dependent induction H.
  dependent induction H0.
  simpl. auto.
Qed.

Definition frob n (x:BraunRef n) : BraunRef n :=
  match x with
    | Conr h o e => Conr h o e
    | Ref b => Ref _ b
  end.

Lemma frobeq : forall n (x:BraunRef n), x = frob x.
Proof.
  destruct x; simpl; reflexivity.
Qed.
    
(*
Lemma rpeat : 
  forall v, WellBraun (Repeat v 0).
Proof.
  unfold WellBraun.
  intros v.
  assert (forall n, 
    (forall l, FiniteBraun (Repeat v (S n)) l -> False) ->
    (forall l, FiniteBraun (Repeat v n) l -> False)).
  intros.
  dependent destruction H0.
  rewrite (frobeq (Repeat v n)) in H0.
  simpl in H0.
  inversion H0.
  rewrite (frobeq (Repeat v n)) in H0.
  simpl in H0.
  inversion H0; subst.
  clear H0.
  auto.
  apply H in H0_. auto.
  assert (forall n, 
    (forall l, FiniteBraun (Repeat v n) l -> False) ->
    (forall l, FiniteBraun (Repeat v (S n)) l -> False)).
  intros.
  assert (FiniteBraun (Repeat v n) (l++l)).
  rewrite (frobeq (Repeat v n)).
  simpl.
  apply FiniteSum; auto.
  eapply H0. apply H2.
  
  assert (forall m b l, @FiniteBraun m b l -> l <> nil).
  clear.
  intros.
  induction H.
  discriminate.
  destruct l. elim IHFiniteBraun1. auto.
  discriminate.

  assert (forall l n, FiniteBraun (Repeat v n) l -> False).
  intros l.
  remember (length l) as ll.
  Check well_founded_ind.
  Check lt_wf_ind.
  generalize dependent Heqll.
  apply (lt_wf_ind ll (fun rr => (rr = length l -> forall n, FiniteBraun (Repeat v n) l -> False))).
  intros.
  eapply H2.
  eapply (well_founded_ind.
  dependent induction ll.
  intros.
  destruct l.
  apply H1 in H2. elim H2. auto.
  

  dependent destruction H1.
  inversion H2
  in
  induction n; intros.
  dependent destruction H1.
  rewrite (frobeq (Repeat v 0)) in H1.
  simpl in H1.
  inversion H1.
  rewrite (frobeq (Repeat v 0)) in H1.
  simpl in H1.
  inversion H1. subst. clear H1.


 Focus 2.
  assert (FiniteBraun (Repeat v (S n) l)
  
  rewrite (frobeq (Repeat v n)) in H.
  simpl in H.
  dependent inversion H.




  intros.
  dependent destruction H.
  assert (Ref n b = Repeat v n -> False).
  rewrite (frobeq (Repeat v n)).
  simpl.
  intros.
  auto.
  inversion H0. auto.
  rewrite (frobeq (Repeat v n)) in H1.
  simpl in H1.
  inversion H1. subst.
  clear H1.
  clear.
  simpl.
  intros.
  inversion H.
  induction (Repeat v n).
  unfold Repeat.
  simpl.
  cofix.
  unfold Repeat.
  injection.
  injection.
  case H.
  elim H.
  dependent destruction H.
  inversion H.
  inversion H using fbi; intros.
  clear H0; subst.
  intros n l.
  remember (FiniteBraun (Repeat v n) l) as H.
  dependent inversion H with fbi.
  remember (Repeat v n) as rvn.
  generalize dependent (Repeat v n).
  remember l as l'.
  generalize dependent l.
  induction H; intros. subst.
  dependent induction H.
  inversion H. subst.
  inversion H2.
  Print existT.

 discriminate H2.
  induction n.
  unfold WellBraun.
  intros.
  inversion H.

  indc
  intros.
  unfold not.

  Check H.
dependent inversion H.

  intros.
  inversion H.
  subst.
  Print existT.
  remember (existT (fun x : nat => BraunRef x) n (Ref n b)) as ll.
  remember (existT (fun x : nat => BraunRef x) n (Repeat v n)) as rr.
  inversion ll.
  elim H2.
  discriminate H2.

  elim H.
  induction H.



  simpl.
  unfold WellBraun.
  intros.
  dependent induction H.
  induction b.
  simpl. auto.
  simpl. auto.

  unfold Repeat in H.
  destruct H.
  elim H.

  discriminate H.
  inversion H.
  clear IHFiniteBraun2. 
  clear IHFiniteBraun1.
  dependent induction H.
  dependent induction H0.
  simpl. auto.
Qed.

  remember (RepeatSmall v) as rsv.
  generalize dependent (RepeatSmall v).
  intros b.
  induction H.
  
  induction H.
  induction l.
  destruct H.
  inversion H. subst.
  induction H.
  

  dependent induction H.
  

  generalize dependent l.


  inversion H.
  subst.
  inversion H1.
  inversion H4.
  intros v l.
  
  induction H.
  
  destruct H.
  simpl.
  split.
  eapply FiniteSum.
*)
CoInductive BraunRef (depth:nat) : Set :=
| Conr : A -> BraunRef (S depth) -> BraunRef (S depth) -> BraunRef depth
| Ref : forall up, up<depth -> list bool -> BraunRef depth.

Inductive FiniteBraun : forall n, BraunRef n -> nat -> Prop :=
| FiniteRef : forall n u p b, FiniteBraun (@Ref n u p b) 1
| FiniteSum : forall n h o e l r, 
  FiniteBraun o l ->
  FiniteBraun e r ->
  FiniteBraun (@Conr n h o e) (l+r).

Fixpoint RealRef3 n (b:BraunRef n) (l:list bool) : bool :=
  match l with
    | nil => match b with
               | Conr _ _ _ => true
               | _ => false
                 end
    | true::tl => match b with
                    | Conr _ o _ => RealRef3 o tl
                    | _ => false
                  end
    | false::tl => match b with
                    | Conr _ _ e => RealRef3 e tl
                    | _ => false
                  end
  end.

Program Fixpoint RealRef2 n (b:BraunRef n) (l:list bool) v (p:v<n) (r:list bool) : bool :=
  match v with
    | 0 => match l with
             | nil => false
             | hd :: tl => RealRef3 b ((rev (negb hd :: tl))++r)
           end
    | S m => match l with
               | nil => false
               | hd :: tl => @RealRef2 n b tl m _ r
             end
  end.
Next Obligation.
  auto with arith.
Defined.

Definition RealRef1 n (b:BraunRef n) (l:list bool) v (p:v<n) (r:list bool) : bool := RealRef2 b (rev l) p r.



Inductive SafeBraunAt (b:BraunRef 0) (l:list bool) : Prop :=
| Nil : forall h o e, SafeBraunAt (Conr h o e) nil
| Odd : forall h o e, SafeBraunAt (Conr h o e) 

CoInductive Braun : Set :=
| Conb : A -> Braun -> Braun -> Braun.

CoInductive coeq : Braun -> Braun -> Prop :=
| co : forall x y od od' ev ev',
        (x = y) -> coeq od od' -> coeq ev ev'
        -> coeq (Conb x od ev) (Conb y od' ev').

Locate "{ _ | _ }".
(*
Program Fixpoint mymod' (i:nat) (n:nat) (m:{k | k < S n}) {struct i} : 
  {j | j < S n} :=
  match i with
    | 0 => m
    | S l => match m with
               | 0 => mymod' l n
               | S p => mymod' l p
             end
    end.
Next Obligation.
  omega.
Defined.

Program Fixpoint mymod (i:nat) (n:nat) {struct i} : {j | j < S n} :=
  match i with
    | 0 => 0
    | S j => mymod' j n
  end.
Next Obligation.
  auto with arith.
Defined.
*)

Variable mymod : nat -> forall n, {j | j < S n}.

(*
Program Definition mymod (i:nat) (n:nat) : {j | j < S n} :=
  match eucl_dev (S n) _ i with
    | divex _ r p _ => r
  end.
Next Obligation.
  auto with arith.
Defined.


Program CoFixpoint cyc 
  (n:nat) 
  (f: {i | i < S n} -> A) 
  (start : {j | j < S n})
  (itvl:nat) : Braun :=
  Conb 
  (f start)
  (cyc f (mymod (start+  itvl) n) (2*itvl))
  (cyc f (mymod (start+2*itvl) n) (2*itvl)).

Print cyc.
*)
Program CoFixpoint cyc 
  (n:nat) 
  (f: {i | i < S n} -> A) 
  (start : nat)
  (itvl:nat) : Braun :=
  Conb 
  (f (mymod start n))
  (cyc f (mymod (start+  itvl) n) (2*itvl))
  (cyc f (mymod (start+2*itvl) n) (2*itvl)).

Print cyc.

Fixpoint bat (x:Braun) (b:list bool) {struct b} : A :=
  match x with
    | Conb h o e =>
      match b with
        | nil => h
        | true  :: r => bat o r
        | false :: r => bat e r
      end
  end.


Fixpoint ord (x:list bool) : nat :=
  match x with
    | nil => 0
    | true::r  => 1 + 2*(ord r)
    | false::r => 2 + 2*(ord r)
  end.

Hint Unfold ord.
(*
Lemma modNo : forall n (i : {j : nat | j < S n}),
  proj1_sig i = proj1_sig (mymod (proj1_sig i) n).
Proof.
  clear A.
  intros; destruct i; simpl.
  generalize dependent n.
  induction x; simpl; intros; auto.
  induction n; simpl.
  inversion l. inversion H0.
  simpl in *.
  
  unfold mymod'.
  simpl.
  simpl in *.
  auto.
  simpl in *.
  


  induction n.
  remember (mymod 0 0) as m; clear Heqm; destruct m.
  simpl. omega.
  unfold mymod.
  fold (mymod 0 n).
  simpl.


  remember (mymod 0 n) as m; destruct m.
  simpl in *.




  induction n.
  remember (mymod 0 0) as m; clear Heqm; destruct m.
  simpl. omega.
  apply IHn.

induction n; simpl; intros;
  destruct i; simpl in *.
  remember (mymod x 0) as m; clear Heqm; destruct m; simpl.
  omega.
  


  intros. destruct i. 
  generalize dependent n.
  induction x; simpl; intros.
  induction n.
  remember (mymod 0 0) as m; clear Heqm; destruct m.
  simpl. omega.
  apply IHn.
  


  induction n.
  inversion l; subst.
  simpl.
  remember (mymod 0 0) as m. clear Heqm.
  destruct m. simpl. inversion l0. auto. inversion H0.

  inversion H0.
  simpl in *.
  



  simpl in IHn.
  assert ({x < S n} + {x = S n}).
  clear IHn A.
  generalize dependent n.
  induction x; intros.
  left. auto with arith.
  induction n.
  right. inversion l. auto. subst. inversion H0. inversion H1.
  simpl in *.
  assert ({x < S n}  + {x = S n}).
  apply IHx.
  auto with arith.
  case H; intros.
  left. auto with arith.
  right. auto with arith.
  case H; intros.
  rewrite IHn at 1.


  auto with arith.
  remember (mymod x (S n)) as m.
  destruct m.
  simpl in *.
  elim l.

  induction n; induction i.

  inversion p. subst.
  simpl.
  remember (mymod 0 0) as m. clear Heqm.
  destruct m. simpl. inversion l. auto.
  inversion H0.
  inversion H0.

  simpl.
  remember (mymod x (S n)) as m.
  destruct m. simpl.

  induction x; induction x0; auto with arith.
  erewrite IHx0.
  

  Unfocus.

  erewrite (@IHn.
  induction m.
  induciton m.
  unfold mymod. simpl.
  unfold mymod_obligation_1. simpl.
  unfold mymod_obligation_2. simpl.
  unfold proj1_sig. simpl.
  unfold mymod_obligation_1.
  simpl. f_equal.
  simpl.

  intros. generalize dependent n.

*)
(*
Lemma propInSet : 
  forall (X : Prop) (Y : Set)
    (f : X -> Y) (a b : X), f a = f b.
Proof.
  clear.
  intros.
  intuition.
  firstorder.
  auto.
*)

Variable modAdd : forall x y n,
  proj1_sig (mymod (proj1_sig (mymod x n) + y) n) =
  proj1_sig (mymod (x+y) n).

Print proj1_sig.
Print sig.
Check exist.

Lemma cycis :
  forall b n f i j,
    (forall p q, proj1_sig p = proj1_sig q -> f p = f q) ->
    bat (cyc f i j) b =
    f (mymod (i + j * (ord b)) n).
Proof.
  induction b; intros.
  simpl. f_equal. f_equal. omega.

  destruct a; simpl; rewrite IHb;
    apply H; rewrite modAdd;
      (*generalize (ord b); clear; intro;*)
      rewrite mult_comm; symmetry; rewrite mult_comm;
        unfold mult;
          fold (mult (n + (n + 0)) j);
          fold (mult n (j + (j + 0)));
            repeat (rewrite mult_plus_distr_r);
            repeat (rewrite mult_plus_distr_l);
              f_equal; f_equal; omega.
Qed.

End type.

Check cycis.

omega.
  simpl. 

Locate "_ * _".
Print mult.





  omega. simpl.

  remember (ord b) as c. 

  

  Focus 2.
  simpl. rewrite IHb. f_equal.

  Unfocus.
  transitivity (mymod (proj1_sig i) n); try (f_equal; omega)

  destruct i.
  induction x.
  simpl.
  induction i.
  unfold proj1_sig.
  unfold mymod. simpl.



  intros

  omega.
  auto.

  auto with arith.
  omega.
  unfold modulo.
  simpl.


CoFixpoint fmap F (x:Braun) : Braun :=
match x with
  | Conb h od ev => Conb (F h) (fmap F od) (fmap F ev) 
end.

CoFixpoint oddFromEven F (x:A) (b:Braun) : Braun :=
match b with
  | Conb h od ev => Conb x (oddFromEven F (F h) ev) (fmap F od)
end.

Variable od : (A->A) -> A -> Braun.

Definition ev F (x:A) :=
  fmap F (od F x).

Variable odeq : forall F (x:A), 
  coeq (od F x) (oddFromEven F (F x) (ev F x)).



Definition iterate F (x:A) : Braun :=
  Conb x (od F x) (ev F x).

Lemma batcoeq : forall x y,
  (forall b, bat x b = bat y b) -> coeq x y.
Proof.
  cofix; intros.
  destruct x; destruct y; constructor.
  apply (H nil).
  apply batcoeq. intros. apply (H (true::b)).
  apply batcoeq. intros. apply (H (false::b)).
Qed.


Add Parametric Morphism : bat with
  signature coeq ==> (@eq (list bool)) ==> (@eq A) as batmor.
Proof.
  intros ? ? ? b; 
    generalize dependent x;
      generalize dependent y;
        induction b; intros ? ? xy;
          destruct x; destruct y; 
            inversion xy; subst.

  reflexivity.

  destruct a; apply IHb; assumption.
Qed.

Check batmor_Morphism.

Hint Rewrite odeq using batmor_Morphism : core.

Fixpoint applyn (n:nat) (f:A->A) (x:A) : A :=
  match n with
    | 0 => x
    | S m => f (applyn m f x)
  end.
(*
Fixpoint applyn' (n:nat) (f:A->A) (x:A) : A :=
  match n with
    | 0 => x
    | S m => applyn' m f (f x)
  end.
*)

Hint Unfold applyn.

Definition odds (x:Braun) :=
  match x with
    | Conb _ od _ => od
  end.

Definition evens (x:Braun) :=
  match x with
    | Conb _ _ ev => ev
  end.

Add Parametric Morphism : odds with
  signature 
  coeq ==> coeq as oddsMor.
Proof.
  intros.
  destruct x; destruct y.
  simpl.
  inversion H. assumption.
Qed.

Add Parametric Morphism : evens with
  signature 
  coeq ==> coeq as evensMor.
Proof.
  intros.
  destruct x; destruct y.
  simpl.
  inversion H. assumption.
Qed.

Definition bacc x y := ord x < ord y.

Hint Unfold bacc.

Lemma bwf : well_founded bacc.
Proof.
  apply well_founded_ltof.
Qed.

Fixpoint pow x y :=
  match y with
    | 0 => 1
    | (S n) => x * (pow x n)
  end.

Lemma subHelp :
  forall x y, S x >= S y -> x >= y.
Proof.
  intros; omega.
Qed.


Function sub (x:nat) (y:nat)  {struct x} : (x >= y) -> nat :=
  match x return (x >= y) -> nat with
    | S n => 
      match y return (S n >= y) -> nat with
        | 0 => fun _ => x
        | S m => fun (p:S n >= S m) => @sub n m (subHelp p)
      end
    | 0 => fun _ => 0
  end.

Lemma subeq : forall p q p' q' r s, 
  p = p' -> q = q' -> @sub p q r = @sub p' q' s.
Proof.
  double induction p q; intros; subst; auto.
  unfold sub.
  fold (sub (subHelp r)).
  fold (sub (subHelp s)).
  auto.
Defined.

Print sub.

(*
Definition sub (x:nat) (y:nat) (p: x >= y) : nat.
refine (fix ss x y p :=
  match (x,y) as xy with
    | (S n,0) => S n
    | (S n,S m) => @ss n m (subHelp _)
    | (0,_) => 0
  end).



Program Fixpoint sub x y (p: x >= y) :=
  match (x,y) with
    | (S n,0) => S n
    | (S n,S m) => @sub n m _
    | (0,0) => 0
    | (0,S m) => _
  end.
Next Obligation.
  omega.
Qed.
*)

(*
Lemma eviter :
  forall f b it x,
    (forall n, bacc n b -> bat it n = applyn (ord n) f x) ->
      forall n, ord n <= ord b -> 
        bat (evens it) n = applyn (2*(ord n)+2) f x.
Proof.
  intros.
  destruct it. simpl.
  destruct 
*)



Definition half (x:list bool) :=
  match x with
    | nil => nil
    | _ :: y => y
  end.

Lemma dec1pow :
  forall k, pow 2 k >= 1.
Proof.
  induction k; simpl; omega.
Defined.
(*
Lemma dec2pow :
  forall k, pow 2 (S k) >= 2.
Proof.
  induction k; simpl.
  auto.
  simpl in IHk. omega.
Defined.
*)
Lemma dec2pow :
  forall k, pow 2 k + pow 2 k >= 2.
Proof.
  induction k; simpl.
  auto. omega.
Defined.

Lemma applyAdd :
  forall f n m x,
    applyn n f (applyn m f x) =
    applyn (n+m) f x.
Proof.
  intros f n; 
    generalize dependent f;
      induction n; intros.
  auto.
  simpl. f_equal. apply IHn.
Qed.

Hint Rewrite applyAdd : arith.

Hint Resolve applyAdd.

Lemma applyMul :
  forall f n m x,
    applyn n (applyn m f) x =
    applyn (n*m) f x.
Proof.
  intros f n; 
    generalize dependent f;
      induction n; intros.
  auto.
  simpl. rewrite IHn. apply applyAdd.
Qed.

Hint Rewrite applyMul : arith.
Hint Resolve applyMul.

Lemma subPlus : forall ab a b c c' p q, 
  ab = a+b -> c = c' -> 
  @sub ab c p = a + @sub b c' q.
Proof.
  clear.
  assert (forall a b c p q, 
    @sub (a+b) c p = a + @sub b c q).
  Focus 2. intros; subst; auto.
  induction a; induction b; induction c;
    simpl; intros; subst; auto using subeq.
  inversion q.
  rewrite plus_Snm_nSm in IHb. apply IHb.
Qed.

Hint Rewrite subPlus : arith.
Hint Resolve subPlus.

Lemma subZero : forall n p,
  @sub n 0 p = n.
Proof.
  clear.
  induction n; auto. 
Qed.

Hint Rewrite subZero : arith.
Hint Resolve subZero.

Lemma subOne : forall a b p q,
      S (@sub a (S b) p) = @sub a b q.
Proof.
  clear.
  double induction a b;
    simpl; intros; auto with arith.
Qed.

Hint Rewrite subOne : arith.
Hint Resolve subOne.

Lemma plusMinus : forall k,
  S (sub (dec1pow k)) = pow 2 k.
Proof.
  clear; intros.
  assert (pow 2 k >= 0).
  induction k; omega.
  rewrite (subOne _ H).
  auto.
Qed.

Lemma subPow1 : forall k, 
  sub (dec1pow (S k)) = pow 2 k + sub (dec1pow k).
Proof.
  clear.
  intros k.
  erewrite subPlus.
  reflexivity.
  unfold pow at 1. fold (pow 2 k). omega.
  reflexivity.
Qed.

Hint Rewrite subPow1 : arith.
Hint Resolve subPow1.

Lemma subPow2 : forall k, 
  sub (dec2pow (S k)) = pow 2 (S k) + sub (dec2pow k).
Proof.
  clear.
  intros k.
  erewrite subPlus.
  reflexivity.
  unfold pow. fold (pow 2 k). omega.
  reflexivity.
Qed.

Hint Rewrite subPow2 : arith.
Hint Resolve subPow2.

Lemma subPow2S : forall k, 
  S(sub (dec2pow k)) = sub (dec1pow (S k)).
Proof.
  clear.
  induction k.
  auto.
  rewrite subPow2.
  rewrite subPow1.
  rewrite <- IHk.
  auto with arith.
Defined.

Hint Rewrite subPow2S : arith.
Hint Resolve subPow2S.

Lemma subPow2Div : forall k, 
  sub (dec2pow k) = sub (dec1pow k) + sub (dec1pow k).
Proof.
  clear.
  induction k; auto.
  rewrite subPow1.
  rewrite subPow2.
  unfold pow; fold (pow 2 k). 
  rewrite IHk. omega.
Defined.

Hint Rewrite subPow2Div : arith.
Hint Resolve subPow2Div.

Lemma fmapbat : forall f b x,
  bat (fmap f x) b = f (bat x b).
Proof.
  clear; induction b; destruct x; auto.
  destruct a; simpl; auto.
Qed.

Hint Rewrite fmapbat : core.
Hint Resolve fmapbat.

Lemma mainLemma :
  forall b e x f k,
    (forall j, ord j < ord b ->
      bat e j = 
      applyn (ord j)
      (applyn (pow 2 k) f) 
      (applyn (sub (*(pow 2 (k+1)) 2*) (dec2pow k)) f x)) ->
    bat (oddFromEven f 
      (applyn (sub (*(pow 2 k) 1*) (dec1pow k)) f x) e) b =
    applyn (ord b)
    (applyn (pow 2 k) f) 
    (applyn (sub (*(pow 2 k) 1*) (dec1pow k)) f x).
Proof.
  induction b; destruct e as [hd odd even]; intros.

  reflexivity.

  destruct a; simpl.
  transitivity
    (bat (oddFromEven f (applyn (sub (dec1pow (S k))) f x) even) b); auto.
  transitivity 
    (bat (oddFromEven f (applyn (S (sub (dec2pow k))) f x) even) b); auto.
  repeat (repeat f_equal; unfold applyn).
  transitivity (bat (Conb hd odd even) nil); auto.
  apply H. 
  unfold ord; auto with arith.
  repeat (f_equal); auto with arith.

  rewrite IHb.

  autorewrite with arith.
  f_equal.
  unfold pow; fold (pow 2 k).
  simpl.
  repeat (rewrite mult_plus_distr_r).
  repeat (rewrite mult_plus_distr_l).
  omega.  

  intros.
  transitivity (bat (Conb hd odd even) (false::j)); auto.
  rewrite H.
  autorewrite with arith.
  f_equal.
  unfold ord; fold (ord j).
  unfold pow; fold (pow 2 k).
  simpl. 
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite mult_plus_distr_r).
  simpl. omega.
  
  unfold ord; fold (ord j); fold (ord b).
  omega.

  rewrite fmapbat.

  transitivity (applyn 1 f (bat (Conb hd odd even) (true::b))); auto.

  rewrite H.
  clear.
  autorewrite with arith.
  f_equal.
  
  unfold ord; fold (ord b).
  
  assert (S (sub (dec1pow k)) = pow 2 k). auto using plusMinus.
  remember (sub (dec1pow k)) as km.
  destruct km; simpl; omega.

  clear; unfold ord; omega.
Qed.

Check mainLemma.

Lemma iter :
  let P b := forall f x, bat (iterate f x) b = applyn (ord b) f x
    in forall b, P b.
Proof.
  intro P.
  eapply (well_founded_ind bwf).
  intros b IH.
  unfold P.
  intros.
  destruct b as [|a b]; auto.

  assert 
    (bat (oddFromEven f (f x) (ev f x)) b =
      f (applyn (ord b + (ord b + 0)) f x)) as help.

  replace (f x) with (applyn (sub (dec1pow 1)) f x); auto.
  rewrite mainLemma.
  transitivity (applyn 1 f (applyn (ord b + (ord b + 0)) f x)); auto.
  repeat (repeat (rewrite applyMul); repeat (rewrite applyAdd)).  
  f_equal. simpl; omega.

  intros.
  transitivity
    (bat (iterate f x) (false::j)); auto.
  rewrite IH.
  repeat (rewrite applyMul); repeat (rewrite applyAdd).
  f_equal.
  unfold ord; fold (ord j). simpl; omega.

  unfold bacc; unfold ord; fold (ord b); fold (ord j). 
  destruct a; omega.

  destruct a; simpl.
  rewrite odeq; apply help.

  unfold ev.
  rewrite fmapbat.

  f_equal. rewrite odeq. apply help.
Qed.

Check odeq.

End type.

Fixpoint batod n F x b p :=
  bat (oddFromEven F (F x) (ev (batod (n-1)F x)) b.



Check iter.

Check batcoeq.

CoFixpoint frombat g :=
  Conb 
  (g nil) 
  (frombat (fun r => g (true::r)))
  (frombat (fun r => g (false::r))).

End type.

Check frombat.

Program Fixpoint fixodd (A:Set) b (f:A->A) (x:A) {measure ord b} : A :=
  bat (oddFromEven f (f x) 
    (ev (fun g y => frombat (fun c => fixodd c g y)) f x)) b.
Next Obligation.


End type.

Check fixodd.


Program Fixpoint fixodd f x b {measure ord b} : A :=
  bat (oddFromEven f (f x) (ev f x)) b.




  match b with
    | nil => f x
    |


CoInductive Mayb : Set :=
  | These : A -> option Mayb -> option Mayb -> Mayb.

Print option.

Fixpoint mat b x :=
  match x with
    | None => None
    | Some (These h o e) =>
      match b with
        | nil => Some h
        | true::r => mat r o
        | false::r => mat r e
      end
  end.

Definition isSome (t:Set) (x:option t) :=
  match x with
    | None => False
    | Some _ => True
  end.

Definition mall n :=
  { x | forall b, ord b < ord n -> 
        isSome (mat b x)}.

Locate "{ _ | _ }".
Print sig.

Fixpoint succ n :=
  match n with
    | nil => true :: nil
    | true ::r => false::r
    | false::r => true::(succ r)
  end.

Print succ.
Print isSome.
Print mat.

Notation "[ e ]" := (exist _ e _).

Check proj1_sig.
Check proj2_sig.
(*
Function mmap (f:A->A) (n:list bool) (x:mall n) {measure ord n} : mall n :=
  match x with
    | exist None _ => [None]
    | exist (Some (These h o e)) _ => 
      [Some (These (f h) (proj1_sig (@mmap f (half n) [o])) (proj1_sig (@mmap f _ [e])))]
  end.
*)

CoFixpoint mmap (f:A->A) (x:Mayb) : Mayb :=
  match x with
    | These h _ _ =>
      These (f h) None None
(*
    | These h None None =>
      These (f h) None None
    | These h None (Some e) =>
      These (f h) None (Some (mmap f e))
    | These h (Some o) None =>
      These (f h) (Some (mmap f o)) None
    | These h (Some o) (Some e) =>
      These (f h) (Some (mmap f o)) (Some (mmap f e))
*)
  end.

CoFixpoint moddFromEven f x v : Mayb :=
  match v with
    | These h None None =>
      These x None None
    | These h None (Some e) =>
      These x (Some (moddFromEven f (f h) e)) None
    | These h (Some o) None =>
      These x None (Some (mmap f o))
    | These h (Some o) (Some e) =>
      These x (Some (moddFromEven f (f h) e)) (Some (mmap f e))
  end.

CoFixpoint moddFromEven' f x v : Mayb :=
  These x 
  (match v with
     | These _ _ None =>
       None
     | These h _ (Some e) =>
       Some (moddFromEven f (f h) e)
   end)
  (match v with
     | These _ None _ =>
       None
     | These _ (Some o) _ =>
       Some (mmap f o)
   end).

Definition mhead x :=
  match x with
    | These h _ _ => h
  end.


CoFixpoint even f x : Mayb :=
      These (f (mhead (odd f x))) None None
(*
    | These h None None =>
      These (f h) None None
    | These h None (Some e) =>
      These (f h) None (Some (mmap f e))
    | These h (Some o) None =>
      These (f h) (Some (mmap f o)) None
    | These h (Some o) (Some e) =>
      These (f h) (Some (mmap f o)) (Some (mmap f e))
*)

(*  mmap f (odd f x)*)
with odd f x : Mayb :=
  These (f x)
  (match even f x with
     | These _ _ None =>
       None
     | These h _ (Some e) =>
       Some (moddFromEven f (f h) e)
   end)
  (match even f x with
     | These _ None _ =>
       None
     | These _ (Some o) _ =>
       Some (mmap f o)
   end).
(*  moddFromEven' f (f x) (even f x).*)

End type.

Check iter.

