(* 
This file proves the productivity of iterate in:

data Braun a = Braun a (Braun a) (Braun a)

instance Functor Braun where
  fmap f (Braun h o e) = Braun (f h) (fmap f o) (fmap f e)

oddFromEven f x (Braun h o e) =
  Braun x (oddFromEven f (f h) e) (fmap f o)

iterate f x =
  let od = oddFromEven f x ev
      ev = fmap f od
  in Braun x od ev

*)
Require Import List.
Require Import Setoid.
Require Import BraunStreams.

Set Implicit Arguments.
(*Set Contextual Implicit.*)
(*Unset Strict Implicit. *)
(*Set Reversible Pattern Implicit. *)

Section Single.

Variable (a : Set).
Variable (aeq : relation a).
Variable (aeqEquiv : Equivalence aeq).

Definition braun := braun a.
Definition coeq := coeq aeq.
Definition exteq := @exteq a aeq a aeq.
Definition opaque := @opaque a a aeq aeq.

Variable f : a -> a.
Variable fOpaque : opaque f.

Definition Braun' := list bool -> A.

(* Extensional function quality is an equivalence relation: *)

Section Double.

Variable (B:Set).
(*
Variable (Beq : relation B).
Variable (Beq_equiv : Equivalence Beq).
*)
Definition exteq (f:B -> A) (g:B -> A) := 
  forall x, aeq (f x) (g x).

Hint Unfold exteq.

Lemma exteq_refl : forall f, exteq f f.
Proof.
  auto using Equivalence_Reflexive.
Qed.

Lemma exteq_symm : forall f g, exteq f g -> exteq g f.
Proof.
  auto using Equivalence_Symmetric.
Qed.

Lemma exteq_trans : forall f g h, exteq f g -> exteq g h -> exteq f h.
Proof.
  eauto using Equivalence_Transitive.
Qed.

Add Parametric Relation : (B->A) exteq
reflexivity proved by exteq_refl
symmetry proved by exteq_symm
transitivity proved by exteq_trans
as exteq_equiv.

End Double.

Hint Unfold exteq.

(* unco converts the usual Braun streams to their functional dopplegangers, Braun' *)

Fixpoint unco (x : Braun) (n : list bool) {struct n} : A :=
match x with
| Cons h od ev =>
  match n with
    | nil => h
    | true ::r => unco od r
    | false::r => unco ev r
  end
end.

Require Import Coq.Program.Equality.

Ltac des :=
  intros; simpl in *;
  match goal with
    | [H:Equivalence ?S |- _] => inversion_clear H; des
    | [a:bool |- _] => destruct a; des
    | [xy : coeq ?x ?y |- _] => inversion_clear xy; auto
    | _ => auto
  end.

(* unco turns bisimilar Braun streams into extensionally equal Braun' functions *)

Add Parametric Morphism : unco with
  signature coeq ==> (@exteq (list bool)) as unco_mor.
Proof.
  assert (forall n x y, coeq x y -> aeq (unco x n) (unco y n)).
  induction n; des.
  auto.
Qed.

(* reco undoes the conversion, turning Braun' functions into Braun streams *)

CoFixpoint reco (x : Braun') : Braun :=
Cons (x nil) (reco (fun y => x (cons true y)))
             (reco (fun y => x (cons false y))).

(* A little trick from http://adam.chlipala.net/cpdt/
This function is useful for proofs.
 *)

Definition frob (x : Braun) : Braun :=
match x with
| Cons h od ev => Cons h od ev
end.

Lemma frobeq : forall (x:Braun), x = frob x.
Proof.
  destruct x. simpl. reflexivity.
Defined.

(* like unco, reco takes entensionally equivalent functions to bisimilar streams *)

Add Parametric Morphism : reco with
  signature (@exteq (list bool)) ==> coeq as reco_mor.
Proof.
  cofix.
  intros x y xy.
  rewrite (frobeq (reco x)).
  rewrite (frobeq (reco y)).
  simpl.
  constructor.
  unfold exteq in xy. auto.
  apply reco_mor_Morphism. unfold exteq. auto.
  apply reco_mor_Morphism. unfold exteq. auto.
Qed.

(* unco and reco are inverses: *)

Lemma unre : forall x y, exteq x y -> exteq (unco (reco x)) y.
Proof.
  assert (forall n x y, exteq x y -> aeq (unco (reco x) n) (y n)).
  induction n; des.
  apply IHn with (y := fun z => y (true::z)). des.
  apply IHn with (y := fun z => y (false::z)). des.
  auto.
Qed.

Lemma reun : forall x y, coeq x y -> coeq (reco (unco x)) y.
Proof.
  Lemma reun' : 
    forall x y, coeq x y -> coeq (reco (fun v => unco x v)) y.
  Proof.
    cofix.
    intros.
    rewrite (frobeq (reco (fun v => unco x v))).
    simpl.
    destruct y. simpl.
    destruct x. simpl. 
    inversion H. subst.
    constructor.

    assumption.
    apply reun'. assumption.
    apply reun'. assumption.
  Qed.
  Show.
  intros.
  rewrite reco_mor_Morphism.
  apply reun' with (x := x).
  assumption.
  unfold exteq. intros.
  apply Equivalence_Reflexive.
Qed.

Check reun'.

(* bOrd converts locations in Braun streams to natural numbers *)

Fixpoint bOrd (x : list bool) : nat :=
match x with
  | nil => 0
  | (true :: r) => 1 + 2 * (bOrd r)
  | (false :: r) => 2 + 2 * (bOrd r)
end.


(* The usual record selectors: *)

Definition headB (x : Braun) :=
match x with 
| Cons h _ _ => h
end.

Definition head' (x:Braun') := x nil.

Definition oddB (x : Braun) :=
match x with 
| Cons _ od _ => od
end.

Definition odd' (x : Braun') (n : list bool) := x (true :: n).

Definition evenB (x : Braun) :=
match x with 
| Cons _ _ ev => ev
end.

Definition even' (x : Braun') (n : list bool) := x (false :: n).

(* And fmap as in Haskell's Functor class *)

CoFixpoint fmapB (x:Braun) : Braun :=
match x with
| Cons h od ev => Cons (F h) (fmapB od) (fmapB ev)
end.

Definition fmap' (x : Braun') (n : list bool) : A :=
F (x n).

(*
Fixpoint oddFromEven (x : A) (v : Braun') (n : list bool) {struct n} : A :=
match n with
| nil => x
| true :: r => oddFromEven (F (head' v)) (even' v) r
| false :: r => fmap' (odd' v) r
end.
*)
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Recdef.

Require Import Coq.omega.Omega.

(* A Br n is a Braun stream that is only defined for indices less than n *)

Definition Br (n:list bool) := 
  forall (b:list bool), bOrd b < bOrd n -> A.

Require Import Arith.

(* succT n is one more than n *)

Fixpoint succT (n:list bool) : list bool :=
match n with
| nil => true :: nil
| true ::r => false::r
| false::r => true::(succT r)
end.


Lemma succTisS : forall n, bOrd (succT n) = S (bOrd n).
Proof.
  induction n; des. omega.
Defined.

Hint Rewrite succTisS : bord.

Ltac num :=
  des; autorewrite with bord in *; try omega; auto.

(* twiceT n is 2*n *)

Fixpoint twiceT (n:list bool) : list bool :=
match n with
| nil => nil
| true::r => false::(twiceT r)
| false::r => false::(succT (twiceT r))
end.

Lemma twice : forall n, bOrd (twiceT n) = 2*(bOrd n).
Proof.
  induction n; num.
Qed. 

Hint Rewrite twice : bord.

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

Definition ord := bOrd.

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

Definition predT (n:list bool) : list bool :=
  match n with 
    | nil => nil
    | true::r => twiceT r
    | false::r => true::r
  end.

Lemma succPred : 
  forall x, x <> nil -> succT (predT x) = x.
Proof.
  intros; destruct x.
  destruct H. auto.
  destruct b; simpl.
  rewrite <- (@unt (succT (twiceT x))).
  num. simpl.
  rewrite <- unt.
  simpl. auto. auto.
Qed.

Hint Rewrite succPred : bord.
  
(* using the selectors defined above, the type of odds is 
Br n -> Br (oddsT n)
and the type of evens if
Br n -> Br (evensT n)
*)

Definition oddsT (n:list bool) : list bool :=
match n with
| nil => nil
| true ::r => r
| false::r => succT r
end.

Definition evensT (n:list bool) : list bool :=
match n with
| nil => nil
| p::q => q
end.

(*
CoInductive Be : list bool -> Set :=
| Bnil : Be nil
| Bcons : forall b r, A -> Be (oddsT (b::r)) -> Be r -> Be (b::r).

CoInductive CoNat : Set :=
| Z : CoNat
| S : CoNat -> CoNat.

Definition naeq (x:CoNat) : CoNat :=
match x with
  | Z => Z
  | S n => S n
end.

Lemma nana : forall x, x = naeq x.
Proof.
  destruct x; reflexivity.
Qed.

CoFixpoint CoOdds (n:CoNat) : CoNat :=
match n with
  | Z => Z
  | S Z => Z
  | S (S m) => S (CoOdds m)
end.

Definition CoEvens (n:CoNat) : CoNat :=
match n with
  | Z => Z
  | S m => CoOdds m(*
  | S (S Z) => Z
  | S (S (S m)) => S (CoEvens (S m))*)
end.

CoInductive CoBr : CoNat -> Set :=
  | CoBrCons : 
    forall n, 
      A -> 
      CoBr (CoOdds (S n)) -> 
      CoBr (CoEvens (S n)) ->
      CoBr (S n).

CoFixpoint fmapC (n:CoNat) (x:CoBr n) : CoBr n :=
match x with
| CoBrCons _ h od ev => CoBrCons _ (F h) (fmapC od) (fmapC ev)
end.

Program CoFixpoint fmapE (n:list bool) (x:Be n) : Be n :=
match x with
| Bnil => Bnil
| Bcons _ _ h od ev => Bcons _ (F h) (fmapE od) (fmapE ev)
end.

Print fmapE.
*)
(*
Definition oddsR (n:list bool) (x:Br n) : Br (oddsT n).
unfold Br.
refine (fun n x => fun b p => x (true::b) _).
destruct n; num. 
Defined.
*)
Program Definition oddsR (n:list bool) (x:Br n) : Br (oddsT n) :=
  fun b p => x (true::b) _.
Next Obligation.
  destruct n; num.
Defined.

(* BUG *)
(* Functional Scheme oddsR_ind := Induction for oddsR Sort Prop. *)
(*
Require Import Coq.Program.Equality.
*)
Program Definition evensR (n:list bool) (x:Br n) : Br (evensT n) :=
  fun b p => x (false::b) _.
Next Obligation.
  destruct n; num.
Qed.

(*
Program CoFixpoint oddFromEvenCo (x:A) (n:CoNat) (v:CoBr n) : CoBr (S n) :=
match v with
  | CoBrCons _ h od ev => CoBrCons _ x (oddFromEvenCo (F h) ev) (fmapC od)
end.
Next Obligation.
  rewrite nana.
  simpl.
  reflexivity.
Qed.

Check oddFromEvenCo.
*)
(*
Program CoFixpoint oddFromEvenPe (x : A) (n : list bool) (v : Be n) : Be (succT n) :=
match v with
  | Bnil => Bcons _ x Bnil Bnil
  | Bcons _ _ h od ev => Bcons _ x (oddFromEvenPe (F h) ev) (fmapE od)
end.
Next Obligation.
  num. num.

match n with
  | nil => x
  | true :: r => oddFromEvenPr' (F (v nil _ )) (evensR v) r _
  | false :: r => F (v (true::r) _)
end.
Next Obligation.
  num.
Defined.
Next Obligation.
  destruct n; num.
Defined.
Next Obligation.
  num.
Defined.
*)

(* 
oddFromEvenPr' is a Br replacement for the Haskell oddFromEven above.
It is not defined as having the type 

A -> forall n, Br n -> Br (succT n) because it is recursive in a value hidden by the abbreviation Br (succT n).
*)

Program Fixpoint oddFromEvenPr' (x : A) (n : list bool) (v : Br n)  (b:list bool) (p:bOrd b < bOrd (succT n)) {struct b} : A :=
match b with
  | nil => x
  | true :: r => @oddFromEvenPr' (F (v nil _ )) (evensT n) (evensR v) r _
  | false :: r => F (v (true::r) _)
end.
Next Obligation.
  num.
Defined.
Next Obligation.
  destruct n; num.
Defined.
Next Obligation.
  num.
Defined.

Print oddFromEvenPr'.
Print oddFromEvenPr'_obligation_2.

(*

From the FAQ:

137  Is there an axiom-free proof of Streicher's axiom K for the equality on nat?
Yes, because equality is decidable on nat. Here is the proof.
*)
Require Import Eqdep_dec.
Require Import Peano_dec.

Theorem K_nat :
   forall (x:nat) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
Proof.
  intros; apply K_dec_set with (p := p).
  apply eq_nat_dec.
  assumption.
Qed.

(*
Similarly, we have
*)

Theorem eq_rect_eq_nat :
  forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
Proof.
  intros; apply K_nat with (p := h); reflexivity.
Qed.

(*

138  How to prove that two proofs of n<=m on nat are equal?
This is provable without requiring any axiom because axiom K directly holds on nat. Here is a proof using question 137.

*)

Require Import Arith.

Scheme le_ind' := Induction for le Sort Prop.

Theorem le_uniqueness_proof : forall (n m : nat) (p q : n <= m), p = q.
Proof.
  induction p using le_ind'; intro q.
  replace (le_n n) with
   (eq_rect _ (fun n0 => n <= n0) (le_n n) _ (refl_equal n)).
  2:reflexivity.
  generalize (refl_equal n).
     pattern n at 2 4 6 10, q; case q; [intro | intros m l e].
      rewrite <- eq_rect_eq_nat; trivial.
      contradiction (le_Sn_n m); rewrite <- e; assumption.
  replace (le_S n m p) with
   (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (refl_equal (S m))).
  2:reflexivity.
   generalize (refl_equal (S m)).
     pattern (S m) at 1 3 4 6, q; case q; [intro Heq | intros m0 l HeqS].
      contradiction (le_Sn_n m); rewrite Heq; assumption.
      injection HeqS; intro Heq; generalize l HeqS.
       rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
       rewrite (IHp l0); reflexivity.
Qed.

Lemma oddFromEvenPrNil : forall x n v p,
  @oddFromEvenPr' x n v nil p = x.
Proof.
  auto.
Defined.

Lemma oddFromEvenPrTrue : forall x n v r p i j,
    @oddFromEvenPr' x n v (true::r) p =
    @oddFromEvenPr' (F (v nil i)) (evensT n) (evensR v) r j.
Proof.
  intros.
  simpl.
  rewrite (le_uniqueness_proof i _).
  rewrite (le_uniqueness_proof j _).
  reflexivity.
Qed.

Lemma oddFromEvenPrFalse : forall x n v r p i,
    @oddFromEvenPr' x n v (false::r) p =
    F (v (true::r) i).
Proof.
  intros.
  simpl.
  rewrite (le_uniqueness_proof i _).
  reflexivity.
Qed.

(*
Lemma oddFrom_ind : forall (x : A) (n : list bool) (v : Br n)  (b:list bool), oddFromEvenPr' x n v b = 
match b return (bOrd b < bOrd (succT n)) -> A with
  | nil => fun _ => x
  | true :: r => fun p => oddFromEvenPr' (F (v nil (oddFromEvenPr'_obligation_1 x n v b p) )) _ (evensR _ v) r _
  | false :: r => fun p => F (v (true::r) _)
end.
*)

Definition oddFromEvenPr (x:A) (n:list bool) (v:Br n) : Br (succT n) := oddFromEvenPr' x v.

Definition toPrime (x:(forall n, Br n)) : Braun'.
unfold Braun'.
unfold Br.
intros x l.
apply (x (succT l) l).
num.
Defined.

Definition fromPrime (x:Braun') : (forall n, Br n).
unfold Braun'.
unfold Br.
intros x n b p.
apply x.
apply b.
Defined.

Print fromPrime.
Print toPrime.

Lemma toFromPrime :
  forall (x:(forall n, Br n)),
    (forall n n' b p q, aeq (x n b p) (x n' b q)) ->
    let y := fromPrime (toPrime x) in
      forall n n' b p q,
        aeq (x n b p) (y n' b q).
Proof.
  intros.
  unfold toPrime in y.
  unfold fromPrime in y.
  simpl in y.
  unfold y.
  apply H.
Qed.

Lemma fromToPrime :
  forall x:Braun',
    let y := toPrime (fromPrime x) in
      forall n,
        aeq (x n) (y n).
Proof.
  intros.
  unfold y; unfold fromPrime; unfold toPrime.
  apply Equivalence_Reflexive.
Qed.

Program Definition oddFrom x e :=
  toPrime (fun n => 
    match n with 
      | nil => _
      | _ => @oddFromEvenPr x (predT n) (fromPrime e (predT n))
    end).
Next Obligation.
  unfold Br.
  intros.
  destruct b as [|a b]; simpl in H.
  assert False.
  inversion H.
  inversion H0.
  destruct a; simpl in H.
  assert False.
  inversion H.
  inversion H0.
  assert False.
  inversion H.
  inversion H0.
Qed.
Next Obligation.
  rewrite succPred.
  auto. auto.
Qed.

Check even'.
  

Print oddFrom.

Check oddFrom.
Check unco.

Check (fun x e => reco (oddFrom x (unco e))).

Definition oddFromEven x e := reco (oddFrom x (unco e)).
Print coeq.
Print Braun.

CoFixpoint fmap (x:Braun) : Braun :=
  match x with
    | Cons h od ev => Cons (F h) (fmap od) (fmap ev) 
  end.
(*
Lemma oddFromCoeq : 
  forall x b,
    coeq (oddFromEven x b)
         (match b with
            | Cons h od ev => Cons x (oddFromEven (F h) ev) (fmap od)
          end).
Proof.
  cofix.
  intros.
  destruct b.
  unfold oddFromEven at 1.
  rewrite (frobeq (reco (oddFrom x (unco (Cons a b1 b2))))).
  simpl.
  constructor.
  unfold oddFrom.
  simpl.
  unfold toPrime.
  simpl. apply Equivalence_Reflexive.
  
  unfold oddFrom.
  unfold toPrime.
  simpl.
  unfold oddFromEvenPr.
  unfold oddFromEvenPr'.
  erewrite oddFromEvenPrTrue.
  apply oddFromCoeq.
  simpl.
  Check frob.
  unfold oddFrom.
  

  
  

Print fromPrime.

apply (x (succT l) l).
num.
Defined.


Definition oddFromP (x:A) (v:
*)
(*
Definition invariant (x:forall n, Br n) := 
  forall b, (forall n p n' p', aeq (x n b p) (x n' b p')).

Check evensR.

Hint Unfold invariant.
*)
Hint Unfold evensR.

Check evensR.

Lemma evensRinvariant: 
  forall n n' (x:Br n) (x':Br n'), 
    (forall z s t, aeq (x z s) (x' z t)) ->
    forall m p p', aeq (@evensR n x m p) (@evensR n' x' m p').
Proof.
  intros.
  unfold evensR in *.
  auto.
Defined.

Lemma oddsRinvariant: 
  forall n n' (x:Br n) (x':Br n'), 
    (forall z s t, aeq (x z s) (x' z t)) ->
    forall m p p', aeq (@oddsR n x m p) (@oddsR n' x' m p').
Proof.
  intros.
  unfold oddsR in *.
  auto.
Defined.

Lemma oddFrom_morph :
  forall x y, aeq x y -> 
    forall n p q r, 
      aeq (@oddFromEvenPr' x n p q r)
      (@oddFromEvenPr' y n p q r).
Proof.
  intros.
  destruct q.
  auto.
  reflexivity.
Qed.


Lemma oddFromInvariant : 
  forall n n' (x:Br n) (x':Br n'), 
    (forall z s t, aeq (x z s) (x' z t)) ->
    forall v  b p p', 
      aeq (@oddFromEvenPr' v n x b p)
      (@oddFromEvenPr' v n' x' b p').
Proof.
  intros.
  generalize dependent n;
    generalize dependent n';
      generalize dependent v.
  induction b; intros.
  simpl. reflexivity.
  destruct a.
  Check oddFromEvenPrTrue.
  assert (bOrd nil < bOrd n) as i.
  simpl.
  simpl in p.
  rewrite succTisS in p. omega.
  assert (bOrd b < bOrd (succT (evensT n))) as j.
  simpl in p.
  rewrite succTisS in *.
  destruct n as [|a n]; simpl; try (omega); destruct a; simpl in *; try (omega).
  erewrite oddFromEvenPrTrue with (i := i) (j := j).
  assert (bOrd nil < bOrd n') as i'.
  simpl.
  simpl in p'.
  rewrite succTisS in p'. omega.
  assert (bOrd b < bOrd (succT (evensT n'))) as j'.
  simpl in p'.
  rewrite succTisS in *.
  destruct n' as [|a n']; simpl; try (omega); destruct a; simpl in *; try (omega).
  erewrite oddFromEvenPrTrue with (i := i') (j := j').
  Check oddFrom_morph.
  rewrite oddFrom_morph.
  auto using evensRinvariant.
  apply F_morph.
  apply H.
  assert (bOrd (true::b) < bOrd n) as i.
  rewrite succTisS in p; simpl in *. omega.
  erewrite oddFromEvenPrFalse with (i := i).
  assert (bOrd (true::b) < bOrd n') as i'.
  rewrite succTisS in p'; simpl in *. omega.
  erewrite oddFromEvenPrFalse with (i := i').
  apply F_morph.  
  apply H.
Qed.

Program Definition fmapR (n:list bool) (x:Br n) : Br n :=
  fun b p => F (x b _).

Lemma fmapInvariant: 
  forall n n' (x:Br n) (x':Br n'), 
    (forall z s t, aeq (x z s) (x' z t)) ->
    forall m p p', aeq (@fmapR n x m p) (@fmapR n' x' m p').
Proof.
  intros.
  unfold fmapR in *.
  auto.
Qed.


Lemma oddFromUnfold : forall x e b,
  aeq (oddFrom x e b)
  (match b with
     | nil => x
     | true :: r => @oddFrom (F (e nil)) (even' e) r
     | false :: r => F (e (true::r))
   end).
Proof.
  intros.
  generalize dependent x; 
    generalize dependent e.
  induction b; intros; simpl.
  unfold oddFrom; simpl; auto.
  unfold toPrime. simpl. reflexivity.
  destruct a; simpl.
  unfold oddFrom.
  unfold toPrime.
  simpl.
  pose (succT b) as sb; fold sb;
    destruct b as [|a b].
  simpl in sb.
  unfold sb. simpl.
  apply F_morph.
  unfold fromPrime; simpl.
  reflexivity.
  destruct a. simpl in *.
  apply oddFromInvariant.
  intros.
  apply evensRinvariant.
  intros.
  unfold fromPrime.
  Print evensR.
  unfold evensR.
  unfold even'.
  reflexivity.
  simpl in *.
  apply F_morph.
  unfold oddFrom.
  unfold fromPrime.
  unfold even'.
  unfold evensR.
  reflexivity.
  unfold oddFrom.
  unfold toPrime.
  simpl.
  apply F_morph.
  unfold fromPrime.
  reflexivity.
Qed.

Lemma allEq :
  forall x y,
    (forall b, aeq (unco x b) (unco y b)) ->
    coeq x y.
Proof.
  cofix.
  intros.
  destruct x; destruct y.
  constructor.
  pose (H nil) as heq.
  simpl in heq.
  apply heq.
  apply allEq.
  intros r; pose (H (true::r)) as leq.
  simpl in leq. apply leq.
  apply allEq.
  intros r; pose (H (false::r)) as leq.
  simpl in leq. apply leq.
Qed.


Add Parametric Morphism : oddFrom with
  signature aeq ==> (@exteq (list bool)) ==> (@eq (list bool)) ==> aeq as oddFrom_mor.
Proof.
  intros.
  generalize dependent x;
    generalize dependent y;
        generalize dependent x0;
            generalize dependent y0.
  induction y1; intros.
  repeat (rewrite oddFromUnfold).
  auto.
  destruct a.
  rewrite oddFromUnfold.
  rewrite (@oddFromUnfold y y0 (true::y1)).
  apply IHy1.
  unfold even'.
  unfold exteq.
  intros.
  unfold exteq in H0.
  apply H0.
  apply F_morph.
  unfold exteq in H0.
  apply H0.
  rewrite oddFromUnfold.
  rewrite (@oddFromUnfold y y0 (false::y1)).
  apply F_morph.
  unfold exteq in H0.
  apply H0.
Qed.
  

Lemma oddFromPlug :
  forall x b,
    match b with
      | Cons h od ev => 
        coeq (oddFromEven x b) 
             (Cons x (oddFromEven (F h) ev) (fmap od))
    end.
Proof.
  intros.
  destruct b; simpl.
  unfold oddFromEven.
  apply allEq.
  intros.
  destruct b as [|h t].
  simpl.
  rewrite oddFromUnfold.
  reflexivity.
  destruct h; simpl.
  Check unco_mor.
  pose unco_mor as unco_help.
  unfold exteq in unco_help.
  apply unco_help.
  pose reco_mor as reco_help.
  apply reco_help.
  unfold exteq.
  intros r.
  rewrite oddFromUnfold.
  simpl.
  unfold even'.
  simpl.
  apply oddFrom_mor.
  reflexivity.
  unfold exteq; intros.
  reflexivity. reflexivity.
  
  pose unco_mor as unco_help.
  unfold exteq in unco_help.
  apply unco_help.
  simpl.
  Check Equivalence_Transitive.
  Print Transitive.
  Check oddFromUnfold.
  eapply Equivalence_Transitive with (y := reco (fun z => F (unco (Cons a b1 b2) (true :: z)))).
  apply reco_mor.
  unfold exteq.
  intros.
  apply oddFromUnfold.
  simpl.
  apply allEq.
  intros.
  clear unco_help.
  generalize dependent b1.
  induction b.
  simpl.
  destruct b1; simpl. reflexivity.
  destruct a0.
  simpl.
  intros.
  destruct b1. 
  apply IHb.
  intros.
  simpl.
  destruct b1.
  apply IHb.
Qed.

Definition evenR' (n:list bool) (od:Br n) : Br n := fmapR od.

Lemma obl : forall b, bOrd b < bOrd (succT b).
Proof.
  num.
Defined.

Lemma oddRhelp : forall n b (p:bOrd b < bOrd n), bOrd b < bOrd (succT n).
Proof.
  num.
Qed.

Check evenR'.

(*
Program Fixpoint oddR (X:A) (n:list bool) (b:list bool) (p:bOrd b < bOrd n) {measure bOrd n} : A :=
  let er := @evenR' n (@oddR _) in
    @oddFromEvenPr (F X) n er b (@oddRhelp n b p).
Next Obligation.
  apply obl.
Defined.
*)
(*
Function oddR (X:A) (n:list bool) (b:list bool) (p:bOrd b < bOrd n) {measure bOrd n} : A := @oddFromEvenPr (F X) b (evenR' (oddR X b)) b (obl b).
(*Error: find_call_occs : Lambda*)
(* Error: Unable to find an instance for the variables b, p.*)
*)


Program Fixpoint oddR (X:A) (n:list bool) {measure bOrd n} : Br n :=
  fun b p => 
    let er := evenR' (oddR b) in
      @oddFromEvenPr (F X) b er b _.
Next Obligation.
  apply obl.
Defined.

(*
Functional Scheme oddRsc := Induction for oddR Sort Prop.
Error: Cannot define graph(s) for oddR
*)

(*
Axiom proofIrrel : forall (P:Prop) (p q:P), p = q.
*)
Lemma oddRoddFrom : 
  forall X n b p, 
    exists q,
      aeq 
      (@oddR X n b p)
      (@oddFromEvenPr (F X) _ (evenR' (@oddR X b)) b q).
Proof.
  intros.
  assert (bOrd b < bOrd (succT b)) as q.
  num.
  exists q.
  remember (bOrd n) as nn in |- *.
  generalize dependent b.
  generalize dependent n.
  induction nn; intros.
  induction n.
  simpl in p; induction b; simpl in p; inversion p.
  destruct a; simpl in *; inversion Heqnn.

  unfold oddR at 1.
  Check Fix_measure_sub.
  Print Fix_measure_sub.
  pose (fun (n0 : list bool)
           (oddR0 : forall n' : {n' : list bool | bOrd n' < bOrd n0},
                    Br (proj1_sig n')) (b0 : list bool)
           (p0 : bOrd b0 < bOrd n0) =>
         let er :=
           evenR'
             (oddR0
                (exist (fun n' : list bool => bOrd n' < bOrd n0) b0
                   (oddR_obligation_1 X n0 oddR0 b0 p0))) in
         oddFromEvenPr (F X) er b0 (oddR_obligation_2 X n0 oddR0 b0 p0))
  as I.
  fold I.
  unfold Fix_measure_sub.
  rewrite F_unfold.
  apply oddFromInvariant.
  intros.
  unfold evenR'.
  apply fmapInvariant.
  intros.
  simpl in s0.
  fold I.
  unfold oddR.
  unfold Fix_measure_sub.
  unfold evenR'.
  Check oddFromInvariant.
  Check Fix_measure_F_sub.
  Check (lt_wf (bOrd b)).
  Check Fix_measure_F_inv.
  
  erewrite Fix_measure_F_inv with (m := (fun n0 : list bool => bOrd n0)) (s := (lt_wf ((fun n0 : list bool => bOrd n0) b))).
  unfold proj1_sig.
  Print Equivalence.
  Check Equivalence_Reflexive.
  Print Reflexive.
  Print Acc.
  Locate "_ < _".
  unfold lt in s0, t0.
  rewrite (le_uniqueness_proof s0 t0).
  apply Equivalence_Reflexive.
Qed.

Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.

Lemma oddRInvariant : 
  forall X n n' b p q, 
    aeq (@oddR X n b p)
        (@oddR X n' b q).
Proof.
  Check (@well_founded_ind nat lt lt_wf).
  intros.
  remember (bOrd n) as nn in |- *.
  generalize dependent b.
  generalize dependent n.
  generalize dependent n'.
  generalize dependent X.
  generalize dependent nn.
  pose (fun (nn : nat) => forall (X : A) (n' n : list bool),
   nn = bOrd n ->
   forall (b : list bool) (p : bOrd b < bOrd n) (q : bOrd b < bOrd n'),
   aeq (oddR X n b p) (oddR X n' b q)) as P.
  apply (@well_founded_ind nat lt lt_wf P).
  unfold P in *; clear P.
  intros.
  assert (exists r,
    aeq 
    (@oddR X n b p)
    (@oddFromEvenPr (F X) _ (evenR' (@oddR X b)) b r)) as J.
  apply oddRoddFrom.
  destruct J.
  assert (exists s,
    aeq 
    (@oddR X n' b q)
    (@oddFromEvenPr (F X) _ (evenR' (@oddR X b)) b s)) as I.
  apply oddRoddFrom.
  destruct I.
  eapply Equivalence_Symmetric in H2.
  assert (aeq 
    (oddFromEvenPr (F X) (evenR' (oddR X b)) b x0)
    (oddFromEvenPr (F X) (evenR' (oddR X b)) b x1)).
  apply oddFromInvariant.
  intros.
  unfold evenR'.
  apply fmapInvariant.
  intros.
  eapply H.
  rewrite H0.
  apply p. auto.

  eapply Equivalence_Transitive.
  apply H1.
  eapply Equivalence_Transitive.
  apply H3.
  auto.
Qed.

Definition evenR X (n:list bool) : Br n := evenR' (oddR X n).

Require Import Recdef.

(*BUG*)
(*
Function oddR (n:list bool) (b:list bool) (p:bOrd b < bOrd n) {measure bOrd n} : A := oddFromEvenPr (F X) b (evenR' b (oddR b)) b (obl b).
*)
(* Error: Unable to find an instance for the variables b, p.*)
(*
Function oddR (n:list bool) {measure bOrd n} : Br n :=
  fun b p => oddFromEvenPr (F X) b (evenR' b (oddR b)) b (obl b).
*)
(*Error: find_call_occs : Lambda*)

(*
Program Definition iterate' X n : Br n :=
fun b p => 
  match b with
    | nil => X
    | true ::r => oddR X (succT (succT r)) r _
    | false::r => evenR X (succT r) r _
  end.
Next Obligation.
  num.
Defined.
Next Obligation.
  num.
Defined.
*)

Program Definition iterate' X : Braun' :=
fun n => 
  match n with
    | nil => X
    | true ::r => oddR X (succT r) r _
    | false::r => evenR X (succT r) r _
  end.
Next Obligation.
  num.
Defined.
Next Obligation.
  num.
Defined.

Definition iterate X := reco (iterate' X).



(*
Add Parametric Relation A : A (@eq A)
reflexivity proved by reflexivity
symmetry proved by symmetry
transitivity proved by transitivity
as eq_equiv.
*)
(*
Check iterate' (eq_equiv nat) 0 S.
Check iterate' (eq_equiv nat) 0 S nil.
Eval compute in iterate' (eq_equiv nat) 0 S nil.
Eval compute in iterate' (eq_equiv nat) 0 S (false::nil).
Eval compute in iterate' (eq_equiv nat) 0 S (false::true::nil).

Print iterate'.
Print oddR.
Extraction Language Haskell.
Extraction iterate'.
Extraction evenR.
Extraction evenR'.
Extraction oddR.
Extraction oddFromEvenPr'.
*)
Lemma headIter : forall X, headB (iterate X) = X.
Proof.
  auto.
Qed.

Lemma coext : forall f g,
  coeq (reco f) (reco g) <-> exteq f g.
Proof.
  split.
  unfold exteq.
  intros fg n.
  generalize dependent f. generalize dependent g.
  induction n; intros;
  rewrite frobeq in fg;
  simpl in fg;
  replace (reco f) with (frob (reco f)) in fg;
  simpl in fg;
  inversion fg; subst; auto.
  destruct a.
  eapply IHn with (f := fun y => f (true:: y)) (g := fun y => g (true:: y)).
  auto.
  eapply IHn with (f := fun y => f (false:: y)) (g := fun y => g (false:: y)).
  auto.

  generalize dependent f. generalize dependent g.
  cofix.
  intros.
  rewrite frobeq.
  simpl.
  replace (reco f) with (frob (reco f)). 
  simpl.
  unfold exteq in H.
  constructor.
  apply H.
  eapply coext with (f := fun y => f (true:: y)) (g := fun y => g (true:: y)).
  unfold exteq.
  intros.
  apply H.
  eapply coext with (f := fun y => f (false:: y)) (g := fun y => g (false:: y)).
  unfold exteq.
  intros.
  apply H.
  symmetry. apply frobeq.
Qed.

Lemma fmapCommute : forall x, coeq (fmapB (reco x)) (reco (fmap' x)).
Proof.
  cofix.
  intros.
  rewrite frobeq.
  simpl.
  replace (fmapB (reco x)) with (frob (fmapB (reco x))).
  simpl.
  constructor.
  simpl.
  unfold fmap'.
  reflexivity.
  apply fmapCommute.
  apply fmapCommute.
  auto using frobeq.
Qed.

Lemma evenIter : forall X,
    coeq (evenB (iterate X)) (fmapB (oddB (iterate X))).
Proof.
  unfold iterate.
  simpl.
  Check fmapCommute.
  intros X.
  rewrite fmapCommute. 
  Locate " /\ ".
  Print and.
  Print proj1.
  Check (fun p q => proj1 (coext p q)).
  Check (fun p q => proj2 (coext p q)).
  eapply (fun p q => proj2 (coext p q)).
  unfold exteq.
  intros n.
  reflexivity.
Qed.

Print Br.

Definition oddFromEven (x:A) (w:Braun) := 
  reco (fun n => (@oddFromEvenPr x n (fun b i => unco w b)) n (obl n)).


Print iterate. Print iterate'.
Print oddR.

Lemma oddIter : forall X,
    coeq (oddB (iterate X)) (oddFromEven (F X) (evenB (iterate X))).
Proof.
  unfold iterate.
  simpl.
  unfold oddFromEven.
  intros X.
  eapply (fun p q => proj2 (coext p q)).
  unfold exteq.
  intros n.
  unfold oddFromEvenPr.
  
  r
    (unco
      (reco
        (fun y : list bool =>
          evenR (succT y) y (iterate'_obligation_2 refl)))) with 
        (fun y : list bool =>
          evenR (succT y) y (iterate'_obligation_2 refl)).
  unfold oddR.
  apply oddFromInvariant.
  

  reflexivity.



  rewrite frobeq.


Fixpoint applyN (a:Set) (n:nat) (f:a->a) (z:a) : a :=
  match n with
    | 0 => z
    | S m => f (applyN _ m f z)
  end.


Lemma itWorks : forall b, iterate _ 0 S b = bOrd b.
Proof.

  intros b.
  remember (bOrd b) as b'.
  generalize dependent b.
  induction b' as [b' | b' IH].

  intros b bval.
  assert (b = nil) as bnil.
  destruct b as [_ | bh bt]; auto.
    destruct bh; simpl in bval; inversion bval.
  rewrite bnil.
  auto.

  intros b bval.
  assert (exists bh, exists bt, b = bh::bt) as bcons.
  destruct b as [bn | bh bt].
    simpl in bval. inversion bval.
    exists bh. exists bt. auto.
  destruct bcons as [bh bcons].
  destruct bcons as [bt bcons].
  subst.
  
  destruct bh.
  Focus 2.
  assert (iterate _ 0 S (false::bt) = S (iterate _ 0 S (true::bt))) as R.
  unfold iterate.
  unfold evenR. 
  unfold evenR'. 
  unfold fmapR. 
  reflexivity.
  assert (b' = bOrd (true::bt)) as oneless.
  simpl bOrd.
  simpl bOrd in bval.
  omega.
  rewrite -> R.
  f_equal.
  apply IH. exact oneless.

  destruct bt.
  simpl.
  unfold oddR. unfold oddFromEvenPr. 
  unfold Fix_measure_sub. simpl. simpl in bval. auto.
  destruct b.
  Focus 2.
  assert (iterate nat 0 S (true::false::bt) = S(iterate _ 0 S (false::true::bt))).
  unfold iterate.
  unfold oddR. unfold oddFromEvenPr. unfold fmapR.
  simpl. unfold Fix_measure_sub. simpl.
  
  
simpl. 
  Print oddR.
  unfold oddFromEvenPr.
simpl. simpl.
  

  assert (exists U, exists V, iterate nat 0 S (false::bt) = evenR _ 0 S U bt V) as i2e.
  refine (ex_intro _ _ _).
  refine (ex_intro _ _ _).
  simpl iterate. reflexivity.
  assert (forall U V, exists W, exists Y, evenR nat 0 S U bt V = fmapR _ S W (oddR _ 0 S _) bt Y) as e2f.
  intros.
  refine (ex_intro _ _ _).
  refine (ex_intro _ _ _).
  unfold evenR. reflexivity.
  assert (forall W Y, exists U, exists V, fmapR nat S W (oddR nat 0 S W) bt Y = S (oddR _ 0 S U bt V)).
  intros.
  eapply ex_intro.
  eapply ex_intro.
  unfold fmapR. reflexivity.
  assert (forall U V, S (oddR nat 0 S U bt V) = S (iterate _ 0 S (true::bt))).
  intros.
  f_equal.
  simpl iterate. 
  Abort.
(*
reflexivity.
  


  assert (exists U, exists V, iterate nat 0 S (false::bt) = evenR _ 0 S U bt V).
  Print iterate.
  exists (succT bt).
  Print iterate.
  exists (iterate_obligation_2  (false::bt) bt (refl_equal (false::bt))).
  simpl iterate. reflexivity.
  

  
  assert (exists n', (S b' = 1 + (2*n)) \/ (S b' = S
  simpl.
    destruct b as H.
  induction b.
    auto.
    



  Show Script.
  proof.
    Show Script.
  
  per induction on b'.

  Show Script.

    suppose it is 0.
      let b:(list bool).
      claim (forall c, bOrd c = 0 -> c = nil).
      let c:(list bool).
      per cases on c.
        suppose it is nil.
          thus thesis.
        suppose it is (d::e).
          per cases on d.
            suppose it is true.
              assume H:(bOrd (true::e) = 0).
              reconsider H as (1 + 2 * bOrd e = 0).
              reconsider H as (S(2 * bOrd e) = 0).
              reconsider H as False.
          per induction on d.
            suppose it is true.
          reconsider H as 
          
      given b such that b0:(0 = bOrd b).
      define b'' as (bOrd b).
      claim bnil:(forall c, c = b -> c = nil).
        per induction on b.
          suppose it is nil.
            thus thesis.
          suppose it is (cons c d).
            reconsider b0 as (0 = bOrd (c::d)).
      
proof.

let b:(list bool).
define b' as (bOrd b).
escape.
generalize dependent b.
induction b'.
per induction on b'.

  suppose it is 0.
  claim (bOrd b = 0).

  apply well_founded_ind with (R := fun x y => bOrd x < bOrd y).
  Require Import Coq.Arith.Wf_nat.
  apply well_founded_lt_compat with (f := bOrd).
  auto.

  intros.
  destruct x.
  reflexivity.
  destruct b.
  hnf.
  simpl.
  unfold oddR. simpl. unfold Fix_measure_sub. simpl.
  unfold oddFromEvenPr. simpl. unfold fmapR. simpl.
  f_equal. f_equal. f_equal.
  assert (forall n m, n = m -> S n = S m). clear.
  intros.
  f_equal. assumption.
  unfold Fix_measure_sub. simpl. hnf.
  apply H0.

  constructor.
  intros.
  induction
  constructor.


  intros b.
  remember (bOrd b) as z.
  generalize dependent b.
  induction z.
  intros.
  induction b.
  simpl. reflexivity.
  induction a; simpl in Heqz; inversion Heqz.
  intros.
  induction b.
  simpl. reflexivity.
  
  
  sim
  induction b; simpl; inversion Heqz; auto.
  induction b.
  simpl. reflexivity.
  induction a.
  simpl.
  unfold oddR.
  simpl.
  reflexivity.

Extraction Language Haskell.
Extraction iterate.
Extraction oddR.

Print oddFromEvenPr.

  simpl. omega.
  simpl in p.
omega.
Qed.
Next Obligation.
  Check oddFromEvenPr_obligation_4.
  Print oddFromEvenPr_obligation_4.
  subst.


  case a.
  elim a. simpl. apply IHn.

Definition oddsR (n:list bool) (x:Br n) : Br (oddsT n).
refine (fun n x =>
fun 
match n with
| 
*)
(*
Definition oddsR (n:nat) (x : forall (b:list bool) (_:bOrd b < n), A) (c : list bool) (d:bOrd (true::c) < n) : A := x (true :: c) d.
Definition evensR (n:nat) (x : forall (b:list bool) (_:bOrd b < n), A) (c : list bool) (d:bOrd (false::c) < n) : A := x (false :: c) d.


Program Fixpoint oddFromEvenP (f : A->A) (x : A) (n : list bool) (v : Br (bOrd n)) {struct n} : A :=
match n with
| nil => x
| true :: r => oddFromEvenP f (f (v nil _ )) r (fun p => fun q => v (false::p) _)
| false :: r => f (*oddsR _ v r _*) (v (true::r) _)
end.
Obligations.
Next Obligation.
  simpl. omega.
Qed.
Next Obligation.
  simpl.
  omega.
Qed.

Print oddFromEvenP.

Definition EvenR (n:nat) (odR : forall (b:list bool) (_:bOrd b < n), A) (c:list bool) (p:bOrd c < n) : A := F (odR c p).

Program Fixpoint oddFromEvenPr (f:A->A)(x:A) (n : list bool) (v : forall (b:list bool) (_:bOrd (false::b) < bOrd (true::n)), A) {struct n} : A :=
match n with
| nil => x
| true :: r => oddFromEvenP f (f (v nil _ )) r (fun p => fun q => v (false::p) _)
| false :: r => f (*oddsR _ v r _*) (v (true::r) _)
end.
Obligations.
Next Obligation.
  simpl. omega.
Qed.
Next Obligation.
  simpl.
  omega.
Qed.
Next Obligation.
  simpl. omega.
Qed.

Print oddFromEvenP.

Definition evS (odS:list bool -> A) (n:list bool) : #A := 
  Return (F (odS n)).
CoFixpoint odS (evS:list bool -> A) (n:list bool) : #A := 
  Return (oddFromEven F (F X) evS n).

Require Import Computation.Termination.
Require Import Computation.Eval.
Require Import Computation.Tactics.

Definition evS' (odS:list bool -> A) (n:list bool) : A.
refine (fun (odS:list bool -> A) (n:list bool) =>
  eval (evS odS n) _).
constructor.
unfold evS.
eapply ex_intro.
eapply TerminatesReturnWith.
Defined.

Definition odS' (evS:list bool -> A) (n:list bool) : A.
refine (fun (evS:list bool -> A) (n:list bool) =>
  eval (odS evS n) _).
constructor.
remember (odS evS0 n) as oen.
destruct oen.
Guarded.
exists a.
apply TerminatesReturnWith.
unfold odS in Heqoen.
Admitted.

Fixpoint evSS (n:list bool) : A := evS' odSS n
with odSS (n:list bool) : A := odS' evSS n.
inversion Heqoen.
Guarded.


unfold odS.
eapply ex_intro.
assert (((cofix odS (evS : list bool -> A) (n0 : list bool) : 
       #A := Return (oddFromEven F (F X) evS n0)) evS0 n) = decomp ((cofix odS (evS : list bool -> A) (n0 : list bool) : 
       #A := Return (oddFromEven F (F X) evS n0)) evS0 n)) as DI.
apply decomp_thm.
destruct (decomp ((cofix odS (evS : list bool -> A) (n0 : list bool) : 
       #A := Return (oddFromEven F (F X) evS n0)) evS0 n)).
Guarded.
rewrite DI.
Print TerminatesReturnWith.
eapply TerminatesReturnWith with (a

unfold oddFromEven. simpl.
induction n. simpl.
simpl.
induction n. simpl.

eapply TerminatesReturnWith.
Defined.
Print TerminatesWith.
Print eval.

(*  nx <- Fs (Return X);*)
  match n with (*oddFromEvenC F nx evS n.*)
    | nil => Return (F X) (*Return nx*)
    | true ::r =>
        next <- liftM _ F (evS 1 nil);
        oddFromEvenC F next (evensC (evS (bOrd n))) r
    | false::r => liftM _ F (oddsC (evS (bOrd n)) r)
  end.


CoFixpoint isEven (*isOdd:nat->#bool*) (n:nat) : #bool :=
  match n with
    | 0      => Return true
    | (S n') => x <- isOdd n';Return (negb x)
  end
with
 isOdd (*isEven:nat->#bool*) (n:nat) : #bool :=
  match n with
    | 0      => Return false
    | (S n') => x <- isEven n';
                Return (negb x)
  end.
(*

Check isEven.


CoFixpoint isEven' := match (kludge isEven) with f => isEven isOdd' end
with       isOdd' := (kludge isOdd) isEven'
with       kludge := (fun x=>x).



Definition kludge := (fun (A:Type) => fun (x:A)=>x).
CoFixpoint isEven' := (kludge _ isEven) isOdd'
with       isOdd' := (kludge _ isOdd) isEven'.
*)

(*
Definition bcup (x:Bc) : #Braun' :=
  Return (fun n => x n)
*)

Fixpoint oddFromEven (f : A->A) (x : A) (v : Braun') (n : list bool) {struct n} : A :=
match n with
| nil => x
| true :: r => oddFromEven f (f (v nil)) (evens v) r
| false :: r => fmap' f (odds v) r
end.


Definition restrict (x:Braun') (n:nat) (b:list bool) (_:bOrd b < n) : A :=
  x b.

Definition oddsR (n:nat) (x : forall (b:list bool) (_:bOrd b < n), A) (c : list bool) (d:bOrd (true::c) < n) : A := x (true :: c) d.
Definition evensR (n:nat) (x : forall (b:list bool) (_:bOrd b < n), A) (c : list bool) (d:bOrd (false::c) < n) : A := x (false :: c) d.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Recdef.

Require Import Coq.omega.Omega.

Program Fixpoint oddFromEvenP (f : A->A) (x : A) (n : list bool) (v : forall (b:list bool) (_:bOrd b < bOrd n), A) {struct n} : A :=
match n with
| nil => x
| true :: r => oddFromEvenP f (f (v nil _ )) r (fun p => fun q => v (false::p) _)
| false :: r => f (*oddsR _ v r _*) (v (true::r) _)
end.
Obligations.
Next Obligation.
  simpl. omega.
Qed.
Next Obligation.
  simpl.
  omega.
Qed.

Print oddFromEvenP.

Definition EvenR (n:nat) (odR : forall (b:list bool) (_:bOrd b < n), A) (c:list bool) (p:bOrd c < n) : A := F (odR c p).

Program Fixpoint oddFromEvenPr (f:A->A)(x:A) (n : list bool) (v : forall (b:list bool) (_:bOrd (false::b) < bOrd (true::n)), A) {struct n} : A :=
match n with
| nil => x
| true :: r => oddFromEvenP f (f (v nil _ )) r (fun p => fun q => v (false::p) _)
| false :: r => f (*oddsR _ v r _*) (v (true::r) _)
end.
Obligations.
Next Obligation.
  simpl. omega.
Qed.
Next Obligation.
  simpl.
  omega.
Qed.
Next Obligation.
  simpl. omega.
Qed.

Print oddFromEvenP.

Program Definition EvenR (b:list bool) (odR : forall (n:list bool) (_:bOrd (true::b) < bOrd(n), A) (c:list bool) (p:bOrd c < n) : A := F (odR n c p).



Program Fixpoint odR (n:nat) (b:list bool) (p:bOrd (true::b) = n) {struct n}: A :=
  oddFromEvenP F (F X) b (EvenR _ (odR )).
Next Obligation.
Obligation 3.
Obligation 2.

Program Fixpoint odR (n:nat) (b:list bool) (p:bOrd b < n) {struct n}: A :=
match n with
| 0 => _
| S m' => oddFromEvenP F (F X) b (EvenR _ (odR m' _))
end.
Obligations.
Obligation 3.

Obligation 2.
Next Obligation.

End Single.

Extraction Language Haskell.
Extraction oddFromEvenP.
Extraction oddsR.

Definition evS (odS:Braun') (n:list bool) : A := odS n.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Recdef.
Program Fixpoint odS (n:list bool) {measure bOrd n} : A := 
  oddFromEven F (F X) (evS odS) n.
Next Obligation.
  
Check Function.

Check odS.

Obligations.
intros.
Proof.

Fixpoint evC := fun n => Return evS odC
with       odC := odS evC.
*)

Section Sharp.

Variable A:Set.
Variable X:A.
Variable F:A->A.



Definition oddsCC (x : Bc A) (n : list bool) := 
  v <- x (true :: n);
  Return v.
Definition evensCC (x : Bc A) (n : list bool) := 
  v <- x (false :: n);
  Return v.

CoFixpoint oddFromEvenCC (x : A) (v : Bc A) (n : list bool) : #A := Return x.
(*
match n with
| nil => Return x
| true ::r => Return x (*thead <- call v nil;
              oddFromEvenCC (F thead) (fun n => call v (false::n)) r*)
| false::r => Return x (*liftM _ F (oddsCC v r)*)
end.
*)
Locate "call".

CoFixpoint evS (m:list bool) : #A :=
  x <- call odS m;
  Return (F x)
with odS (n:list bool) : #A := 
  oddFromEvenCC (F X) (fun b => call (evS b)) n.

CoFixpoint evS (n:list bool) : #A := 
  x <- odS n;
  Return (F x)
(*Fs (odS n)*)
(*
case odS n
  call (fmapC Fs odS n)*)
with odS (n:list bool) : #A := 
(*  nx <- Fs (Return X);*)
  ev <- evS;
  match n with (*oddFromEvenC F nx evS n.*)
    | nil => Return (F X) (*Return nx*)
    | true ::r =>
        next <- liftM _ F (evS nil);
        oddFromEvenC F next (evensC evS) r
    | false::r => liftM _ F (oddsC evS r)
  end.

CoFixpoint evS (odS : Bc) (n:list bool) : #A := 
  x <- odS n;
  Return (F x).
(*Fs (odS n)*)
(*
case odS n
  call (fmapC Fs odS n)*)
CoFixpoint odS (evS :Bc) (n:list bool) : #A := 
  nx <- Fs (Return X);
  oddFromEvenC F nx evS n.

CoFixpoint evS' := (id evS) odS'
with odS' := (id odS) evS'.

CoFixpoint oddFromEven' (f : A->A) (x : A) (v : Braun) : Braun :=
  match v with
    | Cons h od ev => Cons x (oddFromEven' f (f h) ev) (fmap f od)
  end.

CoFixpoint evs : Braun := fmap F
match id ods with
| Cons h o e => Cons h o e(*fmap F ods*) (*Cons (F h) (fmap F o) (fmap F e)*)
end
(*fmap F ods*)
with ods : Braun := oddFromEven' F (F X) evs.
    in
      Stream x od ev




End Single.

Extraction oddFromEven'.
Extraction Language Haskell.
Extraction oddFromEven'.

Extraction unco.
Extraction unco'.
Definition oddFromBraun (A:Set) (f:A->A) (x:A) (v:Braun A) : Braun A :=
  reco A (oddFromEven A f x (unco A v)).
Extraction oddFromBraun.


Extraction (fun (x : nat) => x).

Section Iterate.
  
  Variable F : A -> A.
  Variable X : A.

  Definition id (x:nat) := x.

  Require Import Coq.Program.Tactics.

  Program Fixpoint evF (n:list bool) {measure bOrd n} : A :=
    fmap' F odF n
  with odF (n:list bool) {measure bOrd n} : A :=
    oddFromEven F (F X) evF n.
  

  Print eq.

  Require Import Recdef.
(*
  Inductive evP : Braun' -> Prop :=
    evPC : forall v, odP v -> evP (fmap' v)
  with odP : Braun' -> Prop :=
    odPC : forall v, evP v -> 
  *)
(*
  Fixpoint evF (n:list bool) (m:nat) (p:bOrd n = m) {struct m} : A :=
    fmap' F (fun x => odF x (bOrd x) (refl_equal (bOrd x))) n
  with odF (n:list bool) (m:nat) (p:bOrd n = m) {struct m} : A :=
    oddFromEven F (F X) (fun x => evF x (bOrd x) (refl_equal (bOrd x))) n.
  *)  
  Definition iterate : forall n,
    ( forall m, bOrd m < bOrd n -> A) -> A.
  refine (fun n => fun rec =>
    match n with 


  Function oddF (n:list bool) {measure bOrd n} : A :=
    match n with
      | nil => F X
      | true::r => 
        oddFromEven F (F (F (F X))) (evens (fun z => F (oddF z))) r
      | false::r =>
        fmap' F (odds (fmap' F oddF)) r
        end.

  Fixpoint evF (n:list bool) (m:nat) (p:bOrd n = m) {struct m} : A :=
    fmap' F (fun x => odF x (bOrd x) (refl_equal (bOrd x))) n
  with odF (n:list bool) (m:nat) (p:bOrd n = m) {struct m} : A :=
    oddFromEven F (F X) (fun x => evF x (bOrd x) (refl_equal (bOrd x))) n.
    

  Definition BraunP := list bool -> A -> Prop.

  Definition evensP (f : BraunP) (n : list bool) (v : A) : Prop :=
    f (true :: n) v.
  Definition oddsP (f : BraunP) (n : list bool) (v : A) : Prop :=
    f (false :: n) v.
  
  Definition fmapP (f : BraunP) (n : list bool) (v : A) : Prop :=
    exists a, f n a /\ F a = v.

  Inductive oddFrom (x : A) (v : BraunP) : BraunP :=
    | oddFromN : oddFrom x v nil x
    | oddFromT : forall r z,
                 oddFrom (F x) (evensP v) r z ->
                 oddFrom x v (true :: r) z
    | oddFromF : forall r z, 
                 fmapP (oddsP v) r z ->
                 oddFrom x v (false :: r) z.

  Fixpoint oddFromFunc (x:A) (v:BraunP) (n:list bool) (t:A) {struct n} : Prop :=
    match n with
      | nil => t = x
      | true :: r => oddFromFunc (F x) (evensP v) r t
      | false :: r => fmapP (oddsP v) r t
    end.

  Print oddFromFunc.

  Fixpoint evF (n:list bool) (t:A) {struct n} : Prop :=
    fmapP odF n t
  with odF (n:list bool) (t:A) {struct n} : Prop :=
    match n with
      | nil => t = F X
      | true :: r => oddFromFunc (F (F X)) (evensP evF) r t
      | false :: r => fmapP (oddsP evF) r t
    end.
    oddFromFunc (F X) evF n t.

  Inductive evI : BraunP :=
    | evC : forall n v, fmapP odI n v -> evI n v
  with odI : BraunP :=
    | odC : forall n v, oddFromFunc (F X) evI (* fun _ => fun _ => True *) n v (*(F X) evI n v*) -> odI n v.


    | odnil : forall v, evI nil v -> odI nil (f x)
    | odT : forall r v, 
            evI (true :: r) v -> 
            odI (true :: r) (oddFromEven f (f (f x)) 


(oddFromEven f (f x) v).

  Check evI.

  Lemma eoW : exists e, exists o, forall n, 
    ((exists v, e n = v) /\ (exists w, o n = w)) /\
    eqB e (fmap' f od) /\ odI o.
  Proof.
    eapply ex_intro.
    eapply ex_intro.
    induction n.
    simpl.
    Check x.
    Check (146).
    
    split. Focus 2. intros.
    simpl. eapply ex_intro.
    eapply ex_intro.
    split.
    eapply evC.
    Focus 2.
    eapply odC.

  Fixpoint itod (n : list bool) : A :=
    match n with
      | nil => f x
      | true :: r => oddFromEven f (f (f x)) (fun z => f (itod (false :: z))) r
      | false :: r => fmap' f (odds (fun z => f (itod z))) r
    end.


Fi    oddFromEven f (f x) itev n.xpoint iterate (f : A->A) (x : A) (n : list bool) {struct n} : A :=
match n with
| nil => x
| true :: t => 

  induction H.
  apply extE.
  unfold reco.
  unfold unco.
  simpl.
  induction n.
  simpl. reflexivity.
  simpl. 
  induction a.
  simpl.
  fold unco. fold reco.
  fold unco in IHn. fold reco in IHn.
  unfold unco.
  unfold reco.
  assert (forall n m, unco (reco x) m = x m -> unco (reco x) (n ++ m) = x (n ++ m)).
  induction n.
  auto.
  simpl. auto.
  simpl.
  induction n. simpl. reflexivity.
  


  generalize dependent x.
  generalize dependent y.
  induction n. intros.
  simpl. inversion H. reflexivity. apply H0.
  generalize dependent n.
  induction a.
  intros.
  unfold unco.
  fold unco.
  simpl.
  simpl.
  unfold reco.
  simpl.
  unfold unco. dimpl.
  case a.
  simpl.


Check nil.*)