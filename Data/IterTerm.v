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

Set Implicit Arguments.
(*Set Contextual Implicit.*)
(*Unset Strict Implicit. *)
(*Set Reversible Pattern Implicit. *)

Section Single.

Variable (A : Set).
Variable (Aeq : relation A).
Variable (Aeq_equiv : Equivalence Aeq).
Variable F : A -> A.
Variable F_morph : forall x y, Aeq x y -> Aeq (F x) (F y).

CoInductive Braun : Set :=
| Cons : A -> Braun -> Braun -> Braun.

(* Bisimilarity is the equivalence relation we will want on Braun streams *)

CoInductive coeq : Braun -> Braun -> Prop :=
| co : forall x y od od' ev ev', 
        Aeq x y -> coeq od od' -> coeq ev ev' 
        -> coeq (Cons x od ev) (Cons y od' ev').

Lemma coeq_refl : forall x, coeq x x.
Proof.
  cofix.
  destruct x. 
  constructor.
  setoid_reflexivity.
  apply coeq_refl.
  apply coeq_refl.
Qed.

Lemma coeq_symm : forall x y, coeq x y -> coeq y x.
Proof.
  cofix.
  intros x y coeq_x_y.
  destruct coeq_x_y.
  constructor. 
  setoid_symmetry. assumption.
  apply coeq_symm. assumption.
  apply coeq_symm. assumption.
Qed.

Lemma coeq_trans : forall x y z , coeq x y -> coeq y z -> coeq x z.
Proof.
  cofix.
  intros x y z coeq_x_y coeq_y_z.
  inversion coeq_x_y as [xh  yh xod  yod xev  yev].
  inversion coeq_y_z as [yh' zh yod' zod yev' zev yzh yzod yzev yy].
  subst.
  inversion yy. subst. clear yy.
  constructor.
  setoid_transitivity yh; assumption.
  apply coeq_trans with yod; assumption.
  apply coeq_trans with yev; assumption.
Qed.

Add Parametric Relation : Braun coeq
reflexivity proved by coeq_refl
symmetry proved by coeq_symm
transitivity proved by coeq_trans
as coeq_equiv.

(* An equivalent definition of Braun streams: *)

Definition Braun' := list bool -> A.

(* Extensional function quality is an equivalence relation: *)

Section Double.

Variable (B:Set).

Definition exteq (f:B -> A) (g:B -> A) := forall x, Aeq (f x) (g x).

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
  assert (forall n x y, coeq x y -> Aeq (unco x n) (unco y n)).
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
  assert (forall n x y, exteq x y -> Aeq (unco (reco x) n) (y n)).
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

Lemma oddFromEvenPrNil : forall x n v p,
  @oddFromEvenPr' x n v nil p = x.
Proof.
  auto.
Defined.

Lemma oddFromEvenPrTrue : forall x n v r p,
  exists i, exists j,
    @oddFromEvenPr' x n v (true::r) p =
    @oddFromEvenPr' (F (v nil i)) (evensT n) (evensR v) r j.
Proof.
  intros.
  Locate " exists _ , _ ".
  Print ex.
  eapply ex_intro.
  eapply ex_intro.
  reflexivity.
Defined.

Lemma oddFromEvenPrFalse : forall x n v r p,
  exists i,
    @oddFromEvenPr' x n v (false::r) p =
    F (v (true::r) i).
Proof.
  intros.
  Locate " exists _ , _ ".
  Print ex.
  eapply ex_intro.
  reflexivity.
Defined.

(*
Lemma oddFrom_ind : forall (x : A) (n : list bool) (v : Br n)  (b:list bool), oddFromEvenPr' x n v b = 
match b return (bOrd b < bOrd (succT n)) -> A with
  | nil => fun _ => x
  | true :: r => fun p => oddFromEvenPr' (F (v nil (oddFromEvenPr'_obligation_1 x n v b p) )) _ (evensR _ v) r _
  | false :: r => fun p => F (v (true::r) _)
end.
*)

Definition oddFromEvenPr (x:A) (n:list bool) (v:Br n) : Br (succT n) := oddFromEvenPr' x v.
(*
Definition invariant (x:forall n, Br n) := 
  forall b, (forall n p n' p', Aeq (x n b p) (x n' b p')).

Check evensR.

Hint Unfold invariant.
*)
Hint Unfold evensR.

Check evensR.

Lemma evensRinvariant: 
  forall n n' (x:Br n) (x':Br n'), 
    (forall z s t, Aeq (x z s) (x' z t)) ->
    forall m p p', Aeq (@evensR n x m p) (@evensR n' x' m p').
Proof.
  intros.
  unfold evensR in *.
  auto.
Defined.

Lemma oddsRinvariant: 
  forall n n' (x:Br n) (x':Br n'), 
    (forall z s t, Aeq (x z s) (x' z t)) ->
    forall m p p', Aeq (@oddsR n x m p) (@oddsR n' x' m p').
Proof.
  intros.
  unfold oddsR in *.
  auto.
Defined.

Lemma oddFromInvariant : 
  forall n n' (x:Br n) (x':Br n'), 
    (forall z s t, Aeq (x z s) (x' z t)) ->
    forall v  b p p', 
      Aeq (@oddFromEvenPr' v n x b p)
      (@oddFromEvenPr' v n' x' b p').
Proof.
  assert 
    (forall b, 
      forall n n' (x:Br n) (x':Br n'), 
        (forall z s t, Aeq (x z s) (x' z t)) ->
        forall v p p', 
          Aeq (@oddFromEvenPr' v n x b p)
          (@oddFromEvenPr' v n' x' b p')).
  induction b; intros.
  reflexivity.
  destruct a.
  destruct (oddFromEvenPrTrue v x p) as [? truep].
  destruct truep as [? truep].
  rewrite truep.
  destruct (oddFromEvenPrTrue v x' p') as [? truep'].
  destruct truep' as [? truep'].
  rewrite truep'.
  rewrite IHb.

  Lemma oddFrom_morph :
    forall x y, Aeq x y -> 
      forall n p q r, 
        Aeq (@oddFromEvenPr' x n p q r)
            (@oddFromEvenPr' y n p q r).
  Proof.
    intros.
    destruct q.
    auto.
    reflexivity.
  Qed.

  rewrite oddFrom_morph.
  reflexivity.
  auto using F_morph.
  auto using evensRinvariant.

  destruct (oddFromEvenPrFalse v x p) as [? falsep].
  rewrite falsep.
  destruct (oddFromEvenPrFalse v x' p') as [? falsep'].
  rewrite falsep'.
  auto using F_morph.
  auto.
Qed.

Program Definition fmapR (n:list bool) (x:Br n) : Br n :=
  fun b p => F (x b _).

Lemma fmapInvariant: 
  forall n n' (x:Br n) (x':Br n'), 
    (forall z s t, Aeq (x z s) (x' z t)) ->
    forall m p p', Aeq (@fmapR n x m p) (@fmapR n' x' m p').
Proof.
  intros.
  unfold fmapR in *.
  auto.
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



Lemma oddRoddFrom : 
  forall X n b p, 
    exists q,
      Aeq 
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
  erewrite Fix_measure_F_inv.
  unfold proj1_sig.
  Print Equivalence.
  Check Equivalence_Reflexive.
  apply Equivalence_Reflexive.

  eapply Equivalence_Reflexive.

  unfold proj1_sig at 1.

. simpl.

  rewrite Fix_measure_F_eq.

  erewrite Fix_measure_F_inv.
  rewrite 
  apply Equivalence_Reflexive.
  Print Equivalence.
  Check (fun A => @Equivalence A).
  Check 
  auto.

  unfold oddR at 1 in IHnn.
  unfold Fix_measure_sub in IHnn.
  rewrite F_unfold in IHnn.




  simpl in I.

  unfold fmapR.
  apply F_morph.
  fold (Fix_measure_sub _ _).
  apply evensRinvariant.
  fold Fix_measure_sub.
  f_equal.
  f_equal.
  
  simpl

  unfold Fix_measure_sub.
  unfold Fix_measure_F_sub.
  intros  
Abort.
(*
  intros.
  eapply ex_intro.
  unfold oddR at 1.
  unfold Fix_measure_sub.
  rewrite F_unfold.
  apply oddFromInvariant.
  intros.
  unfold evenR'.
  unfold fmapR.
  apply F_morph.
  unfold oddR at 1.
Abort.
*)
(*
  reflexivity.
  unfold Fix_measure_sub.
  simpl.
  reflexivity.
  rewrite <- Fix_measure_F_eq.
  Require Import Program.Wf.WfExtensionality.
  unfold_sub.
  unfold Fix_measure_sub at 1.
  unfold Fix_measure_F_sub at 1.
  simpl.
  apply oddFromInvariant.
  intros.
  unfold evenR'.
  unfold fmapR.
  apply F_morph.
  simpl.
  fold oddR. fold evenR'. 
  simpl. auto. eauto.
  eapply Equivalence_Reflexive.
  reflexivity.
  unfold evenR'.
  simpl.
  unfold fmapR. simpl.
  reflexivity.
Abort.
*)

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