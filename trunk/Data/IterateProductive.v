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
Require Import BraunFunctions.

Set Implicit Arguments.

Section Single.

Variable (a : Set).
Variable (aeq : relation a).
Variable (aeqEquiv : Equivalence aeq).

Definition braun := braun a.
Definition fraun := fraun a.
Definition coeq := coeq aeq.
Definition exteq := @exteq a aeq a aeq.
Definition fexteq := @BraunStreams.exteq a aeq (list bool) eq.
Definition opaque := @opaque a a aeq aeq.
(*
Variable f : a -> a.
Variable fOpaque : opaque f.
*)
Ltac des :=
  intros; simpl in *;
  match goal with
    | [H:Equivalence ?S |- _] => inversion_clear H; des
    | [a:bool |- _] => destruct a; des
    | [xy : coeq ?x ?y |- _] => inversion_clear xy; auto
    | _ => auto
  end.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Recdef.

Require Import Coq.omega.Omega.

(* A Br n is a Braun stream that is only defined for indices less than n *)

Definition Br (n:list bool) := 
  forall (b:list bool), ord b < ord n -> a.

Require Import Arith.

Hint Rewrite succTisS : bord.

Ltac num :=
  des; autorewrite with bord in *; try omega; auto.
Hint Rewrite tun : bord.

Lemma tun' : forall x, ord (unord x) = x.
Proof.
  intros; apply tun.
Qed.

Hint Rewrite tun' : bord.

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

Program Definition oddsR (n:list bool) (x:Br n) : Br (oddsT n) :=
  fun b p => x (true::b) _.
Next Obligation.
  destruct n.
  simpl in p. inversion p.
  destruct b0; simpl in *; try omega.
  rewrite succTisS in p. omega.
Defined.

Program Definition evensR (n:list bool) (x:Br n) : Br (evensT n) :=
  fun b p => x (false::b) _.
Next Obligation.
  destruct n; num.
Qed.

(* 
oddFromEvenPr' is a Br replacement for the Haskell oddFromEven above.
It is not defined as having the type 

A -> forall n, Br n -> Br (succT n) because it is recursive in a value hidden by the abbreviation Br (succT n).
*)

Program Fixpoint oddFromEvenPr' (f:a->a) (x : a) (n : list bool) (v : Br n)  (b:list bool) (p:ord b < ord (succT n)) {struct b} : a :=
match b with
  | nil => x
  | true :: r => @oddFromEvenPr' f (f (v nil _ )) (evensT n) (evensR v) r _
  | false :: r => f (v (true::r) _)
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

Lemma oddFromEvenPrNil : forall f x n v p,
  @oddFromEvenPr' f x n v nil p = x.
Proof.
  auto.
Defined.

Lemma oddFromEvenPrTrue : forall f x n v r p i j,
    @oddFromEvenPr' f x n v (true::r) p =
    @oddFromEvenPr' f (f (v nil i)) (evensT n) (evensR v) r j.
Proof.
  intros.
  simpl.
  rewrite (le_uniqueness_proof i _).
  rewrite (le_uniqueness_proof j _).
  reflexivity.
Qed.

Lemma oddFromEvenPrFalse : forall f x n v r p i,
    @oddFromEvenPr' f x n v (false::r) p =
    f (v (true::r) i).
Proof.
  intros.
  simpl.
  rewrite (le_uniqueness_proof i _).
  reflexivity.
Qed.

(*
Lemma oddFrom_ind : forall (x : A) (n : list bool) (v : Br n)  (b:list bool), oddFromEvenPr' x n v b = 
match b return (ord b < ord (succT n)) -> A with
  | nil => fun _ => x
  | true :: r => fun p => oddFromEvenPr' (F (v nil (oddFromEvenPr'_obligation_1 x n v b p) )) _ (evensR _ v) r _
  | false :: r => fun p => F (v (true::r) _)
end.
*)

Definition oddFromEvenPr f (x:a) (n:list bool) (v:Br n) : Br (succT n) := oddFromEvenPr' f x v.

Definition toPrime (x:(forall n, Br n)) : fraun.
unfold fraun.
unfold Br.
intros x l.
apply (x (succT l) l).
num.
Defined.

Definition fromPrime (x:fraun) : (forall n, Br n).
unfold fraun.
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
  forall x:fraun,
    let y := toPrime (fromPrime x) in
      forall n,
        aeq (x n) (y n).
Proof.
  intros.
  unfold y; unfold fromPrime; unfold toPrime.
  apply Equivalence_Reflexive.
Qed.

Program Definition oddFrom f x e :=
  toPrime (fun n => 
    match n with 
      | nil => _
      | _ => @oddFromEvenPr f x (predT n) (fromPrime e (predT n))
    end).
Next Obligation.
  unfold Br.
  intros.
  destruct b as [|z b]; simpl in H.
  assert False.
  inversion H.
  inversion H0.
  destruct z; simpl in H.
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

Definition oddFromEven f x e := fraunBraun (oddFrom f x (braunFraun e)).

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
  forall f x y, aeq x y -> 
    forall n p q r, 
      aeq (@oddFromEvenPr' f x n p q r)
      (@oddFromEvenPr' f y n p q r).
Proof.
  intros.
  destruct q.
  auto.
  reflexivity.
Qed.


Lemma oddFromInvariant : 
  forall f g (fOpaque : opaque f) (gOpaque : opaque g)
    (fgeq : exteq f g)    
    n n' (x:Br n) (x':Br n'), 
    (forall z s t, aeq (x z s) (x' z t)) ->
    forall v w (vw:aeq v w) b p p', 
      aeq (@oddFromEvenPr' f v n x b p)
      (@oddFromEvenPr' g w n' x' b p').
Proof.
  intros.
  generalize dependent n;
    generalize dependent n';
      generalize dependent v;
        generalize dependent w.
  induction b as [|z b]; intros.
  simpl. auto.
  destruct z.
  Check oddFromEvenPrTrue.
  assert (ord nil < ord n) as i.
  simpl.
  simpl in p.
  rewrite succTisS in p. omega.
  assert (ord b < ord (succT (evensT n))) as j.
  simpl in p.
  rewrite succTisS in *.
  destruct n as [|z n]; simpl; try (omega); destruct z; simpl in *; try (omega).
  erewrite oddFromEvenPrTrue with (i := i) (j := j).
  assert (ord nil < ord n') as i'.
  simpl.
  simpl in p'.
  rewrite succTisS in p'. omega.
  assert (ord b < ord (succT (evensT n'))) as j'.
  simpl in p'.
  rewrite succTisS in *.
  destruct n' as [|z n']; simpl; try (omega); destruct z; simpl in *; try (omega).
  erewrite oddFromEvenPrTrue with (i := i') (j := j').
  Check oddFrom_morph.
  rewrite oddFrom_morph.
  auto using evensRinvariant.
  apply fgeq; auto. reflexivity.
  assert (ord (true::b) < ord n) as i.
  rewrite succTisS in p; simpl in *. omega.
  erewrite oddFromEvenPrFalse with (i := i).
  assert (ord (true::b) < ord n') as i'.
  rewrite succTisS in p'; simpl in *. omega.
  erewrite oddFromEvenPrFalse with (i := i').
  apply fgeq; auto.
Qed.

Program Definition fmapR f (n:list bool) (x:Br n) : Br n :=
  fun b p => f (x b _).

Lemma fmapInvariant: 
  forall f g (fOpaque : opaque f) (gOpaque : opaque g)
    (fgeq : exteq f g)    
    n n' (x:Br n) (x':Br n'), 
    (forall z s t, aeq (x z s) (x' z t)) ->
    forall m p p', aeq (@fmapR f n x m p) (@fmapR g n' x' m p').
Proof.
  intros.
  unfold fmapR in *.
  auto.
Qed.


Lemma oddFromUnfold : forall f (fOpaque : opaque f) x e b,
  aeq (oddFrom f x e b)
  (match b with
     | nil => x
     | true :: r => @oddFrom f (f (e nil)) (fevens e) r
     | false :: r => f (e (true::r))
   end).
Proof.
  intros.
  generalize dependent x; 
    generalize dependent e.
  induction b as [|z b]; intros; simpl.
  unfold oddFrom; simpl; auto.
  unfold toPrime. simpl. reflexivity.
  destruct z; simpl.
  unfold oddFrom.
  unfold toPrime.
  simpl.
  pose (succT b) as sb; fold sb;
    destruct b as [|z b].
  simpl in sb.
  unfold sb. simpl.
  apply fOpaque.
  unfold fromPrime; simpl.
  reflexivity.
  destruct z. simpl in *.
  apply oddFromInvariant; auto.
  unfold exteq. unfold BraunStreams.exteq.
  intros; apply fOpaque; auto.
  intros.
  apply evensRinvariant.
  intros.
  unfold fromPrime.
  Print evensR.
  unfold evensR.
  unfold fevens.
  reflexivity.
  simpl in *.
  apply fOpaque.
  unfold oddFrom.
  unfold fromPrime.
  unfold fevens.
  unfold evensR.
  reflexivity.
  unfold oddFrom.
  unfold toPrime.
  simpl.
  apply fOpaque.
  unfold fromPrime.
  reflexivity.

  unfold oddFrom.
  simpl.
  unfold toPrime.
  simpl.
  apply fOpaque.
  unfold fromPrime. reflexivity.
Qed.

Lemma allEq :
  forall x y,
    (forall b, aeq (braunFraun x b) (braunFraun y b)) ->
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


Lemma oddFromMorph : 
  forall f g (fOpaque : opaque f) (gOpaque : opaque g)
    (fgeq : exteq f g)
    x y (xy:aeq x y)
    b c (bc:fexteq b c) n,
    aeq (@oddFrom f x b n)
        (@oddFrom g y c n).
Proof.
  intros.
  generalize dependent f;
    generalize dependent g;
      generalize dependent x;
        generalize dependent y;
          generalize dependent b;
            generalize dependent c.
  induction n as [|z n]; intros.
  repeat (rewrite oddFromUnfold; auto); auto.
  destruct z.
  rewrite (oddFromUnfold fOpaque).
  rewrite (oddFromUnfold gOpaque).
  apply IHn; auto.
  unfold fevens.
  unfold fexteq. unfold BraunStreams.exteq.
  intros; subst.
  unfold fexteq in bc.
  unfold BraunStreams.exteq in bc.
  apply bc; auto.
  apply opaqueEq; apply aeqEquiv.
  apply opaqueEq; apply aeqEquiv.
  apply fgeq; auto.
  apply bc; auto.
  apply opaqueEq; apply aeqEquiv.
  apply opaqueEq; apply aeqEquiv.

  rewrite (oddFromUnfold fOpaque).
  rewrite (oddFromUnfold gOpaque).
  apply fgeq; auto.
  apply bc; auto.
  apply opaqueEq; apply aeqEquiv.
  apply opaqueEq; apply aeqEquiv.
Qed.

Lemma oddFromPlug :
  forall f (fOpaque: opaque f) x b,
    match b with
      | bons h od ev => 
        coeq (oddFromEven f x b) 
             (bons x (oddFromEven f (f h) ev) (fmap f od))
    end.
Proof.
  intros.
  destruct b; simpl.
  unfold oddFromEven.
  apply allEq.
  intros.
  destruct b as [|h t].
  simpl.
  rewrite oddFromUnfold; auto.
  reflexivity.
  destruct h; simpl.
  Check braunFraunMorph.
  pose (@braunFraunMorph a aeq) as unco_help.
  unfold BraunStreams.exteq in unco_help; auto.
  apply unco_help.
  pose (@fraunBraunMorph a aeq) as reco_help.
  apply reco_help; auto.
  unfold BraunStreams.exteq.

  intros; subst.
  rewrite oddFromUnfold. simpl.
  unfold fevens. simpl.
  rewrite oddFromMorph.
  reflexivity.  auto. auto.
  unfold exteq.
  unfold BraunStreams.exteq; intros.
  apply fOpaque; auto.
  reflexivity.
  unfold fexteq. unfold BraunStreams.exteq. intros. subst. reflexivity.
  auto. auto.
  apply opaqueEq. apply aeqEquiv.
  apply opaqueEq. apply aeqEquiv.

  pose (@braunFraunMorph a aeq) as unco_help.
  unfold BraunStreams.exteq in unco_help.
  apply unco_help.
  eapply Equivalence_Transitive with (y := fraunBraun (fun z => f (braunFraun (bons a0 b1 b2) (true :: z)))).
  apply fraunBraunMorph. apply aeqEquiv.
  unfold BraunStreams.exteq.
  intros. subst.
  apply oddFromUnfold; auto.
  simpl.
  apply allEq.
  intros.
  clear unco_help.
  generalize dependent b1.
  induction b.
  simpl.
  destruct b1; simpl. reflexivity.
  destruct a1.
  simpl.
  intros.
  destruct b1. 
  apply IHb.
  intros.
  simpl.
  destruct b1.
  apply IHb. reflexivity.
  apply opaqueEq.
  apply aeqEquiv.
  apply opaqueEq.
  apply aeqEquiv.
Qed.

Lemma oddFromEvenUnfold : 
  forall f (fOpaque : opaque f) (x : a) (b : braun),
    coeq (oddFromEven f x b)
         (bons x
           (oddFromEven f (f (bead b)) (bevens b))
           (fmap f (bodds b))).
Proof.
  intros; destruct b.
  simpl.
  pose (oddFromPlug fOpaque x (bons a0 b1 b2)) as oo.
  simpl in oo.
  apply oo.
Qed.

Lemma oddFromEvenInvariant : 
  forall f g (fOpaque : opaque f) (gOpaque : opaque g)
    (fgeq : exteq f g)    
    v w (vw:aeq v w) 
    p q (pq:coeq p q),
      coeq (oddFromEven f v p)
           (oddFromEven g w q).
Proof.

  intros.
  apply batCoeq.
  intros.
  generalize dependent f;
    generalize dependent g;
      generalize dependent v;
        generalize dependent w;
          generalize dependent p;
            generalize dependent q.
  induction b as [|z b]; intros.
  simpl.
  repeat (rewrite oddFromUnfold; auto).
  destruct z.
  transitivity (bat (oddFromEven f (f (bead p)) (bevens p)) b).
  transitivity (bat (bodds (oddFromEven f v p)) b).
  remember (oddFromEven f v p) as ofvp;
    destruct ofvp; simpl.
  reflexivity.
  apply batMorph with (aeq := aeq); auto.
  transitivity (bodds
    (bons v
      (oddFromEven f (f (bead p)) (bevens p))
      (fmap f (bodds p)))).
  apply oddsMorph.
  apply oddFromEvenUnfold; auto.
  simpl. reflexivity.
  transitivity (bat (oddFromEven g (g (bead q)) (bevens q)) b).
  apply IHb; auto. 
  destruct pq; simpl; auto.
  destruct pq; simpl; auto.
  transitivity (bat (bodds (oddFromEven g w q)) b).
  apply batMorph with (aeq := aeq); auto.
  transitivity (bodds
    (bons w
      (oddFromEven g (g (bead q)) (bevens q))
      (fmap g (bodds q)))).
  simpl; reflexivity.
  apply oddsMorph.
  symmetry.
  apply oddFromEvenUnfold; auto.
  remember (oddFromEven g w q) as ogwq;
    destruct ogwq; simpl.
  reflexivity.

  transitivity (bat (fmap f (bodds p)) b).
  transitivity (bat (bevens (oddFromEven f v p)) b).
  remember (oddFromEven f v p) as ofvp;
    destruct ofvp; simpl.
  reflexivity.
  apply batMorph with (aeq := aeq); auto.
  transitivity (bevens
    (bons v
      (oddFromEven f (f (bead p)) (bevens p))
      (fmap f (bodds p)))).
  apply evensMorph.
  apply oddFromEvenUnfold; auto.
  simpl. reflexivity.
  transitivity (bat (fmap g (bodds q)) b).
  apply batMorph with (aeq := aeq); auto.
  apply fmapMorph; auto.
  apply oddsMorph. auto.
  transitivity (bat (bevens (oddFromEven g w q)) b).
  apply batMorph with (aeq := aeq); auto.
  transitivity (bevens
    (bons w
      (oddFromEven g (g (bead q)) (bevens q))
      (fmap g (bodds q)))).
  simpl; reflexivity.
  apply evensMorph.
  symmetry.
  apply oddFromEvenUnfold; auto.
  remember (oddFromEven g w q) as ogwq;
    destruct ogwq; simpl.
  reflexivity.
Qed.

Definition evenR' f (n:list bool) (od:Br n) : Br n := fmapR f od.

Lemma obl : forall b, ord b < ord (succT b).
Proof.
  num.
Defined.

Lemma oddRhelp : forall n b (p:ord b < ord n), ord b < ord (succT n).
Proof.
  num.
Qed.

(*
Program Fixpoint oddR (X:A) (n:list bool) (b:list bool) (p:ord b < ord n) {measure ord n} : A :=
  let er := @evenR' n (@oddR _) in
    @oddFromEvenPr (F X) n er b (@oddRhelp n b p).
Next Obligation.
  apply obl.
Defined.
*)
(*
Function oddR (X:A) (n:list bool) (b:list bool) (p:ord b < ord n) {measure ord n} : A := @oddFromEvenPr (F X) b (evenR' (oddR X b)) b (obl b).
(*Error: find_call_occs : Lambda*)
(* Error: Unable to find an instance for the variables b, p.*)
*)


Program Fixpoint oddR f (X:a) (n:list bool) {measure ord n} : Br n :=
  fun b p => 
    let er := evenR' f (oddR b) in
      @oddFromEvenPr f (f X) b er b _.
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
  forall f (fOpaque : opaque f) X n b p, 
    exists q,
      aeq 
      (@oddR f X n b p)
      (@oddFromEvenPr f (f X) _ (evenR' f (@oddR f X b)) b q).
Proof.
  intros.
  assert (ord b < ord (succT b)) as q.
  num.
  exists q.
  remember (ord n) as nn in |- *.
  generalize dependent b.
  generalize dependent n.
  induction nn; intros.
  induction n.
  simpl in p; induction b; simpl in p; inversion p.
  destruct a0; simpl in *; inversion Heqnn.

  unfold oddR at 1.
  Check Fix_measure_sub.
  Print Fix_measure_sub.
  pose (fun (n0 : list bool)
           (oddR0 : forall n' : {n' : list bool | ord n' < ord n0},
                    Br (proj1_sig n')) (b0 : list bool)
           (p0 : ord b0 < ord n0) =>
         let er :=
           evenR' f
             (oddR0
                (exist (fun n' : list bool => ord n' < ord n0) b0
                   (oddR_obligation_1 f X n0 oddR0 b0 p0))) in
         oddFromEvenPr f (f X) er b0 (oddR_obligation_2 f X n0 oddR0 b0 p0))
  as I.
  fold I.
  unfold Fix_measure_sub.
  rewrite F_unfold.
  apply oddFromInvariant; auto.
  unfold exteq; unfold BraunStreams.exteq; intros; apply fOpaque; auto.
  intros.
  unfold evenR'.
  apply fmapInvariant; auto.
  unfold exteq; unfold BraunStreams.exteq; intros; apply fOpaque; auto.
  intros.
  simpl in s0.
  fold I.
  unfold oddR.
  unfold Fix_measure_sub.
  unfold evenR'.
(*
  Check oddFromInvariant.
  Check Fix_measure_F_sub.
  Check (lt_wf (ord b)).
  Check Fix_measure_F_inv.
  *)
  erewrite Fix_measure_F_inv with (m := (fun n0 : list bool => ord n0)) (s := (lt_wf ((fun n0 : list bool => ord n0) b))).
  unfold proj1_sig.
(*
  Print Equivalence.
  Check Equivalence_Reflexive.
  Print Reflexive.
  Print Acc.
  Locate "_ < _".
*)
  unfold lt in s0, t0.
  rewrite (le_uniqueness_proof s0 t0).
  apply Equivalence_Reflexive. reflexivity.
Qed.

Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.

Lemma oddRInvariant : 
  forall f g (fOpaque : opaque f) (gOpaque : opaque g)(fg:exteq f g) 
    X Y (XY:aeq X Y) n n' b p q, 
    aeq (@oddR f X n b p)
        (@oddR g Y n' b q).
Proof.
  Check (@well_founded_ind nat lt lt_wf).
  intros.
  remember (ord n) as nn in |- *.
  generalize dependent b.
  generalize dependent n.
  generalize dependent n'.
  generalize dependent X.
  generalize dependent Y.
  generalize dependent nn.
  pose (fun (nn : nat) => forall (Y X : a) ,
    aeq X Y -> forall (n' n : list bool),
   nn = ord n ->
   forall (b : list bool) (p : ord b < ord n) (q : ord b < ord n'),
   aeq (oddR f X n b p) (oddR g Y n' b q)) as P.
  apply (@well_founded_ind nat lt lt_wf P).
  unfold P in *; clear P.
  intros.
  assert (exists r,
    aeq 
    (@oddR f X n b p)
    (@oddFromEvenPr f (f X) _ (evenR' f (@oddR f X b)) b r)) as J.
  apply oddRoddFrom; auto.
  destruct J.
  assert (exists s,
    aeq 
    (@oddR g Y n' b q)
    (@oddFromEvenPr g (g Y) _ (evenR' g (@oddR g Y b)) b s)) as I.
  apply oddRoddFrom; auto.
  destruct I.
  eapply Equivalence_Symmetric in H3.
  assert (aeq 
    (oddFromEvenPr f (f X) (evenR' f (oddR f X b)) b x0)
    (oddFromEvenPr g (g Y) (evenR' g (oddR g Y b)) b x1)).
  apply oddFromInvariant; auto.
  intros.
  unfold evenR'.
  apply fmapInvariant; auto.
  intros.
  eapply H. subst. apply p. auto. auto.
  eapply Equivalence_Transitive.
  apply H2.
  eapply Equivalence_Transitive.
  apply H4.
  auto.
Qed.

Definition evenR f X (n:list bool) : Br n := evenR' f (oddR f X n).

Require Import Recdef.

(*BUG*)
(*
Function oddR (n:list bool) (b:list bool) (p:ord b < ord n) {measure ord n} : A := oddFromEvenPr (F X) b (evenR' b (oddR b)) b (obl b).
*)
(* Error: Unable to find an instance for the variables b, p.*)
(*
Function oddR (n:list bool) {measure ord n} : Br n :=
  fun b p => oddFromEvenPr (F X) b (evenR' b (oddR b)) b (obl b).
*)
(*Error: find_call_occs : Lambda*)

End Single.
