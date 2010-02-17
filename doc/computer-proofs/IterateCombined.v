Require Import IterateCorrect.
Require Import IterateProductive.
Require Import BraunStreams.

Section Single.

Variable (a : Set).
Variable (aeq : relation a).
Variable (aeqEquiv : Equivalence aeq).


Check IterateCorrect.iter.
Print Z.
Check opaque.

Definition combiner :=
  (fun (f:a->a) (fOpaque:@opaque a a aeq aeq f) =>
    @IterateCorrect.iter a aeq aeqEquiv
    (@oddFromEven a aeq aeqEquiv)
    (fun g x b og => @oddFromEvenUnfold a aeq aeqEquiv g og x b)
    (fun f g x y v w fo go fg xy vw =>
      @oddFromEvenInvariant a aeq aeqEquiv f g fo go fg x y xy v w vw)
    (@bodd a aeq aeqEquiv)
    (@beven a aeq aeqEquiv)
    (@boddUnfold a aeq aeqEquiv)
    (@bevenUnfold a aeq aeqEquiv)).

Lemma iterateCorrect : 
  forall f x b,
    opaque aeq aeq f ->
    aeq
    (bat (iterate (bodd aeqEquiv) (beven aeqEquiv) f x) b) 
    (applyn (ord b) f x).
Proof.
  intros.
  pose combiner as c.
  simpl in c.
  eapply c; auto.
  apply X.
Qed.

End Single.