(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)


(*************************************************)
(*      Environment for Linear Logic             *)
(*************************************************)
Class LEnv := {
  LWeight : Type;
  LWeightPlus : LWeight -> LWeight -> LWeight;
  LWeightZero : LWeight;
  LWeightPlusAssoc a b c :
    LWeightPlus a (LWeightPlus b c) = LWeightPlus (LWeightPlus a b) c;
  LWeightZeroL a : LWeightPlus a LWeightZero = a;
  LWeightZeroR a : LWeightPlus LWeightZero a = a;
  LWeightPlusComm a b : LWeightPlus a b = LWeightPlus b a
}.

Delimit Scope LWeight_scope with LWeight.
Notation "a + b" := (LWeightPlus a b) : LWeight_scope.
Notation "0" := LWeightZero : LWeight_scope.


(*************************************************)
(* Auto-derivation rules for proposition weights *)
(*************************************************)
Class LWeightMinus{E:LEnv} (W V X:LWeight) := {
  lweightminus_eqn : (V + X = W)%LWeight
}.
Arguments LWeightMinus [E] W%LWeight V%LWeight X%LWeight.
Arguments Build_LWeightMinus [E] [W] [V] [X] _.
Arguments lweightminus_eqn [E] [W] [V] [X] [_].
Class LWeightMinus1{E:LEnv} (W V X:LWeight) := {
  lweightminus1_eqn : (V + X = W)%LWeight
}.
Arguments LWeightMinus1 [E] W%LWeight V%LWeight X%LWeight.
Arguments Build_LWeightMinus1 [E] [W] [V] [X] _.
Arguments lweightminus1_eqn [E] [W] [V] [X] [_].
Class LWeightAnnihil{E:LEnv} (W:LWeight) := {
  lweightannihil_eqn : (W = 0)%LWeight
}.
Arguments LWeightAnnihil [E] W%LWeight.
Arguments Build_LWeightAnnihil [E] [W] _.
Arguments lweightannihil_eqn [E] [W] [_].

Class LWeightCastPlus{E:LEnv} (W V X:LWeight) := {
  lweightcastplus_eqn : (V + X = W)%LWeight
}.
Arguments LWeightCastPlus [E] W%LWeight V%LWeight X%LWeight.
Arguments Build_LWeightCastPlus [E] [W] [V] [X] _.
Arguments lweightcastplus_eqn [E] [W] [V] [X] [_].
Class LWeightCastZero{E:LEnv} (W:LWeight) := {
  lweightcastzero_eqn : (0 = W)%LWeight
}.
Arguments LWeightCastZero [E] W%LWeight.
Arguments Build_LWeightCastZero [E] [W] _.
Arguments lweightcastzero_eqn [E] [W] [_].

Instance LWeightCastPlus_self{E:LEnv} (V X:LWeight)
    : LWeightCastPlus (V + X)%LWeight V X := {|
  lweightcastplus_eqn := eq_refl
|}.
Instance LWeightCastZero_self{E:LEnv}
    : LWeightCastZero 0%LWeight := {|
  lweightcastzero_eqn := eq_refl
|}.

Instance LWeightMinus_VPlus{E:LEnv} {W W' X V V0 V1:LWeight}
    {H:LWeightCastPlus V V0 V1}
    {H0:LWeightMinus W V0 W'} {H1:LWeightMinus W' V1 X}
    : LWeightMinus W V X | 0.
Proof.
  rewrite <-(@lweightcastplus_eqn _ _ _ _ H).
  exists.
  rewrite <-LWeightPlusAssoc.
  rewrite (@lweightminus_eqn _ _ _ _ H1).
  apply (@lweightminus_eqn _ _ _ _ H0).
Defined.
Instance LWeightMinus_VZero{E:LEnv} {W V:LWeight}
    {H:LWeightCastZero V}
    : LWeightMinus W V W | 0.
Proof.
  rewrite <-(@lweightcastzero_eqn _ _ H).
  exists.
  apply LWeightZeroR.
Defined.
Instance LWeightMinus_Promote{E:LEnv} {W V X:LWeight}
    {H:LWeightMinus1 W V X}
    : LWeightMinus W V X | 1.
Proof.
  exists.
  apply lweightminus1_eqn.
Defined.

Instance LWeightMinus1_WPlusL{E:LEnv} {W V X W0 W1:LWeight}
    {H:LWeightCastPlus W W0 W1}
    {H0:LWeightMinus1 W0 V X}
    : LWeightMinus1 W V (X + W1) | 0.
Proof.
  rewrite <-(@lweightcastplus_eqn _ _ _ _ H).
  exists.
  rewrite LWeightPlusAssoc.
  f_equal.
  apply (@lweightminus1_eqn _ _ _ _ H0).
Defined.
Instance LWeightMinus1_WPlusR{E:LEnv} {W V X W0 W1:LWeight}
    {H:LWeightCastPlus W W0 W1}
    {H1:LWeightMinus1 W1 V X}
    : LWeightMinus1 W V (W0 + X) | 0.
Proof.
  rewrite <-(@lweightcastplus_eqn _ _ _ _ H).
  exists.
  rewrite (LWeightPlusComm V).
  rewrite <-LWeightPlusAssoc.
  f_equal.
  rewrite LWeightPlusComm.
  apply (@lweightminus1_eqn _ _ _ _ H1).
Defined.
Instance LWeightMinus1_self{E:LEnv} {W:LWeight}
    : LWeightMinus1 W W 0 | 0.
Proof.
  exists.
  apply LWeightZeroL.
Defined.

Instance LWeightAnnihil_plus{E:LEnv} {W W0 W1:LWeight}
    {H:LWeightCastPlus W W0 W1}
    {H0:LWeightAnnihil W0}
    {H1:LWeightAnnihil W1}
    : LWeightAnnihil W | 0.
Proof.
  rewrite <-lweightcastplus_eqn.
  exists.
  rewrite (@lweightannihil_eqn _ _ H0).
  rewrite (@lweightannihil_eqn _ _ H1).
  apply LWeightZeroL.
Defined.
Instance LWeightAnnihil_self{E:LEnv} {W:LWeight}
    {H:LWeightCastZero W}
    : LWeightAnnihil W | 0.
Proof.
  exists.
  symmetry; apply lweightcastzero_eqn.
Defined.

Lemma test{E:LEnv} : forall(a b c d:LWeight),
  exists e, ((c + a) + e = a + b + c)%LWeight.
Proof.
  intros a b c d.
  eexists.
  apply lweightminus_eqn.
Qed.




(*************************************************)
(*        Definition of Linear Type              *)
(*************************************************)

Delimit Scope ILL_scope with ILL.
Reserved Notation "'TT'".
Reserved Notation "A '-o' B"
  (at level 99, right associativity, y at level 200).

Record LType{E:LEnv} := {
  ltype : Type;
  lweight : ltype -> @LWeight E
}.
Arguments LType [E].
Arguments Build_LType [E] _ _.
Arguments ltype [E] _%ILL.
Arguments lweight [E] [_] _.
(* Linear Implication *)
Record LFun{E:LEnv} (A B:LType) := {
  lfun_val : ltype A -> ltype B;
  lfun_weight : @LWeight E;
  lfun_weight_eqn :
    forall x, (lfun_weight + lweight x = lweight (lfun_val x))%LWeight
}.
Arguments LFun [E] A B.
Arguments Build_LFun [E] [A] [B] _ _ _.
Arguments lfun_val [E] [A] [B] _ _.
Arguments lfun_weight [E] [A] [B] _.
Arguments lfun_weight_eqn [E] [A] [B] _ _.

Definition LImpl{E:LEnv} (A B:LType):LType := {|
  ltype := LFun A B;
  lweight := @lfun_weight _ _ _
|}.
Notation "A -o B" := (LImpl A%ILL B%ILL) : ILL_scope.

Instance LImpl_weight_decompose{E:LEnv} (A B:LType)
    (f : ltype (A -o B)) (x : ltype A)
    : LWeightCastPlus (lweight (lfun_val f x)) (lweight f) (lweight x).
Proof.
  rewrite <-lfun_weight_eqn.
  auto with typeclass_instances.
Defined.

Record LGoal{E:LEnv} (T:LType) (W:LWeight) : Type := {
  lgoal_proof : ltype T;
  lgoal_weight : W = lweight lgoal_proof
}.
Arguments LGoal [E] T%ILL W%LWeight.
Arguments Build_LGoal [E] [T] [W] _ _.
Arguments lgoal_proof [E] [T] [W] _.
Arguments lgoal_weight [E] [T] [W] _.

Notation "T [ 'using_hypotheses' W ]" :=
  (LGoal T%ILL W%LWeight)
  (at level 100,
   no associativity,
   format "'[' T '//' [ 'using_hypotheses'  W ] ']'").

Ltac ll_cleanhypotheses :=
  repeat match goal with
  | [ x : ltype _ |- _ ] => clear x
  end.

Definition limpl_intro{E:LEnv} (A B:LType) (W:LWeight)
    (X : forall a : ltype A, LGoal B (W + lweight a)) :
    LGoal (A -o B) W := {|
  lgoal_proof := {|
    lfun_val a := lgoal_proof (X a);
    lfun_weight := W;
    lfun_weight_eqn a := lgoal_weight (X a)
  |} : ltype (A -o B);
  lgoal_weight := eq_refl
|}.

Ltac introll x :=
  apply limpl_intro; intros x;
  rewrite ?LWeightZeroL, ?LWeightZeroR;
  ll_cleanhypotheses.

Definition limpl_applygoal{E:LEnv} (A B:LType) (W:LWeight)
    (x:ltype (A -o B)) {X:LWeight} {mn:LWeightMinus W (lweight x) X} :
    LGoal A X -> LGoal B W.
Proof.
  intros a.
  refine {|
    lgoal_proof := lfun_val x (lgoal_proof a)
  |}.
  etransitivity; [|apply lfun_weight_eqn].
  etransitivity; [symmetry; apply lweightminus_eqn|].
  f_equal.
  apply lgoal_weight.
Defined.

Ltac applyll x :=
  apply (limpl_applygoal _ _ _ x); simpl;
  rewrite ?LWeightZeroL, ?LWeightZeroR;
  ll_cleanhypotheses.

Definition linear_exact{E:LEnv} (A:LType) (W:LWeight)
    (x:ltype A) {X:LWeight} {mn:LWeightMinus W (lweight x) X}
    {ann:LWeightAnnihil X} : LGoal A W.
Proof.
  refine {|
    lgoal_proof := x
  |}.
  etransitivity; [symmetry; apply lweightminus_eqn|].
  rewrite (@lweightannihil_eqn _ _ ann).
  apply LWeightZeroL.
Defined.

Ltac exactll x := apply (linear_exact _ _ x).

Lemma CombinatorB{E:LEnv} (A B C:LType) :
  (B -o C) -o (A -o B) -o (A -o C)
  [using_hypotheses 0].
Proof.
  introll x.
  introll y.
  introll z.
  applyll x.
  applyll y.
  exactll z.
Qed.

Lemma CombinatorC{E:LEnv} (A B C:LType) :
  (A -o B -o C) -o (B -o A -o C)
  [using_hypotheses 0].
Proof.
  introll x.
  introll y.
  introll z.
  applyll (lfun_val x z).
  exactll y.
Qed.
