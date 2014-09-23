(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)

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


Class WeightEliminable1{E:LEnv} (W:LWeight) (V:LWeight) := {
  WE_remain : LWeight;
  WE_eqn : (V + WE_remain = W)%LWeight
}.

Instance WE_id{E:LEnv} W : WeightEliminable1 W W := {|
  WE_remain := 0%LWeight;
  WE_eqn := LWeightZeroL _
|}.
Instance WE_plus_l{E:LEnv} W0 W1 V
  (H : WeightEliminable1 W0 V) : WeightEliminable1 (W0 + W1)%LWeight V := {|
  WE_remain := (WE_remain + W1)%LWeight
|}.
Proof.
  rewrite LWeightPlusAssoc.
  f_equal.
  apply WE_eqn.
Defined.
Instance WE_plus_r{E:LEnv} W0 W1 V
  (H : WeightEliminable1 W1 V) : WeightEliminable1 (W0 + W1)%LWeight V := {|
  WE_remain := (W0 + WE_remain)%LWeight
|}.
Proof.
  rewrite (LWeightPlusComm V).
  rewrite <-LWeightPlusAssoc.
  f_equal.
  rewrite LWeightPlusComm.
  apply WE_eqn.
Defined.

Class WeightEliminable2{E:LEnv} (W:LWeight) (V:LWeight) := {
  WE_remain2 : LWeight;
  WE_eqn2 : (V + WE_remain2 = W)%LWeight
}.

Instance WE2_from1{E:LEnv} W V
  (H : WeightEliminable1 W V) : WeightEliminable2 W V := {|
  WE_remain2 := WE_remain;
  WE_eqn2 := WE_eqn
|}.
Instance WE2_zero{E:LEnv} W : WeightEliminable2 W 0%LWeight := {|
  WE_remain2 := W;
  WE_eqn2 := LWeightZeroR _
|}.
Instance WE2_plus{E:LEnv} W V0 V1
  (H0 : WeightEliminable2 W V0)
  (H1 : WeightEliminable2 (@WE_remain2 _ _ _ H0) V1)
  : WeightEliminable2 W (V0 + V1)%LWeight := {|
  WE_remain2 := @WE_remain2 _ _ _ H1
|}.
Proof.
  rewrite <-LWeightPlusAssoc.
  rewrite WE_eqn2.
  apply WE_eqn2.
Defined.

Lemma WE_eliminate1{E:LEnv} {W0 W1 V}
  {H0 : WeightEliminable1 W0 V}
  {H1 : WeightEliminable1 W1 V} :
    @WE_remain _ _ _ H0 = @WE_remain _ _ _ H1 -> W0 = W1.
Proof.
  intros H.
  rewrite <-(@WE_eqn _ _ _ H0).
  rewrite <-(@WE_eqn _ _ _ H1).
  f_equal.
  apply H.
Qed.

Class WeightAnnihilated{E:LEnv} (W:LWeight) := {
  WA_eqn : (0 = W)%LWeight
}.

Instance WA_zero{E:LEnv} : WeightAnnihilated 0%LWeight := {|
  WA_eqn := eq_refl
|}.
Instance WA_plus{E:LEnv} (W0 W1:LWeight)
  (H0 : WeightAnnihilated W0)
  (H1 : WeightAnnihilated W1) : WeightAnnihilated (W0 + W1)%LWeight := {|
|}.
Proof.
  rewrite <-(@WA_eqn _ _ H0).
  rewrite <-(@WA_eqn _ _ H1).
  rewrite LWeightZeroL.
  reflexivity.
Defined.

Ltac elimweight_once := progress (
  apply WE_eliminate1; simpl;
  rewrite ?LWeightZeroL, ?LWeightZeroR).

Ltac elimweight := repeat elimweight_once.



Record LType{E:LEnv} := {
  ltype : Type;
  lweight : ltype -> @LWeight E
}.
Arguments LType [E].
Arguments Build_LType [E] _ _.
Arguments ltype [E] _.
Arguments lweight [E] [_] _.

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

Record LGoal{E:LEnv} (T:LType) (W:LWeight) : Type := {
  lgoal_proof : ltype T;
  lgoal_weight : W = lweight lgoal_proof
}.
Arguments LGoal [E] T W.
Arguments Build_LGoal [E] [T] [W] _ _.
Arguments lgoal_proof [E] [T] [W] _.
Arguments lgoal_weight [E] [T] [W] _.

Notation "T [ 'using_hypotheses' W ]" :=
  (LGoal T W%LWeight)
  (at level 200,
   no associativity,
   format "'[' T '//' [ 'using_hypotheses'  W ] ']'").

Ltac ll_cleanhypotheses :=
  repeat match goal with
  | [ x : ltype _ |- _ ] => clear x
  end.

Definition limpl_intro{E:LEnv} (A B:LType) (W:LWeight)
    (X : forall a : ltype A, LGoal B (W + lweight a)%LWeight) :
    LGoal (LImpl A B) W := {|
  lgoal_proof := {|
    lfun_val a := lgoal_proof (X a);
    lfun_weight := W;
    lfun_weight_eqn a := lgoal_weight (X a)
  |} : ltype (LImpl A B);
  lgoal_weight := eq_refl
|}.

Ltac introll x :=
  apply limpl_intro; intros x;
  rewrite ?LWeightZeroL, ?LWeightZeroR;
  ll_cleanhypotheses.

Definition limpl_applygoal{E:LEnv} (A B:LType) (W:LWeight)
    (x:ltype (LImpl A B)) {we:WeightEliminable2 W (lweight x)} :
    LGoal A (@WE_remain2 _ _ _ we) -> LGoal B W.
Proof.
  intros a.
  refine {|
    lgoal_proof := lfun_val x (lgoal_proof a)
  |}.
  etransitivity; [|apply lfun_weight_eqn].
  etransitivity; [symmetry; apply WE_eqn2|].
  f_equal.
  apply lgoal_weight.
Defined.

Ltac applyll x :=
  apply (limpl_applygoal _ _ _ x); simpl;
  rewrite ?LWeightZeroL, ?LWeightZeroR;
  ll_cleanhypotheses.

Definition linear_exact{E:LEnv} (A:LType) (W:LWeight)
    (x:ltype A) {we:WeightEliminable2 W (lweight x)}
    {ann:WeightAnnihilated (@WE_remain2 _ _ _ we)} : LGoal A W.
Proof.
  refine {|
    lgoal_proof := x
  |}.
  etransitivity; [symmetry; apply WE_eqn2|].
  rewrite <-(@WA_eqn _ _ ann).
  apply LWeightZeroL.
Defined.

Ltac exactll x := apply (linear_exact _ _ x).

Lemma CombinatorB{E:LEnv} (A B C:LType) :
  @LGoal _ (LImpl (LImpl B C) (LImpl (LImpl A B) (LImpl A C))) LWeightZero.
Proof.
  introll x.
  introll y.
  introll z.
  applyll x.
  applyll y.
  exactll z.
Qed.