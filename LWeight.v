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
  LWeightPlusComm a b : LWeightPlus a b = LWeightPlus b a;
  LPole : Type;
  lpoleweight : LPole -> LWeight
}.

Delimit Scope LWeight_scope with LWeight.
Arguments LWeightPlus [_] _%LWeight _%LWeight.
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
Class LWeightCastSelf{E:LEnv} (W V:LWeight) := {
  lweightcastself_eqn : (V = W)%LWeight
}.
Arguments LWeightCastSelf [E] W%LWeight V%LWeight.
Arguments Build_LWeightCastSelf [E] [W] [V] _.
Arguments lweightcastself_eqn [E] [W] [V] [_].
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
Instance LWeightMinus_VSelf{E:LEnv} {W X V V0:LWeight}
    {H:LWeightCastSelf V V0}
    {H0:LWeightMinus W V0 X}
    : LWeightMinus W V X | 2.
Proof.
  rewrite <-(@lweightcastself_eqn _ _ _ H).
  exact H0.
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
Instance LWeightMinus1_WSelf{E:LEnv} {W V X W0:LWeight}
    {H:LWeightCastSelf W W0}
    {H0:LWeightMinus1 W0 V X}
    : LWeightMinus1 W V X | 2.
Proof.
  rewrite <-(@lweightcastself_eqn _ _ _ H).
  exact H0.
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

Class LWeightEquation{E:LEnv} (W V:LWeight) := {
  lweight_eqn : W = V
}.
Arguments LWeightEquation [E] W V.
Arguments Build_LWeightEquation [E] [W] [V] _.
Arguments lweight_eqn [E] [W] [V] _.

Instance LWeightEquationAuto{E:LEnv} {W V X:LWeight}
    {mn:LWeightMinus W V X} {annihil:LWeightAnnihil X}
    : LWeightEquation W V.
Proof.
  exists.
  rewrite <-lweightminus_eqn.
  rewrite (@lweightannihil_eqn _ _ annihil).
  apply LWeightZeroL.
Defined.

Definition lweight_hole{E:LEnv} (W:LWeight) := W.
Lemma lweight_hole_unfold{E:LEnv} (W:LWeight)
  : lweight_hole W = W.
Proof.
  reflexivity.
Qed.
Opaque lweight_hole.
