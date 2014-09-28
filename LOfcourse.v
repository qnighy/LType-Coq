(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LWeight LType_base LGoal.

(*************************************************)
(*       Conjunctive Exponential Modality        *)
(*************************************************)

Record LOfcourseVal{E:LEnv} (A:LType) := {
  lofcourseval : ltype A;
  lofcourseval_nil : lweight lofcourseval = 0%LWeight
}.
Arguments LOfcourseVal [E] A%LL.
Arguments Build_LOfcourseVal [E] [A] _ _.
Arguments lofcourseval [E] [A] _.
Arguments lofcourseval_nil [E] [A] _.

Definition LOfcourse{E:LEnv} (A:LType) : LType := {|
  ltype := LOfcourseVal A;
  lweight x := lweight (lofcourseval x)
|}.
Notation "! A" := (LOfcourse A%LL) : LL_scope.

Class LOfcAutoPromotion{E:LEnv} (W:LWeight) := {
  lofc_autopromotion_eqn : W = 0%LWeight
}.
Instance LOfcAutoPromotionZero{E:LEnv} : LOfcAutoPromotion 0%LWeight.
Proof.
  exists; reflexivity.
Defined.
Instance LOfcAutoPromotionPlus{E:LEnv} {W0 W1:LWeight}
    {H0:LOfcAutoPromotion W0} {H1:LOfcAutoPromotion W1}
    : LOfcAutoPromotion (W0 + W1)%LWeight.
Proof.
  exists.
  rewrite (@lofc_autopromotion_eqn _ _ H0).
  rewrite (@lofc_autopromotion_eqn _ _ H1).
  apply LWeightZeroL.
Defined.
Instance LOfcAutoPromotionOfc{E:LEnv} (A:LType)
  (v:ltype (!A)) : LOfcAutoPromotion v.
Proof.
  exists; apply lofcourseval_nil.
Defined.

(* Promotion *)
Definition LOfcConstructor{E:LEnv} {A:LType} {W:LWeight}
    {H:LOfcAutoPromotion W} : LGoal A W -> LGoal (!A) W.
Proof.
  intros H0.
  refine {|
    lgoal_proof := {|
      lofcourseval := H0
    |} : ltype (!A);
    lgoal_weight_eqn := {| lweight_eqn := _ |}
  |}.
  simpl.
  apply lgoal_weight_eqn.
Grab Existential Variables.
  rewrite <-(lweight_eqn (lgoal_weight_eqn H0)).
  apply (@lofc_autopromotion_eqn _ _ H).
Defined.

(* Dereliction *)
Definition LOfcDestructor{E:LEnv} {A B:LType} {W:LWeight}
    : LGoal (A -o B) W -> LGoal (!A -o B) W.
Proof.
  intros H0.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(oa:ltype (!A)) => (lgoal_proof H0) (lofcourseval oa);
      lfun_weight := W
    |} : ltype (!A -o B)
  |}.
Grab Existential Variables.
  intros x; simpl; refine (lweight_eqn _).
Defined.

(* Contraction *)
Definition LOfcClone{E:LEnv} {A B:LType} {W:LWeight}
    : LGoal (!A -o !A -o B) W -> LGoal (!A -o B) W.
Proof.
  intros H0.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(oa:ltype (!A)) => (lgoal_proof H0) oa oa;
      lfun_weight := W
    |} : ltype (!A -o B)
  |}.
Grab Existential Variables.
  intros x; simpl.
  rewrite <-lfun_weight_eqn.
  change (W + x = (lgoal_proof H0 x) + lofcourseval x)%LWeight.
  rewrite lofcourseval_nil.
  refine (lweight_eqn _).
Defined.

(* Weakening *)
Definition LOfcClear{E:LEnv} {A B:LType} {W:LWeight}
    : LGoal B W -> LGoal (!A -o B) W.
Proof.
  intros H0.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(oa:ltype (!A)) => lgoal_proof H0;
      lfun_weight := W
    |} : ltype (!A -o B)
  |}.
Grab Existential Variables.
  intros x; simpl.
  rewrite lofcourseval_nil.
  refine (lweight_eqn _).
Defined.



Local Ltac splitll_base ::=
  apply LOfcConstructor ||
  fail "Constructor not found".
Local Ltac destructll_base ::=
  apply LOfcDestructor ||
  fail "Destructor not found".
Local Ltac clonell_base ::=
  apply LOfcClone ||
  fail "Destructor not found".
Local Ltac clearll_base ::=
  apply LOfcClear ||
  fail "Destructor not found".

Local Open Scope LL_goal_scope.

Example LOfcDig1{E:LEnv} (A:LType) :
  (ILL |- (!!A) -o !A).
Proof.
  introsll x.
  destructll x as [x].
  applyll x.
Defined.
Example LOfcDig2{E:LEnv} (A:LType) :
  (ILL |- !A -o !!A).
Proof.
  introsll x.
  splitll.
  applyll x.
Defined.
Local Close Scope LL_goal_scope.
