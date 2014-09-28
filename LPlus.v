(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LWeight LType_base LGoal.

(*************************************************)
(*              Additive Disjunction             *)
(*************************************************)

Definition LPlus{E:LEnv} (A B:LType) : LType := {|
  ltype := ltype A + ltype B;
  lweight x :=
    match x with
    | inl xl => lweight xl
    | inr xr => lweight xr
    end
|}.
Definition LZero{E:LEnv} : LType := {|
  ltype := Empty_set;
  lweight x := match x with end
|}.
Notation "A + B" := (LPlus A%LL B%LL) : LL_scope.
Notation "0" := LZero : LL_scope.

Definition LPlusConstructorL{E:LEnv} {A B:LType} {W:LWeight}
    (H0 : LGoal A W) : LGoal (A + B) W.
Proof.
  refine {|
    lgoal_proof := inl (lgoal_proof H0) : ltype (A + B)
  |}.
Defined.
Definition LPlusConstructorR{E:LEnv} {A B:LType} {W:LWeight}
    (H1 : LGoal B W) : LGoal (A + B) W.
Proof.
  refine {|
    lgoal_proof := inr (lgoal_proof H1) : ltype (A + B)
  |}.
Defined.

Definition LPlusDestructor{E:LEnv} {A B C:LType} {W:LWeight}
    (H0 : LGoal (A -o C) W) (H1 : LGoal (B -o C) W) : LGoal (A + B -o C) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun (x:ltype (A + B)) =>
        match x with
        | inl xl => lfun_val (lgoal_proof H0) xl
        | inr xr => lfun_val (lgoal_proof H1) xr
        end;
      lfun_weight := W
    |} : ltype (A + B -o C)
  |}.
Grab Existential Variables.
  intros [xl|xr]; simpl.
  - refine (lweight_eqn _).
  - refine (lweight_eqn _).
Defined.

Definition LZeroDestructor{E:LEnv} {A:LType} {W:LWeight}
    : LGoal (0 -o A) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun (x:ltype 0) =>
        match x with end;
      lfun_weight := W
    |} : ltype (0 -o A)
  |}.
Grab Existential Variables.
  intros [].
Defined.



Local Ltac leftll_base ::=
  apply LPlusConstructorL ||
  fail "Constructor not found".
Local Ltac rightll_base ::=
  apply LPlusConstructorR ||
  fail "Constructor not found".
Local Ltac destructll_base ::=
  apply LPlusDestructor ||
  apply LZeroDestructor ||
  fail "Destructor not found".

Local Open Scope LL_goal_scope.
Example LPlusComm{E:LEnv} (A B:LType) :
  (ILL |- A + B -o B + A).
Proof.
  introsll x.
  destructll x as [y | z].
  - rightll.
    applyll y.
  - leftll.
    applyll z.
Defined.
Local Close Scope LL_goal_scope.
