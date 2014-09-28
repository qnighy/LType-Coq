(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LWeight LType_base LGoal.

(*************************************************)
(*        Linear Existential Quantification      *)
(*************************************************)

Definition LExists{E:LEnv} {T:Type} (A:T->LType) : LType := {|
  ltype := { t : T & ltype (A t) };
  lweight x := lweight (projT2 x)
|}.
Notation "'lexists' x .. y , p"
    := (LExists (fun x => .. (LExists (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'lexists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : LL_scope.


Definition LExistsConstructor{E:LEnv} {T:Type} {A:T -> LType} {W:LWeight}
    (t : T)
    : LGoal (A t) W -> LGoal (LExists A) W.
Proof.
  intros H0.
  refine {|
    lgoal_proof := existT _ t (lgoal_proof H0) : ltype (LExists A)
  |}.
Defined.

Definition LExistsDestructor{E:LEnv} {T:Type} {A:T -> LType} {B:LType}
    {W:LWeight}
    : (forall t, LGoal (A t -o B) W) -> LGoal (LExists A -o B) W.
Proof.
  intros H0.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(a:ltype (LExists A)) =>
        lgoal_proof (H0 (projT1 a)) (projT2 a);
      lfun_weight := W
    |} : ltype (LExists A -o B)
  |}.
Grab Existential Variables.
  intros x; simpl; refine (lweight_eqn _).
Defined.

Local Ltac existsll_base x ::=
  apply (LExistsConstructor x) ||
  fail "Constructor not found".
Local Ltac destructll_base ::=
  apply LExistsDestructor ||
  fail "Destructor not found".


Local Open Scope LL_goal_scope.
Example LExistsComm{E:LEnv} {S T:Type} (A:S -> T -> LType) :
  (ILL |- (lexists s t, A s t) -o (lexists t s, A s t)).
Proof.
  introsll x.
  destructll x as [s x].
  destructll x as [t x].
  existsll t.
  existsll s.
  applyll x.
Defined.
Local Close Scope LL_goal_scope.