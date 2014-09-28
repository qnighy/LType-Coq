(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LWeight LType_base LGoal.
Require Import LTensor LWith LPlus LOfcourse LForall LExists.

Notation "A ⊸ B" := (LImpl A B)
  (at level 99, right associativity, B at level 200): LL_scope.

Notation "A ⊗ B" := (LTensor A B)
  (at level 40, left associativity): LL_scope.

Notation "A ＆ B" := (LWith A B)
  (at level 40, left associativity): LL_scope.

Notation "⊤" := LTop (at level 0) : LL_scope.

Notation "A ⊕ B" := (LPlus A B)
  (at level 50, left associativity): LL_scope.

Reserved Notation "A ⅋ B" (at level 50, left associativity).
Reserved Notation "⊥" (at level 0).

Notation "∀ x .. y , P" := (LForall (fun x => .. (LForall (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : LL_scope.
Notation "∃ x .. y , P" := (LExists (fun x => .. (LExists (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : LL_scope.

Notation "'ILL' ⊦ T" := (LGoal T%LL 0%LWeight) (at level 200)
    : LL_goal_scope.
Notation "'ILL' ⊦ T [ 'using_hypotheses' W  ]" :=
    (LGoal T%LL W%LWeight) (at level 200) : LL_goal_scope.
