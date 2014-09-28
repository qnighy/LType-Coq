(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LWeight.

(*************************************************)
(*        Definition of Linear Type              *)
(*************************************************)

Delimit Scope LL_scope with LL.
Reserved Notation "A '-o' B"
  (at level 99, right associativity, B at level 200).
Reserved Notation "! A"
  (at level 30).
Reserved Notation "'lforall' x .. y , p"
  (at level 200, x binder, right associativity,
   format "'[' 'lforall'  '/  ' x  ..  y ,  '/  ' p ']'").
Reserved Notation "'lexists' x .. y , p"
  (at level 200, x binder, right associativity,
   format "'[' 'lexists'  '/  ' x  ..  y ,  '/  ' p ']'").


Record LType{E:LEnv} := {
  ltype : Type;
  lweight : ltype -> @LWeight E
}.
Arguments LType [E].
Arguments Build_LType [E] _ _.
Arguments ltype [E] _%LL.
Arguments lweight [E] [_] _.

Coercion lweight : ltype >-> LWeight.

(* Linear Implication *)
Record LFun{E:LEnv} (A B:LType) := {
  lfun_val : ltype A -> ltype B;
  lfun_weight : @LWeight E;
  lfun_weight_eqn :
    forall x : ltype A,
      (lfun_weight + lweight x = lweight (lfun_val x))%LWeight
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
Notation "A -o B" := (LImpl A%LL B%LL) : LL_scope.
Coercion lfun_val : LFun >-> Funclass.

Instance LImpl_weight_decompose{E:LEnv} (A B:LType)
    (f : ltype (A -o B)) (x : ltype A)
    : LWeightCastPlus (lweight (f x)) (lweight f) (lweight x).
Proof.
  rewrite <-lfun_weight_eqn.
  auto with typeclass_instances.
Defined.
