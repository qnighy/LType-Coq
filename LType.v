(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import List.


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


(*************************************************)
(*        Definition of Linear Type              *)
(*************************************************)

Delimit Scope ILL_scope with ILL.
Reserved Notation "'TT'".
Reserved Notation "A '-o' B"
  (at level 99, right associativity, B at level 200).
Reserved Notation "! A"
  (at level 30).

Record LType{E:LEnv} := {
  ltype : Type;
  lweight : ltype -> @LWeight E
}.
Arguments LType [E].
Arguments Build_LType [E] _ _.
Arguments ltype [E] _%ILL.
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
Notation "A -o B" := (LImpl A%ILL B%ILL) : ILL_scope.
Coercion lfun_val : LFun >-> Funclass.

Instance LImpl_weight_decompose{E:LEnv} (A B:LType)
    (f : ltype (A -o B)) (x : ltype A)
    : LWeightCastPlus (lweight (f x)) (lweight f) (lweight x).
Proof.
  rewrite <-lfun_weight_eqn.
  auto with typeclass_instances.
Defined.

Record LGoal{E:LEnv} (T:LType) (W:LWeight) : Type := {
  lgoal_proof :> ltype T;
  lgoal_weight_eqn : LWeightEquation W (lweight lgoal_proof)
}.
Arguments LGoal [E] T%ILL W%LWeight.
Arguments Build_LGoal [E] [T] [W] _ _.
Arguments lgoal_proof [E] [T] [W] _.
Arguments lgoal_weight_eqn [E] [T] [W] _.
Existing Instance lgoal_weight_eqn.

Instance lgoal_weight_self{E:LEnv} {T:LType} {W:LWeight}
    (H:LGoal T W) : LWeightCastSelf (lweight (lgoal_proof H)) W.
Proof.
  exists.
  apply lweight_eqn, lgoal_weight_eqn.
Defined.

Fixpoint implication_list(T:list Type) (G:Type) : Type :=
  match T with
  | nil => G
  | cons Th Tl => Th -> implication_list Tl G
  end.

Fixpoint implication_list_map{T:list Type} {A B:Type}
    (f : A -> B) : implication_list T A -> implication_list T B :=
  match T with
  | nil => f
  | cons Th Tl => fun g x => implication_list_map f (g x)
  end.

Definition LHinted{E:LEnv} (l:list (nat * LWeight)) (G:Type) := G.
Arguments LHinted [E] l%LWeight G.

Class LHintedApp{E:LEnv} (n:nat) (l:list (nat * LWeight))
                (Impls:list Type) (G:Type) := {
  lhinted_app_val : implication_list Impls G
}.
Arguments LHintedApp [E] n l%LWeight Impls G.
Arguments Build_LHintedApp [E] n l%LWeight Impls [G] _.
Arguments lhinted_app_val [E] [n] [l] [Impls] [G] _.

Instance lgoal_autoapply_self{E:LEnv} {T:LType} {n:nat}
   {l:list (nat * LWeight)} {a:ltype T}
   : LHintedApp n l nil (LGoal T (0 + lweight a)%LWeight).
Proof.
  exists.
  refine {|
    lgoal_proof := a
  |}.
Defined.

Definition lgoal_autoapply_take{E:LEnv} {A B T:LType} {n:nat}
  {l:list (nat * LWeight)} {W:LWeight} (HintWeight:LWeight)
  {f:ltype (A -o B)}
  {Impls:list Type}
  {H:forall a:LGoal A HintWeight,
       LHintedApp (S n) l Impls (LGoal T (W + lweight (f a))%LWeight)}
  : LHintedApp n l (LGoal A HintWeight :: Impls)%list
                      (LGoal T (W + HintWeight + lweight f)%LWeight).
Proof.
  exists.
  intros a.
  generalize (lhinted_app_val (H a)); clear H.
  apply implication_list_map.
  intros H.
  refine {| lgoal_proof := H |}.
Defined.

(* manual instance for lgoal_autoapply_take. *)
Hint Extern 1 (LHintedApp ?n ?l _ (LGoal ?T (_ + lweight ?f)%LWeight)) =>
  lazymatch l with
  | context ctx [(n,?W)] =>
      (* idtac "weight is " W; *)
      eapply (lgoal_autoapply_take W)
  | _ =>
      (* idtac "hint not found"; *)
      eapply (lgoal_autoapply_take (lweight_hole _))
  end
  : typeclass_instances.


Definition lhinted_init{E:LEnv} {G:Type}
    (H : LHinted nil G) : G := H.

Definition lhinted_add{E:LEnv} {G:Type} {l:list (nat * LWeight)}
    (n:nat) (W:LWeight)
    (H : LHinted ((n,W)::l)%list G) : LHinted l G := H.

Definition lgoal_autoapply_getvalue{E:LEnv} {l:list (nat * LWeight)}
    {T:LType} {W:LWeight} {X:LWeight} {A:LType} (a:ltype A)
    {Tl:list Type}
    {H:LHintedApp 0 l Tl (LGoal T (X + a))}
    (H0:(W = X + a)%LWeight)
    (Next:implication_list Tl (LGoal T W) -> LGoal T W)
    : LHinted l (LGoal T W).
Proof.
  apply Next; clear Next.
  generalize (lhinted_app_val H); clear H.
  apply implication_list_map.
  intros H.
  refine {|
    lgoal_proof := lgoal_proof H
  |}.
  rewrite H0; refine _.
Defined.

Ltac lweight_solve_hole_check :=
  match goal with
  | [ |- _ = ?x ] =>
      lazymatch x with
      | context ctx [lweight_hole ?h] =>
          idtac "found 1 hole";
          lazymatch context ctx [0%LWeight] with
          | context ctx2 [lweight_hole ?h2] =>
              idtac "foud 2 hole";
              fail "found 2 hole"
          | _ => idtac
          end
      | _ => idtac
      end
  end.

Lemma test{E:LEnv} {A B C D:LType}
  (x:ltype A) (y:ltype B) (z:ltype (A -o B -o C -o D)) : LGoal (C -o D) (x+y+z).
Proof.
  apply lhinted_init.
  (* apply (lhinted_add 0 x). *)
  eapply (lgoal_autoapply_getvalue z).
  - lweight_solve_hole_check.
    let f := lweight_solve_count_holes (x + y + z)%LWeight in idtac f.
    refine (_:x + y + z = 0 + x + y + z)%LWeight.
    apply (lweight_eqn _).
  - intros H; apply H.
  assert (H := lgoal_autoapply_getvalue nil (C -o D)%ILL (x + y + z)%LWeight z).
  lazymatch goal with
  | [ |- LGoal ?T ?W ] =>
      let Tl := fresh Tl in
      evar (Tl : list Type);
      let X := fresh X in
      evar (X : LWeight);
      let H := fresh H in
      assert (H : @LHintedApp E 0 nil Tl (LGoal T (X+z)));
        [unfold Tl,X in *; refine _; eapply _|]
  end.
  admit.
  admit.
  refine _.
  - eapply lgoal_autoapply_take.
Qed.

Class LHinted{E:LEnv} (n:nat) (l:list (nat * LWeight))
    (W V:LWeight) (G:Type) {G':Type} := {
  lhinted_val : W = V -> G'
}.
Arguments LHinted [E] n l%LWeight W%LWeight V%LWeight G [G'].
Arguments Build_LHinted [E] n l%LWeight W%LWeight V%LWeight [G] [G'] _.
Arguments lhinted_val [E] [n] [l] [W] [V] [G] [G'] _ _.

Instance lgoal_autoapply_self{E:LEnv} {T:LType} {n:nat}
   {l:list (nat * LWeight)} {W V:LWeight} {a:ltype T}
   : @LHinted _ n l W V (LGoal T (0 + lweight a)%LWeight)
                        (LGoal T (0 + lweight a)%LWeight).
Proof.
  split.
  intros H.
  refine {|
    lgoal_proof := a
  |}.
Defined.

Definition lgoal_autoapply_take{E:LEnv} {A B T:LType} {n:nat}
  {l:list (nat * LWeight)} {W eqW eqV:LWeight} (HintWeight:LWeight)
  {f:ltype (A -o B)}
  {G':LGoal A HintWeight -> Type}
  {H:forall a:LGoal A HintWeight,
       @LHinted _ (S n) l eqW eqV (LGoal T (W + lweight (f a))%LWeight) (G' a)}
  : @LHinted _ n l eqW eqV (LGoal T (W + HintWeight + lweight f)%LWeight)
                           (forall a:LGoal A HintWeight, G' a).
Proof.
  exists.
  intros Heq a.
  apply (lhinted_val (H a)), Heq.
Defined.

Hint Extern 1 (LHinted ?n ?l (LGoal ?T (_ + lweight ?f)%LWeight)) =>
  lazymatch l with
  | context ctx [(n,?W)] =>
      idtac "weight is " W;
      eapply (lgoal_autoapply_take W)
  | _ =>
      idtac "hint not found";
      eapply (lgoal_autoapply_take _)
  end
  : typeclass_instances.

(*
Definition lgoal_autoapply_prepare{E:LEnv} {A T:LType}
  (l:list (nat * LWeight)) {W X:LWeight}
  (a:ltype A) {G':Type}
  (H0:@LHinted _ 0 l W (X+lweight a)
                       (LGoal T (X+lweight a)) G')
  : LGoal T W.
Proof.
  refine {|
    lgoal_proof := lhinted_val H0;
    lgoal_weight_eqn := _
  |}.
  rewrite H.
  refine _.
Defined.
*)

Lemma test{E:LEnv} {A B C D:LType}
  (x:ltype A) (y:ltype B) (z:ltype (A -o B -o C -o D)) : LGoal (C -o D) (x+y+z).
Proof.
  lazymatch goal with
  | [ |- LGoal ?T ?W ] =>
      let G' := fresh G' in
      evar (G' : Type);
      let X := fresh X in
      evar (X : LWeight);
      let H := fresh H in
      assert (H : @LHinted _ 0 nil (x + y + z) (X+z) (LGoal T (X+z)) G');
        unfold G' in *; clear G';
        unfold X in *; clear X
  end.
  - eapply lgoal_autoapply_take.
    intros a.
    eapply (@lgoal_autoapply_take E B (C -o D)%ILL (C -o D)%ILL
                                  1 nil).
    intros b.
    eapply lgoal_autoapply_self.
  - destruct H as [H].
  apply lhinted_val with
    (n:=0) (l:=((1, (x + y)%LWeight) :: nil)%list)
    (G:=LGoal (C -o D) (x + y + z)).
  eapply (lgoal_autoapply_prepare z).
  - eapply (@lgoal_autoapply_take).
    
  -
  reflexivity.
  - eapply (lgoal_autoapply_take _).
    refine _.
  eapply (lgoal_autoapply_prepare z _).
  refine (_:(x + y + z)%LWeight = (0 + (x + y) + 0 + z)%LWeight).
  apply (lweight_eqn _).
  instantiate.
  instantiate.
  - eapply (lgoal_autoapply_take (x + y)%LWeight).
    eapply (lgoal_autoapply_take _).
    apply lgoal_autoapply_self.
    refine _.
    eapply (lgoal_autoapply_take (x + y)%LWeight).
  -
Defined.

Notation "T [ 'using_hypotheses' W ]" :=
  (LGoal T%ILL W%LWeight)
  (at level 100,
   no associativity,
   format "'[' T '//' [ 'using_hypotheses'  W ] ']'").

Definition limpl_intro{E:LEnv} {A B:LType} {W:LWeight}
    (X : forall a : ltype A, LGoal B (W + lweight a)) :
    LGoal (A -o B) W := {|
  lgoal_proof := {|
    lfun_val a := lgoal_proof (X a);
    lfun_weight := W;
    lfun_weight_eqn a := lweight_eqn _
  |} : ltype (A -o B)
|}.

Definition limpl_revert{E:LEnv} {A B:LType} {W:LWeight} (x:ltype A)
    {X:LWeight} {mn:LWeightMinus W (lweight x) X}
    (H : LGoal (A -o B) X) : LGoal B W.
Proof.
  refine {|
    lgoal_proof := lfun_val (lgoal_proof H) x;
    lgoal_weight_eqn := {| lweight_eqn := _ |}
  |}.
  rewrite <-lweightminus_eqn.
  apply (lweight_eqn _).
Defined.

Definition linear_exact{E:LEnv} {A:LType} {W:LWeight}
    (x:ltype A) {eqn:LWeightEquation W (lweight x)} : LGoal A W.
Proof.
  refine {|
    lgoal_proof := x
  |}.
Defined.

Definition limpl_applygoal{E:LEnv} {A B:LType} {W:LWeight}
    (x:ltype (A -o B)) {X:LWeight} {mn:LWeightMinus W (lweight x) X} :
    LGoal A X -> LGoal B W.
Proof.
  intros a.
  refine {|
    lgoal_proof := lfun_val x (lgoal_proof a)
  |}.
Defined.

Definition linear_cut{E:LEnv} (A:LType) {B:LType} {W:LWeight} (V:LWeight)
    {X:LWeight} {mn:LWeightMinus W V X}
    : LGoal (A -o B) V -> LGoal A X -> LGoal B W.
Proof.
  intros X0 X1.
  refine {|
    lgoal_proof := lfun_val (lgoal_proof X0) (lgoal_proof X1)
  |}.
  etransitivity; [symmetry; apply lweightminus_eqn|].
  rewrite <-lfun_weight_eqn.
  f_equal.
  - apply (@lgoal_weight _ _ _ X0).
  - apply (@lgoal_weight _ _ _ X1).
Defined.
Arguments linear_cut [E] A%ILL [B] [W] V%LWeight [X] [mn] _ _.

Definition LTensor{E:LEnv} (A B:LType) : LType := {|
  ltype := ltype A * ltype B;
  lweight x := (lweight (fst x) + lweight (snd x))%LWeight
|}.
Definition LOne{E:LEnv} : LType := {|
  ltype := unit;
  lweight := fun _ => 0%LWeight
|}.
Notation "A * B" := (LTensor A%ILL B%ILL) : ILL_scope.
Notation "1" := LOne : ILL_scope.

Definition ltensor_split{E:LEnv} {A B:LType} {W:LWeight} (V:LWeight)
    {X:LWeight} {mn:LWeightMinus W V X} :
    LGoal A V -> LGoal B X -> LGoal (A * B) W.
Proof.
  intros a b.
  refine {|
    lgoal_proof := (lgoal_proof a, lgoal_proof b) : ltype (A * B)
  |}.
  etransitivity; [symmetry; apply lweightminus_eqn|].
  simpl.
  f_equal; apply lgoal_weight.
Defined.

Definition lone_split{E:LEnv} {W:LWeight}
  {annihil:LWeightAnnihil W} : LGoal 1 W.
Proof.
  refine {|
    lgoal_proof := tt : ltype 1
  |}.
  apply lweightannihil_eqn.
Defined.

Definition ltensor_uncurry{E:LEnv} {A B C:LType} {W:LWeight} :
  LGoal (A -o B -o C) W -> LGoal (A * B -o C) W.
Proof.
  intros H.
  refine {|
    lgoal_proof := {|
      lfun_val := fun (x:ltype (A * B)) =>
        lfun_val (lfun_val (lgoal_proof H) (fst x)) (snd x);
      lfun_weight := W
    |} : ltype (A * B -o C)
  |}.
  reflexivity.
Grab Existential Variables.
  intros x; simpl.
  rewrite <-lfun_weight_eqn.
  rewrite LWeightPlusAssoc.
  f_equal.
  etransitivity; [|apply (@lfun_weight_eqn _ _ _ (lgoal_proof H))].
  f_equal.
  apply (@lgoal_weight _ _ _ H).
Defined.

Definition lone_uncurry{E:LEnv} {A:LType} {W:LWeight} :
  LGoal A W -> LGoal (1 -o A) W.
Proof.
  intros H.
  refine {|
    lgoal_proof := {|
      lfun_val := fun (x:ltype 1) => lgoal_proof H;
      lfun_weight := W
    |} : ltype (1 -o A)
  |}.
  reflexivity.
Grab Existential Variables.
  intros x; simpl.
  rewrite LWeightZeroL.
  apply lgoal_weight.
Defined.


Record LWithVal{E:LEnv} (A B:LType) := {
  lwithval_fst : ltype A;
  lwithval_snd : ltype B;
  lwithval_weight_eqn : lweight lwithval_fst = lweight lwithval_snd
}.
Arguments LWithVal [E] A%ILL B%ILL.
Arguments lwithval_fst [E] [A] [B] _.
Arguments lwithval_snd [E] [A] [B] _.
Arguments lwithval_weight_eqn [E] [A] [B] _.

Definition LWith{E:LEnv} (A B:LType) : LType := {|
  ltype := LWithVal A B;
  lweight x := lweight (lwithval_fst x)
|}.
Definition LTop{E:LEnv} : LType := {|
  ltype := LWeight;
  lweight x := x
|}.
Notation "A && B" := (LWith A%ILL B%ILL) : ILL_scope.
Notation "'TT'" := LTop : ILL_scope.

Definition lwith_split{E:LEnv} {A B:LType} {W:LWeight}
  (H0 : LGoal A W) (H1 : LGoal B W) : LGoal (A && B) W.
Proof.
  refine {|
    lgoal_proof := {|
      lwithval_fst := lgoal_proof H0;
      lwithval_snd := lgoal_proof H1;
      lwithval_weight_eqn :=
        eq_trans (eq_sym (lgoal_weight H0)) (lgoal_weight H1)
    |} : ltype (A && B);
    lgoal_weight := lgoal_weight H0
  |}.
Defined.
Definition ltop_split{E:LEnv} {W:LWeight} : LGoal TT W.
Proof.
  refine {|
    lgoal_proof := W : ltype TT;
    lgoal_weight := eq_refl
  |}.
Defined.

Definition lwith_uncurry_l{E:LEnv} {A B C:LType} {W:LWeight}
  (H0 : LGoal (A -o C) W) : LGoal (A && B -o C) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(x : ltype (A && B)) =>
        lfun_val (lgoal_proof H0) (lwithval_fst x);
      lfun_weight := W
    |} : ltype (A && B -o C);
    lgoal_weight := eq_refl
  |}.
Grab Existential Variables.
  intros x; simpl.
  rewrite <-lfun_weight_eqn.
  f_equal.
  apply (@lgoal_weight _ _ _ H0).
Defined.
Definition lwith_uncurry_r{E:LEnv} {A B C:LType} {W:LWeight}
  (H1 : LGoal (B -o C) W) : LGoal (A && B -o C) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(x : ltype (A && B)) =>
        lfun_val (lgoal_proof H1) (lwithval_snd x);
      lfun_weight := W
    |} : ltype (A && B -o C);
    lgoal_weight := eq_refl
  |}.
Grab Existential Variables.
  intros x; simpl.
  rewrite lwithval_weight_eqn.
  rewrite <-lfun_weight_eqn.
  f_equal.
  apply (@lgoal_weight _ _ _ H1).
Defined.

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
Notation "A + B" := (LPlus A%ILL B%ILL) : ILL_scope.
Notation "0" := LZero : ILL_scope.

Definition lplus_left{E:LEnv} {A B:LType} {W:LWeight}
    (H0 : LGoal A W) : LGoal (A + B) W.
Proof.
  refine {|
    lgoal_proof := inl (lgoal_proof H0) : ltype (A + B)
  |}.
  apply lgoal_weight.
Defined.
Definition lplus_right{E:LEnv} {A B:LType} {W:LWeight}
    (H1 : LGoal B W) : LGoal (A + B) W.
Proof.
  refine {|
    lgoal_proof := inr (lgoal_proof H1) : ltype (A + B)
  |}.
  apply lgoal_weight.
Defined.

Definition lplus_uncurry{E:LEnv} {A B C:LType} {W:LWeight}
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
    |} : ltype (A + B -o C);
    lgoal_weight := eq_refl
  |}.
Grab Existential Variables.
  intros [xl|xr]; simpl.
  - rewrite <-lfun_weight_eqn.
    f_equal.
    apply (@lgoal_weight _ _ _ H0).
  - rewrite <-lfun_weight_eqn.
    f_equal.
    apply (@lgoal_weight _ _ _ H1).
Defined.
Definition lzero_uncurry{E:LEnv} {A:LType} {W:LWeight}
    : LGoal (0 -o A) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun (x:ltype 0) =>
        match x with end;
      lfun_weight := W
    |} : ltype (0 -o A);
    lgoal_weight := eq_refl
  |}.
Grab Existential Variables.
  intros [].
Defined.

Record LOfcourseVal{E:LEnv} (A:LType) := {
  lofcourseval : ltype A;
  lofcourseval_nil : lweight lofcourseval = 0%LWeight
}.
Arguments LOfcourseVal [E] A%ILL.
Arguments Build_LOfcourseVal [E] [A] _ _.
Arguments lofcourseval [E] [A] _.
Arguments lofcourseval_nil [E] [A] _.

Definition LOfcourse{E:LEnv} (A:LType) : LType := {|
  ltype := LOfcourseVal A;
  lweight := fun _ => 0%LWeight
|}.
Notation "! A" := (LOfcourse A%ILL) : ILL_scope.

Instance LOfcouse_weight_decompose{E:LEnv} (A:LType)
    (x : ltype (!A))
    : LWeightCastZero x.
Proof.
  exists.
  reflexivity.
Defined.

Definition lofcourse_promote{E:LEnv} {A:LType}
    {W:LWeight} {annihil:LWeightAnnihil W}
    (H0 : LGoal A 0) : LGoal (!A) W.
Proof.
  refine {|
    lgoal_proof := {|
      lofcourseval := lgoal_proof H0;
      lofcourseval_nil := eq_sym (lgoal_weight H0)
    |} : ltype (!A)
  |}.
  apply lweightannihil_eqn.
Defined.

Definition lofcourse_derelict{E:LEnv} {A B:LType} {W:LWeight}
    (a : ltype (!A))
    (H0 : LGoal (A -o B) W) : LGoal B W.
Proof.
  refine {|
    lgoal_proof := lfun_val (lgoal_proof H0) (lofcourseval a)
  |}.
  rewrite <-lfun_weight_eqn.
  rewrite lofcourseval_nil, LWeightZeroL.
  apply (@lgoal_weight _ _ _ H0).
Defined.

Ltac ll_cleanup :=
  repeat (
    rewrite <-!lweightcastzero_eqn ||
    rewrite !LWeightZeroL ||
    rewrite !LWeightZeroR);
  repeat match goal with
  | [ x : ltype ?A |- _ ] =>
      lazymatch A with
      | LOfcourse _ => fail
      | _ => idtac
      end;
      clear x
  end.

Tactic Notation "introll" ident(x) :=
  refine (limpl_intro _); intro x; ll_cleanup.
Tactic Notation "introll" :=
  let x := fresh in introll x.
Tactic Notation "introll" ident(x0) ident(x1) :=
  introll x0; introll x1.
Tactic Notation "introll" ident(x0) ident(x1) ident(x2) :=
  introll x0; introll x1; introll x2.
Tactic Notation "introll" ident(x0) ident(x1) ident(x2) ident(x3) :=
  introll x0; introll x1; introll x2; introll x3.
Tactic Notation "introll" ident(x0) ident(x1) ident(x2) ident(x3) ident(x4) :=
  introll x0; introll x1; introll x2; introll x3; introll x4.

Tactic Notation "revertll" ident(x) :=
  refine (limpl_revert x _); clear x; ll_cleanup.

Tactic Notation "applyll" constr(x) :=
  refine (limpl_applygoal x _); ll_cleanup.

Tactic Notation "exactll" constr(x) :=
  refine (linear_exact x).

Tactic Notation "cutll" constr(A) "carrying" constr(V) :=
  refine (linear_cut A V _ _); ll_cleanup.

Tactic Notation "splitll" "carrying" constr(V) :=
  refine (ltensor_split V _ _); ll_cleanup.
Tactic Notation "splitll" :=
  (refine lone_split; ll_cleanup) ||
  (refine (lwith_split _ _); ll_cleanup) ||
  (refine ltop_split) ||
  (refine (lofcourse_promote _); ll_cleanup).

Tactic Notation "leftll" :=
  refine (lplus_left _); ll_cleanup.
Tactic Notation "rightll" :=
  refine (lplus_right _); ll_cleanup.

Tactic Notation "destructll" ident(x) "as" "[" ident(y) ident(z) "]" :=
  revertll x; refine (ltensor_uncurry _); introll y z.

Tactic Notation "destructll" ident(x) "as" "[" ident(y) "_" "]" :=
  revertll x; refine (lwith_uncurry_l _); introll y.
Tactic Notation "destructll" ident(x) "as" "[" "_" ident(z) "]" :=
  revertll x; refine (lwith_uncurry_r _); introll z.

Tactic Notation "destructll" ident(x) "as" "[" ident(y) "|" ident(z) "]" :=
  revertll x; refine (lplus_uncurry _ _); [introll y | introll z].
Tactic Notation "destructll" ident(x) "as" "[" "]" :=
  revertll x; refine lzero_uncurry.

Tactic Notation "destructll" ident(x) :=
  (refine (lofcourse_derelict x _); clear x; introll x) ||
  (revertll x; refine (lone_uncurry _); ll_cleanup) ||
  let y := fresh in let z := fresh in
  destructll x as [y z] ||
  destructll x as [y _] ||
  destructll x as [_ y] ||
  destructll x as [y | y] ||
  destructll x as [].
  


(*************************************************)
(*                  Sample Proof                 *)
(*************************************************)

Lemma CombinatorB{E:LEnv} (A B C:LType) :
  ((B -o C) -o (A -o B) -o (A -o C))
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
  ((A -o B -o C) -o (B -o A -o C))
  [using_hypotheses 0].
Proof.
  introll x.
  introll y.
  introll z.
  applyll (lfun_val x z).
  exactll y.
Qed.

Lemma TensorComm{E:LEnv} (A B:LType) :
  (A * B -o B * A)
  [using_hypotheses 0].
Proof.
  introll x.
  destructll x as [x y].
  splitll carrying y.
  - exactll y.
  - exactll x.
Qed.

Lemma WithComm{E:LEnv} (A B:LType) :
  (A && B -o B && A)
  [using_hypotheses 0].
Proof.
  introll x.
  splitll.
  - destructll x as [_ x].
    exactll x.
  - destructll x as [x _].
    exactll x.
Qed.

Lemma PlusComm{E:LEnv} (A B:LType) :
  (A + B -o B + A)
  [using_hypotheses 0].
Proof.
  introll x.
  destructll x as [x | x].
  - rightll.
    exactll x.
  - leftll.
    exactll x.
Qed.

Lemma OfcDiggL{E:LEnv} (A:LType) :
  ((!!A) -o !A)
  [using_hypotheses 0].
Proof.
  introll x.
  splitll.
  destructll x.
  destructll x.
  exactll x.
Qed.

Lemma OfcDiggR{E:LEnv} (A:LType) :
  ((!A) -o !!A)
  [using_hypotheses 0].
Proof.
  introll x.
  splitll.
  splitll.
  destructll x.
  exactll x.
Qed.

Lemma TensorPlusCommL{E:LEnv} (A B C:LType) :
  (A * B + A * C -o A * (B + C))
  [using_hypotheses 0].
Proof.
  introll x.
  destructll x as [x | x].
  - destructll x as [x y].
    splitll carrying x.
    + exactll x.
    + leftll.
      exactll y.
  - destructll x as [x y].
    splitll carrying x.
    + exactll x.
    + rightll.
      exactll y.
Qed.

Lemma TensorPlusCommR{E:LEnv} (A B C:LType) :
  (A * (B + C) -o A * B + A * C)
  [using_hypotheses 0].
Proof.
  introll x.
  destructll x as [x y].
  destructll y as [y | y].
  - leftll.
    splitll carrying x.
    + exactll x.
    + exactll y.
  - rightll.
    splitll carrying x.
    + exactll x.
    + exactll y.
Qed.

Lemma ExponentialLawL{E:LEnv} (A B:LType) :
  (!(A && B) -o (!A) * (!B))
  [using_hypotheses 0].
Proof.
  introll x.
  splitll carrying 0%LWeight.
  - splitll.
    destructll x.
    destructll x as [x _].
    exactll x.
  - splitll.
    destructll x.
    destructll x as [_ x].
    exactll x.
Qed.
Lemma ExponentialLawR{E:LEnv} (A B:LType) :
  ((!A) * (!B) -o !(A && B))
  [using_hypotheses 0].
Proof.
  introll x.
Qed.