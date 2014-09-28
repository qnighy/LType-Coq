(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LType.

(*************************************************)
(*                    Examples                   *)
(*************************************************)

Example LTensorPlusDistr{E:LEnv} (A B C:LType) :
  ILL |- A * (B + C) o-o A * B + A * C.
Proof.
  splitll.
  - introsll x.
    destructll x as [x y].
    destructll y as [y | y].
    + leftll.
      splitll carrying x into 1.
      * applyll x.
      * applyll y.
    + rightll.
      splitll carrying y into 2.
      * applyll x.
      * applyll y.
  - introsll x.
    destructll x as [x | x].
    + destructll x as [x y].
      splitll carrying x into 1.
      * applyll x.
      * leftll; applyll y.
    + destructll x as [x y].
      splitll carrying x into 1; [applyll x|].
      rightll; applyll y.
Defined.

Example LOfcExponentialLaw{E:LEnv} (A B:LType) :
  ILL |- !(A && B) o-o !A * !B.
Proof.
  splitll.
  - introsll x.
    clonell x into y.
    splitll carrying x into 1.
    + splitll.
      destructll x as [x].
      destructll x as [x _].
      applyll x.
    + splitll.
      destructll y as [y].
      destructll y as [_ y].
      applyll y.
  - introsll x.
    destructll x as [x y].
    splitll.
    splitll.
    + clearll y.
      destructll x as [x].
      applyll x.
    + clearll x.
      destructll y as [y].
      applyll y.
Defined.