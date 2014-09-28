## Linear Logic Toy for Coq

This is a "Toy" for playing with Linear Logic in Coq.

### What is it?

Coq beginners usually prove something like this:

```coq
Example Modus_Ponens : forall P Q:Prop, P /\ (P -> Q) -> Q.
Proof.
  intros P Q [H0 H1].
  apply H1, H0.
Qed.
```

This is an example of (intuitionistic or classical) propositional logic. Coq users also play with a predicate logic.

So what about Linear Logic?

With this module, you can prove something like this:

```coq
Require Import LType.

Example Modus_Ponens{E:LEnv} : forall P Q:LType, ILL |- P * (P -o Q) -o Q.
Proof.
  introsll P Q H.
  destructll H as [H0 H1].
  applyll H1.
  applyll H0.
Qed.
```

Currently, statements of Intuitionistic (propositional or predicate) Linear Logic can be proved. Enjoy!

### How to compile

```
$ coq_makefile -f Make -o Makefile
$ make
```

Tested in Coq 8.4pl3.

### How to invoke CoqTop or CoqIDE

```
$ coqide -R . LType
```

### List of types and tactics

<table>
 <tr>
  <th>Type</th>
  <th>Description</th>
  <th>Hypothesis H</th>
  <th>Goal</th>
 </tr>
 <tr>
  <th><code>A -o B</code></th>
  <td>Linear Implication</td>
  <td><code>applyll H</code></td>
  <td><code>introsll H</code></td>
 </tr>
 <tr>
  <th><code>A * B</code></th>
  <td>Multiplicative Conjunction</td>
  <td><code>destructll H as [H0 H1]</code></td>
  <td>
   <code>splitll H carrying (H0 + H1)%LWeight into 1</code> or
   <code>splitll H carrying 0%LWeight into 1</code> or
   <code>splitll H carrying H0 into 2</code> or something
  </td>
 </tr>
 <tr>
  <th><code>1</code></th>
  <td>Unit of Multiplicative Conjunction</td>
  <td><code>destructll H as []</code></td>
  <td><code>splitll</code></td>
 </tr>
 <tr>
  <th><code>A &amp;&amp; B</code></th>
  <td>Additive Conjunction</td>
  <td>
   <code>destructll H as [H0 _]</code> or
   <code>destructll H as [_ H1]</code>
  </td>
  <td><code>splitll H</code></td>
 </tr>
 <tr>
  <th><code>LTop</code></th>
  <td>Unit of Additive Conjunction</td>
  <td>-</td>
  <td><code>splitll H</code></td>
 </tr>
 <tr>
  <th><code>A + B</code></th>
  <td>Additive Disjunction</td>
  <td><code>destructll H as [H0 | H1]</code></td>
  <td>
   <code>leftll H</code> or
   <code>rightll H</code>
  </td>
 </tr>
 <tr>
  <th><code>0</code></th>
  <td>Unit of Additive Disjunction</td>
  <td><code>destructll H as []</code></td>
  <td>-</td>
 </tr>
 <tr>
  <th><code>!A</code></th>
  <td>Conjunctive Exponential Modality</td>
  <td>
   <code>destructll H as [H]</code> or
   <code>clonell H as [H0 H1]</code> or
   <code>clonell H into H0</code> or
   <code>clearll H</code>
  </td>
  <td><code>splitll</code></td>
 </tr>
 <tr>
  <th><code>lforall x : T, A</code></th>
  <td>Linear Universal Quantification</td>
  <td><code>specializell (H x)</code></td>
  <td><code>introll x</code></td>
 </tr>
 <tr>
  <th><code>lexists x : T, A</code></th>
  <td>Linear Existential Quantification</td>
  <td><code>destructll H as [x H]</code></td>
  <td><code>existsll x</code></td>
 </tr>
 <tr>
  <th><code>A o-o B</code></th>
  <td>Shorthand for <code>(A -o B) &amp;&amp; (B -o A)</code></td>
  <td></td>
  <td></td>
 </tr>
</table>

### Other tactics

- `apply x` ... Can be used when x is exactly the answer.
- `apply x` ... Can be used when x has a type `A -o B -o C` and the goal is `C`. This time, you have to use `carrying W into n` tactical to specify where to send each hypothesis.

