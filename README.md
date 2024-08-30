# Gödel's ontological proof

This is an implementation of Gödel's ontological proof in Agda. The embedding of modal higher-order logic into type theory is partially taken from [the proof in Isabelle](https://www.isa-afp.org/entries/GoedelGod.html), but the proofs themselves are original. For reference, all axioms, theorems, and definitions have names from the original Isabelle implementation. All results proved in Isabelle are covered, with the exception of the consistency proof automated with Nitpick.

I would like to thank [Nathaniel Burke](https://github.com/NathanielB123) for suggesting an elegant use of level variables in the definitions of formulas of modal HOL. Level variables are necessary to obtain a working straight-forward embedding of these formulas into Agda. To ease Agda's inference, they are also made explicit.

Precisely because of these levels, however, the proofs gradually spiral out of control, as more and more arbitrary and difficult adjustments of levels are required. To preserve my sanity, I introduced an additional axiom:
```
postulate
    lift-G : (x : 𝕀) → (G l) x ⊨ (G (lsuc l)) x
```
It states that, if an individual `x` is God at level `l`, it is also God at the next level. I hope it is not inconsistent.