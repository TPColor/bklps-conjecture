# bklps-conjecture

In what follows, we resolve Conjecture 5 of Bonamy–Knor–Lužar–Pinlou–Škrekovski's `On the difference between the Szeged and Wiener index`, officially linked in https://doi.org/10.1016/j.amc.2017.05.047.
In case you don't have access to it, the arXiv preprint is found as https://arxiv.org/abs/1602.05184.

The paper uses the notation `K_n^t` to refer to the complete graph `K_{n-1}` but with an extra vertex that's adjacent to `t` vertices of the `K_{n-1}` part. We determine the Szeged–Wiener gap `η(K_n^t)` of `K_n^t` in our Theorem 1.

The conjecture asserts that if `G` is a finite simple `2`-connected graph of order `n ≥ 10` not isomorphic to `K_n`, `K_n^2`, nor `K_n^{n−2}`, then the Szeged–Wiener gap of `G` is `η(G) ≥ 2n`. This result is formalized in `BKLPS.lean` and is proved with our own notation as Theorem 6. The formalization for the definitions in the papers are found in `Definitions.lean`.

Additionally, Lemma 7 establishes that this bound attains equality for all `n ≥ 10`. Our forthcoming paper (which we plan to publish to arxiv), invites the reader to determine all equality cases.

Lily Zhang independently supplied the main lemmas to resolve the conjecture (pink@berkeley.edu).<br>
Evan Li helped me prove lemmas such as Lemma 2 and Lemma 4 as well as providing programs to check small cases of `n` for Lemma 2 and Theorem 3 (Evl012@ucsd.edu).<br>
Much of this lean formalization was assisted with GPT-5.6 Luna.

# Reproduce

Install Lean 4.27.0 using your usual Lean installation method. From this directory run in powershell:

```powershell
lake build
```
While it takes a while, the file indeed compiles with Lean 4.27.0. There are no `sorry`, `admit`, nor user-created axioms. However, it was difficult for us to avoid `native_decide` since we could not find an easy non-computational argument to resolve the `n = 10` case. We only used it to perform the order 10 check for the base case of our induction to prove Theorem 6. BKLPS themselves claimed in their paper that they performed this search computationally.

# Remark

Another proof appeared on September 8, 2026. Their GitHub formalization is found here: https://github.com/FDmd233/strengthened-szeged-wiener-conjecture

We worked on this conjecture early August as a collaboration, and we eventually solved it (I forgot exactly when). We typed proof sketches to check for errors by putting them through ChatGPT. Their links are below. The most recent one was on August 30, 2026. The proofs are easily recoverable from these links, since most of the remaining steps are fairly trivial (like the `m=5` case for Lemma 4).

https://chatgpt.com/s/t_6ad380016500819183cfbd4660a143f6
https://chatgpt.com/s/t_6ad38131a45881918c4a83b5ee02bbef
https://chatgpt.com/s/t_6ad389aa2be0819198c1ed564675e6dc
https://chatgpt.com/s/t_6ad38585a1c881919f9c2e5564f9f4db
https://chatgpt.com/s/t_6ad38dcb15a48191a6f3a435f1cad645