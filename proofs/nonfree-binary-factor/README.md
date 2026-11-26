# A nonfree factor of the binary free monoid

For $A=\{a,b\}$ there is a submonoid $M$ of $A^*$ such that each word has a unique expression

$$
(ab)^i\,b^j\,m\,a^k\,(aabb)^l, \qquad i,j,k,l\in\mathbb N, \quad m\in M.
$$

This $M$ is nonfree. The theorem rules out a monoid isomorphism with the free monoid on any alphabet, including infinite alphabets.

Manuscript by Astra 6.2, supervised by Christophe Cordero. Date of discovery 25 November 2026. [PDF](manuscript/nonfree_factor_of_the_binary_free_monoid.pdf) · [LaTeX source](manuscript/nonfree_factor_of_the_binary_free_monoid.tex)

## Lean statement

Import `NonfreeBinaryFactor`. The theorem `NonfreeBinaryFactor.exists_nonfree_factor` quantifies over an actual `Submonoid (FreeMonoid Bool)`. The letters $a,b$ are `false,true`, respectively. A decomposition is a tuple of type `ℕ × ℕ × M × ℕ × ℕ`. The function `assemble` multiplies its five factors in manuscript order. For each word the theorem asserts `∃! d, assemble M d = w`. [Main theorem](lean/NonfreeBinaryFactor/MainTheorem.lean) · [Assembly map and its bijectivity](lean/NonfreeBinaryFactor/Factorization.lean)

The witness `middleSubmonoid` is $L\cap R$. Words in $L$ avoid the prefix $ab$ and every initial $b$ is followed by $ab$. Words in $R$ avoid the suffix $aabb$ and every final $a$ is preceded by $aabb$.

| Step in the proof | Lean declarations |
| --- | --- |
| Remove the longest initial power. Then remove initial copies of a letter while the remainder stays in the prefix-avoiding language. | [`exists_prepend`, `prepend_unique`](lean/NonfreeBinaryFactor/NormalForms.lean) |
| Apply the same argument to reversed words for the two terminal powers. Appending either right-hand power preserves and reflects membership in $L$. | [`left_appendRight`, `assemble_bijective`](lean/NonfreeBinaryFactor/Factorization.lean) |
| Every nonempty middle word has length at least three. A new suffix $aabb$ across a product boundary would force the second word to be $abb$, which violates the left rule. | [`length_ge_three`, `middle_append`, `middleSubmonoid`](lean/NonfreeBinaryFactor/Submonoid.lean) |
| The equality $(aab)(babab)=(aabba)(bab)$ has distinct irreducible first factors. Under a free-monoid isomorphism both first factors would be the same letter. | [`Witness.relation`, `Witness.irreducibles`, `middle_not_free`](lean/NonfreeBinaryFactor/Nonfreeness.lean) |

## Verification

Run `./verify.sh` from the repository root to build both libraries, check the examples, audit the axioms and replay the declarations through the Lean kernel. The [audit](checks/Check.lean) allows only `propext`, `Classical.choice` and `Quot.sound`. It also checks the decomposition of the empty word and an example with all five factors nonempty.

To verify the exported proof with the independent Nanoda kernel, run the following from the repository root.

```sh
lake build NonfreeBinaryFactor
mkdir -p build
lake env leanexport NonfreeBinaryFactor.MainTheorem -- NonfreeBinaryFactor.exists_nonfree_factor > build/nonfree-binary-factor.ndjson
lake env nanoda_bin proofs/nonfree-binary-factor/checks/nanoda.json
```
