# A smallest code without a finite maximal completion

Every finite code $Y$ on a finite alphabet has a positively factorizing finite maximal completion on that alphabet whenever $|Y|\le3$, or $\lambda(Y)\le3$, or $\tau(Y)\le10$. Here $\lambda(Y)$ is the maximal length and $\tau(Y)$ the total length of the words of $Y$. For distinct letters $a,b$, the code $X=\{aa,abab,baaa,b\}$ has no finite maximal completion on any alphabet containing $a,b$. It attains the three bounds $|X|=4$, $\lambda(X)=4$ and $\tau(X)=11$ simultaneously.

Manuscript by Astra 6.2, Lean formalization by Opus 5.5, supervised by Christophe Cordero. Date of discovery 26 November 2026. [PDF](manuscript/smallest_noncompletable_code.pdf) · [LaTeX source](manuscript/smallest_noncompletable_code.tex)

## Lean statement

Import `SmallestNoncompletable`. Words are lists of letters, and a code is a set satisfying Mathlib's `InformationTheory.IsUniquelyDecodable`. A positively factorizing finite maximal completion is `ThreeWordCodes.HasPositiveCompletion` from the [three-word library](../three-word-completion/README.md): a finite maximal code `M ⊇ Y` on the same alphabet with finite sets `L`, `R` such that every word has a unique expression `ℓ m₁ ⋯ mⱼ r`. The alphabets of part (a) are finite types of a fixed universe. Part (b) holds on any alphabet with two distinct letters, finite or not. [Statement](lean/SmallestNoncompletable/Statement.lean) · [Main theorem](lean/SmallestNoncompletable/MainTheorem.lean)

```lean
def SimultaneousMinimality : Prop :=
  (∀ (A : Type u) [Fintype A] [DecidableEq A] (Y : Finset (Word A)),
      IsUniquelyDecodable (Y : Set (Word A)) →
        (Y.card ≤ 3 ∨ maxLength Y ≤ 3 ∨ totalLength Y ≤ 10) →
          HasPositiveCompletion (Y : Set (Word A))) ∧
    ∀ (A : Type u) [DecidableEq A] (a b : A), a ≠ b →
      IsUniquelyDecodable (Xfinset a b : Set (Word A)) ∧
        (∀ M : Finset (Word A), Xfinset a b ⊆ M → ¬ IsMaximalCode (M : Set (Word A))) ∧
        (Xfinset a b).card = 4 ∧ maxLength (Xfinset a b) = 4 ∧ totalLength (Xfinset a b) = 11

theorem simultaneous_minimality : SimultaneousMinimality.{u}
```

## From the manuscript to Lean

| Step in the manuscript | Lean declarations |
| --- | --- |
| Codes with at most three words: the formalized three-word theorem. | [`small_code_completion`](lean/SmallestNoncompletable/Reductions.lean), with `three_word_positive_completion`, `noncommuting_pair_completion` and `prefix_case` from the three-word library |
| Lemma 3 in the direction used: two partial parsings realize each residual, so a code contains none of its residuals. The closure rules (8). | [`Res`, `Res.realized`, `Res.not_mem`, `Res.of_mem_mem`, `Res.of_mem_res`](lean/SmallestNoncompletable/Residual.lean) |
| Positive certificates (7). | `HasFiniteCertificate.toPositive` from the three-word library |
| Proposition 5: the factors $P$ and $S$ built from $U$, $V$, $H$, $P_2$, $S_2$, $P_3$, $S_3$. The coefficients of $F$ on words of lengths one to three, four to six, and at least seven. | [`pS`, `qS`, `coeff_short`, `coeff_long_words`, `lhs_long`, `prop5`](lean/SmallestNoncompletable/Prop5.lean) |
| Lemma 6: a finite tree whose leaves read every word shortens the code. Its completions transport back through the substitution of leaves. | [`readTree`, `tree_reduction`, `leaves_completion`](lean/SmallestNoncompletable/Reductions.lean), with `completion_substitution` and `leaves_factorization` from the three-word library |
| Lemma 7: for $|W|\ge4$, $\lambda(W)\ge4$ and $\tau(W)\le10$, a reduction applies to $W$. | [`lemma7`, `canonical`](lean/SmallestNoncompletable/Lemma7.lean) · [`Reducible`, `completion_of_reducible`](lean/SmallestNoncompletable/Reductions.lean) |
| The finite calculation for Lemma 7, as a search checked by the kernel. | [`Search.dfs`, `Search.run`](lean/SmallestNoncompletable/SearchDefs.lean) · [`Search.run_sound`](lean/SmallestNoncompletable/SearchSound.lean) · [`Search.profiles_run`, `Search.profile_mem`](lean/SmallestNoncompletable/Profiles.lean) · [certificates](lean/SmallestNoncompletable/Search) · [generator](checks/generate_search.py) |
| Strong induction on $\tau(Y)\le10$ over all finite alphabets. | [`completion_of_totalLength_le_ten`](lean/SmallestNoncompletable/TotalLength.lean) |
| Reutenauer's factorization for the completions met here: a maximal code containing $b$ factors as $1-\chi_M=J(1-a-b)N$ over $\mathbb Q$. | [`sync_of_maximal`](lean/SmallestNoncompletable/Complete.lean) · [`weak_factorization`](lean/SmallestNoncompletable/Residuals.lean) · [`common_factor`](lean/SmallestNoncompletable/CommonFactor.lean) · [`weak_division`](lean/SmallestNoncompletable/WeakDivision.lean) · [`factorization_of_weak`](lean/SmallestNoncompletable/Factorization.lean) · [`exists_factorization`](lean/SmallestNoncompletable/NoCompletion.lean) |
| Restriction to the letters $a,b$. Framed words: the words of $M$ avoiding $bab$, the alternating words of $M$, and the parity of $(ab)^nb^K\in M^*$. | [`pullback`, `mem_star_pullback`](lean/SmallestNoncompletable/Codes.lean) · [`framing`, `mem_Bcode_of_not_hasBab`, `mem_of_alternating`, `even_of_abPow_mem`](lean/SmallestNoncompletable/Facts.lean) |
| Theorems 2 and 4 for $X=Y_{2,2}$: the coefficients on words with at most one $b$, the periodic determinants, and the period of the $ab$-cycle. | [`evalRec_χR_char`, `evalRec_χL_char`, `evalRec_ψ_char`, `evalRec_ρ_char`](lean/SmallestNoncompletable/Representations.lean) · [`word_identity`](lean/SmallestNoncompletable/Traces.lean) · [`one_add_X_dvd_det`](lean/SmallestNoncompletable/Period.lean) · [`no_binary_code`, `no_finite_maximal_completion`](lean/SmallestNoncompletable/NoCompletion.lean) |
| $X$ is a code, and its three invariants. | [`Xcode_uniquelyDecodable`, `Xfinset_uniquelyDecodable`](lean/SmallestNoncompletable/XCode.lean) · [`X_invariants`, `simultaneous_minimality`](lean/SmallestNoncompletable/MainTheorem.lean) |

## Formalization choices

* **At most three words.** The manuscript adjoins fresh letters to reach three words. Lean completes the empty code and single words as prefix codes, and a two-word code as a noncommuting pair of the three-word library.
* **Reductions.** Lemma 6 is proved for any finite rooted prefix-closed tree through which every word reads back to the root, and the tree of the manuscript is one of them. Lemma 7 concludes that `W` is `Reducible`. Besides Lemma 6 for `W` or its reversal, this allows a prefix code or a suffix code, completed directly, and a letter codeword occurring in no other word next to another letter codeword. The latter is merged into the other letter by a letter map, which lifts completions (`merge_isolated`).
* **The finite calculation.** Enumerating every letter pattern as the manuscript does is beyond the speed of the kernel. The checked search uses a canonical form: the letter codewords come first, the long words are sorted by length, and the letters of the long words are numbered by first appearance, letter codewords and other letters separately. A code with a single long word is prefix-free or has a letter which starts no word (`reducible_of_one_long`), and a code of words of even lengths is shortened by the tree of all letters (`reducible_of_even`). The 14 remaining length profiles are searched in separate modules. Subtrees are pruned when a reduction applies to every completion: a letter which can no longer start or end a long word gives Lemma 6 with the tree $\{\varepsilon,x\}$. The other prunings handle an isolated letter codeword, as many other letters as long words, and a long word repeating earlier words or spelled by them. At a leaf, the search either applies a quick test (repeated word, prefix-free, suffix-free) or checks a certificate: the tree of Lemma 6 computed from $H(W)$ or $H(\operatorname{rev}W)$, or two different parsings of one word. The search visits 38,903 nodes and 9,119 leaves and checks 5,111 certificates. The generator [`checks/generate_search.py`](checks/generate_search.py) recomputes the certificate files. The kernel checks each profile with `decide +kernel` in at most about 12 seconds, and all of them in about a minute.
* **Reutenauer's theorem.** The formalization proves the factorization only for the codes it needs. These contain the letter $b$, so a maximal one contains the synchronizing words $b^Nwb^N$ in $M^*$. The proof follows Berstel, Perrin and Reutenauer, *Codes and Automata*, Section 14.2, from this synchronizing pair, with the common factor theorem (14.3.7) and weak division by $1-a-b$ (14.3.1).
* **Theorems 2 and 4.** Lean proves the case $X=Y_{2,2}$, where $G=\{1\}$, directly. The substitution $a\mapsto0$, $b\mapsto t$ and two triangular representations give the coefficients of $J$ on the words with at most one $b$; their sum on the words with exactly one $b$ is $p(1,1)=|G|=1$. The automaton recognizing the words without the factor $bab$ replaces the cycles $k\notin G$ at once, and the $ab$-cycle is the cycle $k=1$. The determinants of $J$ in both representations equal one, by the determinant identities and the period argument, while the linear coefficients of their traces add up to the same sum, a contradiction.
* **$X$ is a code.** The manuscript obtains unique decipherability from Lemma 3. Lean follows two parsings directly: they start with $b$ and $baaa$, and the dangling suffixes stay in $\{a,aaa,ab,bab\}$.

## Verification

Run `./verify.sh` from the repository root to build all libraries, run the audits and replay the declarations through the Lean kernel. The [audit](checks/Check.lean) prints the statement and its definitions, applies the theorem to $X$ and to three of its words on the binary alphabet, and checks the axioms of the main declarations. Its permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. The search is checked by the kernel with `decide +kernel`, without native code.

To verify the exported proofs with the independent Nanoda kernel, run the following from the repository root.

```sh
lake build SmallestNoncompletable
mkdir -p build
lake env leanexport SmallestNoncompletable.MainTheorem -- SmallestNoncompletable.simultaneous_minimality > build/smallest-noncompletable-code.ndjson
lake env nanoda_bin proofs/smallest-noncompletable-code/checks/nanoda.json
```
