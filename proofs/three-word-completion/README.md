# Positive finite completion of three-word codes

Proof by **GPT-6.2 Astra**, supervised by **Christophe Cordero**.

For each three-element uniquely decodable code $X$ on a finite alphabet $A$, there exist finite sets $M,L,R$ of words over $A$ such that $X\subseteq M$, $M$ is maximal among all codes on $A$, and each word has a unique expression $\ell m_1\cdots m_k r$. Uniqueness includes both outside factors and the full list of $M$-words, which may be empty. [Manuscript (PDF)](manuscript/positive_finite_completion_of_three_word_codes.pdf) · [Editable LaTeX](manuscript/positive_finite_completion_of_three_word_codes.tex)

## Use the theorem

```lean
import ThreeWordCodes.MainTheorem

open ThreeWordCodes

example {A : Type*} [Fintype A] (X : Finset (Word A))
    (hsize : X.card = 3)
    (hcode : InformationTheory.IsUniquelyDecodable (X : Set (Word A))) :
    HasPositiveCompletion (X : Set (Word A)) :=
  three_word_positive_completion X hsize hcode
```

The public theorem is `ThreeWordCodes.three_word_positive_completion`. A word is a list of letters. `HasPositiveCompletion X` uses finite sets `M L R` in the order in which the factors appear in the word. Internally, `PositiveFactorization M P Q` assembles a left factor in `Q`, a list of members of `M`, and a right factor in `P`. [Main theorem](lean/ThreeWordCodes/MainTheorem.lean) · [Statement](lean/ThreeWordCodes/Statement.lean) · [Definitions](lean/ThreeWordCodes/Definitions.lean)

## From the manuscript to Lean

| Manuscript | Mathematical step | Lean modules |
| --- | --- | --- |
| §1, Lemma 1 | A nonnegative polynomial certificate yields unique parsing and a finite maximal code. Prefix and suffix completions, substitution, and shortening reduce the problem to binary words. | [Certificate](lean/ThreeWordCodes/Certificate.lean) · [Prefix completion](lean/ThreeWordCodes/Prefix.lean) · [Substitution](lean/ThreeWordCodes/Substitution.lean) · [Binary reduction](lean/ThreeWordCodes/BinaryReduction.lean) |
| §2, Lemmas 2–4 | Marker counts determine gaps and margins. Blocks between short gaps agree. An ambiguous triple of pairwise noncommuting words has an equation-equivalent binary model with a letter entry. | [Uniform gaps](lean/ThreeWordCodes/UniformGaps.lean) · [Short gaps](lean/ThreeWordCodes/ShortGaps.lean) · [Binary normal form](lean/ThreeWordCodes/LetterTheorem.lean) |
| §3, Lemma 5 and Proposition 6 | A tree extension gives a positive certificate and completes every coded triple containing a power of a letter. | [Tree extension](lean/ThreeWordCodes/Graft.lean) · [One-marker construction](lean/ThreeWordCodes/PurePowerTheorem.lean) · [Finite-set corollary](lean/ThreeWordCodes/PureCorollaries.lean) |
| §3, Proposition 7 | The same construction completes the palindromic family used in the border case. | [Reading the palindromic family](lean/ThreeWordCodes/PalindromicReading.lean) · [Proposition 7](lean/ThreeWordCodes/PalindromicTheorem.lean) |
| §4 | Maximal end powers give the border form. A finite suffix comparison and a forbidden commutation rule out the three possible letter positions. | [Border form](lean/ThreeWordCodes/BorderWords.lean) · [Forbidden commutation](lean/ThreeWordCodes/BorderIdentity.lean) · [Border completion](lean/ThreeWordCodes/BorderSecondLetter.lean) |
| §5, rows I–III | The crossed comparisons give four shapes. Row II uses the forced reading of positive gaps at an $ab$ boundary. | [Four shapes](lean/ThreeWordCodes/CrossedForms.lean) · [Row I](lean/ThreeWordCodes/CrossedSharedTheorem.lean) · [Unit gaps](lean/ThreeWordCodes/CrossedUnitGaps.lean) · [Row II](lean/ThreeWordCodes/CrossedIntermediateTheorem.lean) · [Row III](lean/ThreeWordCodes/CrossedDisjointTheorem.lean) |
| §5, row IV | Exchanging letters reduces the one-letter case. A forced $aba$ reading determines the first long-gap block, and Lemma 3 determines all the others. | [Forced reading](lean/ThreeWordCodes/CrossedOverlapBlocks.lean) · [Row IV](lean/ThreeWordCodes/CrossedOverlapTheorem.lean) · [Conclusion](lean/ThreeWordCodes/MainTheorem.lean) |

The coefficient identity used to construct certificates is $[M]+[P][Q]=1+[P][A][Q]$. Some constructions supply these finite polynomial witnesses explicitly. The separate proposition `ThreeWordPolynomialCompletion` formulates this additional certificate requirement for all triples. The general result proved in [MainTheorem.lean](lean/ThreeWordCodes/MainTheorem.lean) gives the maximal code and the unique factorization stated above.

## Examples and verification

The prefix example completes $\{a,ba,bba\}$ by adding $bbb$. The tree-graft example treats $\{a,aba,babaaab\}$, a code with both a prefix comparison and a suffix comparison. [Prefix example](lean/ThreeWordCodes/Example.lean) · [Tree-graft example](lean/ThreeWordCodes/GraftExample.lean)

The [audit](checks/Check.lean) checks the main result and intermediate theorems for transitive dependencies on axioms. Its permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. Run `./verify.sh` from the repository root for the build, examples, audit and Lean kernel replay.

To check the public theorem and its dependencies with the separately implemented Nanoda checker, run the following from the repository root with `leanexport` and `nanoda_bin` available on the toolchain path. The configuration displays the theorem statement and its axioms and checks the full proof term.

```sh
lake build
mkdir -p build
lake env leanexport ThreeWordCodes.MainTheorem -- ThreeWordCodes.three_word_positive_completion > build/three-word-completion.ndjson
lake env nanoda_bin proofs/three-word-completion/checks/nanoda.json
```
