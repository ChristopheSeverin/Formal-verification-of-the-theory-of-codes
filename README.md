# Code Theory Proofs

A collection of mathematical proofs about variable-length codes. Each entry includes an English manuscript, its editable LaTeX source, and a Lean formalization.

| Theorem | Manuscript | Formal proof |
| --- | --- | --- |
| Every three-word code over a finite alphabet has a finite maximal positively factorizing completion on the same alphabet. | [PDF](proofs/three-word-completion/manuscript/positive_finite_completion_of_three_word_codes.pdf) · [LaTeX](proofs/three-word-completion/manuscript/positive_finite_completion_of_three_word_codes.tex) | [Theorem in Lean](proofs/three-word-completion/lean/ThreeWordCodes/MainTheorem.lean) · [Proof guide](proofs/three-word-completion/README.md) |
| For some nonfree submonoid $M$, each binary word has a unique expression $(ab)^i b^j m a^k(aabb)^l$ with $m\in M$. | [PDF](proofs/nonfree-binary-factor/manuscript/nonfree_factor_of_the_binary_free_monoid.pdf) · [LaTeX](proofs/nonfree-binary-factor/manuscript/nonfree_factor_of_the_binary_free_monoid.tex) | [Theorem in Lean](proofs/nonfree-binary-factor/lean/NonfreeBinaryFactor/MainTheorem.lean) · [Proof guide](proofs/nonfree-binary-factor/README.md) |

## Verify the formal proofs

With Git, Bash and the Lean toolchain manager `elan` installed, run the following command from the repository root.

```sh
./verify.sh
```

The first run uses the public Lean toolchain and the package revisions in [lake-manifest.json](lake-manifest.json). The script builds each library, runs the examples and axiom audits, then replays the declarations of each proof module through the Lean kernel. Once the dependencies are available, `lake build` rebuilds the libraries.

## Rebuild the manuscripts

The PDFs can be read directly. With GNU Make, `latexmk` and a standard pdfLaTeX installation, the following command rebuilds them from their sources.

```sh
make -B papers
```

On Ubuntu, the LaTeX packages used here are `latexmk`, `texlive-latex-extra` and `lmodern`.

## Add a proof

Each theorem has a directory under `proofs/`. Its guide connects the mathematical argument to the Lean declarations. The collection uses one pinned Lean toolchain and one package manifest. [Contribution guide](CONTRIBUTING.md)
