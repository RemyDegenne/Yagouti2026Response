# Yagouti2026Response

A Lean 4 formalization of *On Response-Adaptive Targeting Strategies for Multi-Treatment
Experiments* (Redouane Yagouti, Rémy Degenne and Emilie Kaufmann, 2026,
[arXiv:2606.17777](https://arxiv.org/abs/2606.17777)), on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4). It follows the layout of
[lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template).

It formalizes the asymptotic theory of the αRTS family of response-adaptive designs: strong
consistency with log-log rates (Theorem 4.1), the asymptotic normality of the allocation
proportions and plug-in targets (Theorem 4.2), the three designs of Section 3, and the
forced-exploration variant αRTS-FE of Section 5 (Theorems 5.1, 5.2 and Corollary 5.3), together
with the limit theorems that the paper cites (a martingale strong law, laws of the iterated
logarithm, a martingale central limit theorem, Anscombe's theorem). Two results are stated in a
corrected form, Lemma 4.5 and Corollary 5.3: see the errata. Every headline result is proved, with
no `sorry`.

- Website: https://RemyDegenne.github.io/Yagouti2026Response/, with the blueprint, the referee site and the
  literature links (which declarations formalize which results of the paper). CI builds it on each
  push to `main`. `scripts/formalize.sh` also commits the literature links, as
  `literature/annotations.jsonl`, when the paper is formalized and after the final bump.
- The paper: `arxiv/`. Errors found in it, with their corrections: `notes/paper-errata.md`.
- The paper's results: `AlphaRAR/YDK2026/`, listed with their status in `formalization.yaml`;
  comparator challenges in `comparator/`.
- Library-shaped material: `AlphaRAR/ForLMLExplore/`, which Tau Ceti workers port to LMLExplore;
  `PAPER_ROADMAP.md` says where each item goes.
- Design decisions and reviews: `notes/` and `maths/`.

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`; its arguments go
to `lake build`.

## Working on it

The workflow is the `formalize-paper` skill of the `lml` Claude Code plugin
([lml-claude](https://github.com/LeanMachineLearning/lml-claude)). The paper is formalized; what is
left is to contribute its library-shaped part. `scripts/formalize.sh`, in a terminal or tmux, tags
`PAPER_ROADMAP.md`, sends the reusable parts to LMLExplore, and once they are merged moves the paper
to the current LMLExplore.
