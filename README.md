# Lean formalization of *Non-acceleration of the heavy-ball method in 1D*

[![Lean verification](https://github.com/kostfoto/Heavy-ball_1d-non-acceleration/actions/workflows/lean.yml/badge.svg)](https://github.com/kostfoto/Heavy-ball_1d-non-acceleration/actions/workflows/lean.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2610.25104-b31b1b.svg)](https://arxiv.org/abs/2610.25104)

This repository contains a Lean 4 and Mathlib formalization accompanying
the paper *Non-acceleration of the heavy-ball method in 1D*.

The formalization covers the main mathematical arguments of Sections 2–5
and Appendix B of the paper.

The complete development is contained in
[`HeavyBall.lean`](HeavyBall.lean).

## Scope of the formalization

### Section 2 — Interpolation and cycles

The formalization establishes the smooth strongly convex interpolation
theorems, including the finite-dimensional interpolation condition and its
one-dimensional specialization, and introduces heavy-ball trajectories
and cycles.

Principal declarations:
- `HeavyBall.theorem_2_2`
- `HeavyBall.theorem_2_2_1d`

### Section 3 — Fourier analysis and primitive modes

The formalization covers the Fourier reduction to the necessary mixed
condition and the characterization of primitive root-of-unity feasibility
in Lemma 3.1, including its binding constraint and angular characterization.

It also verifies Theorem 2.3 and Example 3.2.

Principal declarations:
- `HeavyBall.mixed_condition`
- `HeavyBall.lemma_3_1`
- `HeavyBall.lemma_3_1_binding`
- `HeavyBall.lemma_3_1_ii`
- `HeavyBall.theorem_2_3`
- `HeavyBall.example_3_2`

### Section 4 — One-dimensional cycles

The formalization verifies the one-dimensional cycle construction
in Theorem 4.1, following the explicit sorting and chord-angle
arguments in the paper.

Principal declarations:
- `HeavyBall.paperOrder_strictMono`
- `HeavyBall.paper_eq14`
- `HeavyBall.theorem_4_1`

### Section 5 and Appendix B — Exact counterexample certificate

The counterexample is verified using exact arithmetic.

In particular:
- All nine mixed inequalities are established.
- Every primitive root-of-unity mode is excluded.
- The infinite family of large-period cases is handled through the
  uniform bound of Appendix B.
- The remaining thirteen finite cases are verified algebraically.

The final certificate is:

- `HeavyBall.Counterexample.certificate`

Supporting declarations include:
- `HeavyBall.Counterexample.mixed_condition`
- `HeavyBall.Counterexample.no_pure_mode_large`
- `HeavyBall.Counterexample.finite_table`
- `HeavyBall.Counterexample.pure_mode_excluded`

### Limitations

The deduction of non-acceleration relies on an external result by
Goujaud et al., which has not been independently formalized.

The sufficiency direction of Proposition 5.1 is also not formalized.

Consequently, the development does not constitute a complete
machine-checked verification of every result and external dependency
of the paper.

## Reproducing the verification

### Requirements

- [Git](https://git-scm.com/)
- [elan](https://github.com/leanprover/elan), the Lean toolchain manager

Lean and Mathlib are installed automatically through the project's
configuration.

### Installation and verification

Clone the repository:

```bash
git clone https://github.com/kostfoto/Heavy-ball_1d-non-acceleration.git
cd Heavy-ball_1d-non-acceleration
```

Download the Mathlib cache:

```bash
lake exe cache get
```

Verify the entire formalization:

```bash
lake build
```

Alternatively, check the source directly:

```bash
lake env lean HeavyBall.lean
```

A successful build indicates that Lean has accepted the formalization
under the specified toolchain and dependencies.

### Reproducibility

The project uses:

- Lean: `v4.36.0-rc1`
- Mathlib: `fbc1661a327737928fe9d69b74f7deaa09eecfbc`

The Lean toolchain is specified in `lean-toolchain`, while
`lake-manifest.json` pins the exact dependency revisions.

These files are included in the repository to ensure reproducibility.

Running `lake update` is not required and may change the dependency
versions.

## Proof checking and axioms

The formalization contains no `sorry` or `admit`.

The source includes `#print axioms` commands for the principal
theorems, allowing Lean to report their axiom dependencies.

The intended dependencies are restricted to the standard Lean axioms:

- `propext`
- `Classical.choice`
- `Quot.sound`

These can be inspected by running:

```bash
lake env lean HeavyBall.lean
```

The repository also uses GitHub Actions to automatically verify
compilation. The verification status is displayed at the top of this
README.

## Authors

- Konstantinos Fotopoulos
- Michael Helcig
- Karl Deck
- Jannis Alsbach

## Citation

If you use this formalization, please cite the accompanying paper:

```
@article{fotopoulos2026non,
  title={Non-Acceleration of the Heavy-Ball Method in 1D},
  author={Fotopoulos, Konstantinos and Helcig, Michael and Deck, Karl and Alsbach, Jannis},
  journal={arXiv preprint arXiv:2610.25104},
  year={2026}
}
```


## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
