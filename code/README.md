# Agda formalization of proof-relevant Maehara interpolation and well-definedness for the Lambek calculus

The main entry point for the development is [Main.agda](./Main.agda).

`Main.agda` imports the formalization in this directory:

- formulae and contexts in `Fma.agda`
- the sequent calculus and equivalence of derivations in `SeqCalc.agda`
- cut admissibility and cut properties in `Cut.agda` and `CutProperties.agda`
- the Maehara interpolation procedure in `Mip.agda`
- the proof-relevant interpolation (cut as a left inverse of mip) in `CutIntrp.agda`
- equivalence of interpolation triples in `IntrpTriples.agda`
- well-definedness of interpolation in `IntrpWellDef.agda`

The well-definedness proof is split into case files under `IntrpWellDefCases/`.

The formalization is implemented in collaboration with Anthropic Claude Opus 4.8 and OpenAI GPT 5.5.

The whole project type-checks in 5 minutes on an M2 Pro MacBook Pro 16-inch with 32GB ram and in 7 minutes on an AMD Ryzen 7 5700X PC with 32GB ram, respectively.

The formalization uses Agda 2.8.0.
