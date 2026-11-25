# JUQLean

This repository formalizes results on Adams-Thiele and justified upper quota (JUQ). The work originates in my M-PREF 2025 paper with Martin Lackner and was developed further in our EC 2026 paper and my PhD thesis.

I wrote the definitions and theorem statements in [Interface.lean](Interface.lean). The proofs were autoformalized with Codex and checked by Lean. They may differ from the arguments in the paper and thesis.

There are only two Lean source files:

- [Interface.lean](Interface.lean): the definitions and statements to review (manually written and checked).
- [Proofs.lean](Proofs.lean): all the supporting proofs, self-contained except for Mathlib (formalised by Codex).

The main results are `AdamsJUQ` and `OnlyAdamsJUQ`: Adams-Thiele satisfies JUQ, and every composite Thiele rule satisfying JUQ globally refines Adams-Thiele. Finite nonempty and infinite sequences are covered. One sequence is fixed across all election sizes. Uniqueness is up to refinement within the composite Thiele class.

Read the short [mathematical note](definitions.pdf) for the necessary definitions, the exact `AdamsJUQ` and `OnlyAdamsJUQ` statements, and references. More details and original proofs are available in the sources cited below. 

## Build

Install [Elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

Lean 4.32.0 and the Mathlib revision are pinned. Mathlib is the only external Lean dependency.

To inspect the main theorem's foundational dependencies:

```sh
printf 'import Interface\n#print axioms JUQLean.OnlyAdamsJUQ\n' | lake env lean --stdin
```

The checked proofs use only `propext`, `Classical.choice`, and `Quot.sound`, with no proof placeholders or additional axioms.

## References

- Oliviero Nardi. *Multi-Winner Voting: Representation, Manipulation, Deliberation*. PhD thesis, TU Wien, 2026. [PDF](https://olinarr.github.io/files/publications/pdf/OlivieroNardiPhD2026.pdf).
- Martin Lackner and Oliviero Nardi. *Avoiding Overrepresentation: Upper Quota Axioms for Committee Voting*. 16th Multidisciplinary Workshop on Advances in Preference Handling (M-PREF 2025), 2025. [PDF](https://olinarr.github.io/files/publications/pdf/LacknerAndNardiMPREF2025.pdf). 
- Anton Baychkov, Martin Lackner, Jan Maly, Oliviero Nardi, and Jannik Peters. *Beyond Lower Quota: Avoiding Overrepresentation in Multi-Winner Voting*. EC 2026. [PDF](https://olinarr.github.io/files/publications/pdf/BaychkovEtAlEC2026.pdf), [ArXiV](https://arxiv.org/abs/2606.19968).

## License

[MIT](LICENSE).
