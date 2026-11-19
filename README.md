# Two proofs of conjectures of Zhi-Wei Sun

Lean 4 proofs of two statements that
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
tags as open research problems.

| Package | Statement | Declaration |
|---|---|---|
| [`SunConjectures/A189286`](SunConjectures/A189286) | For $`n \ge 1`$, $`8 \mid a(n)`$, and $`a(n)/8`$ is odd exactly when $`n`$ is a power of 2 (Sun, 2011) | `OeisA189286.conjecture_3` |
| [`SunConjectures/A208425`](SunConjectures/A208425) | For primes $`p \equiv 2 \pmod 3`$, $`\sum_{k<p} a(k) \equiv 2p/\binom{2(p+1)/3}{(p+1)/3} \pmod{p^2}`$ (Sun, 2016) | `OeisA208425.conjecture_3` |

Both were still tagged open in `formal-conjectures`, and listed as conjectures
on OEIS, on 18 November 2026.

## Layout

Each package follows the [Palomar](https://palomar-registry.org/) layout.

| File | What it is |
|---|---|
| `Challenge.lean` | The definitions and the statement, with `sorry`. Copied verbatim from `formal-conjectures` at commit `6751c0f043985ac6647db28a45a63afdf21acffe`. Imports only Mathlib. |
| `Solution.lean` | The same declarations, proved. |
| `comparator.json` | Names the theorem to compare and the permitted axioms. |
| `formalization.yaml` | Sources, authorship, automation and review status. |
| `README.md` | The proof in prose, step by step, with a table mapping each step to a Lean lemma. |

`scripts/check_identities.py` tests every numbered formula in the two prose
proofs. It is a guard against a mistyped formula, not a proof.

## Building

```
lake exe cache get
lake build
```

The `Challenge` modules contain a deliberate `sorry`, so the build prints two
warnings. The `Solution` modules build without warnings.

## How the proofs were produced and checked

The proofs were found and written by Gemini 4 Carbon working as an autonomous
agent. Claude checked them independently, restated them as standalone
packages, and wrote the prose accounts. See each `formalization.yaml`.

Each `Solution` theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`. No file contains `sorry` outside the two challenges,
`native_decide`, or an added axiom.

## What has not been done

No mathematician has read either proof. The search for earlier proofs was
limited to OEIS, the `formal-conjectures` repository and a web search.

## Licence

Apache-2.0. The definitions and statements are copied from
`formal-conjectures`, which is also Apache-2.0.
