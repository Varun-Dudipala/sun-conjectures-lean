# Two proofs of conjectures of Zhi-Wei Sun

| File | What it is |
|---|---|
| `A189286.lean` | Lean 4 proof of `OeisA189286.conjecture_3`: for $`n \ge 1`$, $`8 \mid a(n)`$, and $`a(n)/8`$ is odd exactly when $`n`$ is a power of 2 |
| `PROOF_A189286.md` | The same proof in prose |
| `A208425_3.lean` | Lean 4 proof of `OeisA208425.conjecture_3`: for primes $`p \equiv 2 \pmod 3`$, $`\sum_{k<p} a(k) \equiv 2p/\binom{2(p+1)/3}{(p+1)/3} \pmod{p^2}`$ |
| `PROOF_A208425.md` | The same proof in prose |
| `check_identities.py` | Numeric test of every numbered formula in the two prose proofs |

The Lean files are the proofs. They were produced by Gemini 4 Carbon and
checked against the statements in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
at commit `6751c0f043985ac6647db28a45a63afdf21acffe`. Both statements were
still tagged open there, and listed as conjectures on OEIS, on 18 November
2026.

## Checking the Lean proofs

Place the two files in a Lake project that depends on `formal-conjectures`
at the commit above, under `Solutions/OEIS/`, and run

```
lake build Solutions.OEIS.A189286 Solutions.OEIS.A208425_3
```

Each file ends with `#print axioms`, which should list only `propext`,
`Classical.choice` and `Quot.sound`.

## Checking the prose

```
python3 check_identities.py
```

This tests cases; it is a guard against a mistyped formula, not a proof.

## What has not been done

No mathematician has read either proof, and the search for earlier proofs
was limited to OEIS, the `formal-conjectures` repository and a web search.
