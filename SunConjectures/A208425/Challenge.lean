/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Varun Dudipala.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Challenge: OEIS A208425, Sun's supercongruence for primes congruent to 2 modulo 3

The definition and the statement are copied from `FormalConjectures/OEIS/208425.lean` in
google-deepmind/formal-conjectures (commit `6751c0f043985ac6647db28a45a63afdf21acffe`),
declaration `OeisA208425.conjecture_3`. Only that file's imports, attributes, test lemmas and
other conjectures are left out. The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA208425

/-- Expansion of $\sum_{n \ge 0} \frac{(3n)!}{n!^3} \frac{x^{2n}}{(1-x)^{3n+1}}$, given by
$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n-k}{k} \binom{n+k}{k}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * (n - k).choose k * (n + k).choose k

theorem conjecture_3 (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 2) :
    ((∑ k ∈ Finset.range p, (a k : ℚ)) -
      (2 * p : ℚ) / ((2 * (p + 1) / 3).choose ((p + 1) / 3) : ℚ)).num % (p ^ 2 : ℤ) = 0 := by
  sorry

end OeisA208425

end
