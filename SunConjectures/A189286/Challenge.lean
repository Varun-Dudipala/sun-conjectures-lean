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
# Challenge: OEIS A189286, Sun's conjecture on divisibility by 8

The definitions and the statement are copied from `FormalConjectures/OEIS/189286.lean` in
google-deepmind/formal-conjectures (commit `6751c0f043985ac6647db28a45a63afdf21acffe`),
declaration `OeisA189286.conjecture_3`. Only that file's imports, attributes, test lemmas and
other conjectures are left out. The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA189286

/-- The term $\binom{6k}{3k}\binom{3k}{k}$ appearing in the sum. -/
def tTerm (k : ℕ) : ℚ := ((6 * k).choose (3 * k) * (3 * k).choose k : ℕ)

/--
The sequence $a(n)$ given by
$\frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}
  \binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}$.
-/
def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (n + 1), tTerm k * tTerm (n - k)) /
    (((2 * (n : ℚ)) - 1) * ((3 * n).choose n : ℚ))

theorem conjecture_3 (n : ℕ) (hn : 0 < n) :
    ∃ m : ℤ, a n = 8 * m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OeisA189286

end
