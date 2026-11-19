# A conjecture of Zhi-Wei Sun on OEIS A189286

**Status of this document.** This is a prose account of a proof that has been
checked by the Lean 4 proof assistant (`Solution.lean` in this directory, against the
statement `OeisA189286.conjecture_3` in Google DeepMind's `formal-conjectures`
library). The Lean file is the proof of record. The prose follows it step by
step. The proof was found by Gemini 4 Carbon; the prose was written by Claude
from the Lean file. Every numbered formula below was tested numerically by
`scripts/check_identities.py`. No mathematician has refereed this text.

## Statement

For $`n \ge 0`$ let

```math
T(k) = \binom{6k}{3k}\binom{3k}{k}, \qquad
N(n) = \sum_{k=0}^{n} T(k)\,T(n-k),
```

```math
D(n) = (2n-1)\binom{3n}{n}, \qquad
a(n) = \frac{N(n)}{D(n)} .
```

The first values are $`a(0),\dots,a(4) = -1,\ 40,\ 696,\ 23408,\ 969496`$.

**Theorem** (conjectured by Zhi-Wei Sun, 19 April 2011). For every $`n \ge 1`$,
$`a(n)`$ is an integer divisible by $`8`$, and $`a(n)/8`$ is odd if and only if $`n`$
is a power of $`2`$.

The proof shows more: the exact power of $`2`$ dividing $`a(n)`$ is

```math
v_2\big(a(n)\big) = s_2(n) + s_2(3n),
```

where $`s_2`$ is the number of ones in the binary expansion.

## Notation and standard facts

For a prime $`p`$, $`v_p(m)`$ is the exponent of $`p`$ in $`m`$ and $`s_p(m)`$ is the
sum of the base $`p`$ digits of $`m`$.

- **Legendre.** $`(p-1)\,v_p(m!) = m - s_p(m)`$.
- **Consequence.** $`(p-1)\,v_p\binom{a+b}{a} = s_p(a)+s_p(b)-s_p(a+b) \ge 0`$.
- **Kummer.** $`v_p\binom{a+b}{a}`$ is the number of $`i \ge 1`$ with
  $`(a \bmod p^i) + (b \bmod p^i) \ge p^i`$.
- $`s_p(pm) = s_p(m)`$.

## Step 1. $`D(n)`$ divides every term of $`N(n)`$

**Claim.** For $`n \ge 1`$ and $`0 \le k \le n`$, $`D(n) \mid T(k)\,T(n-k)`$. Hence
$`D(n) \mid N(n)`$ and $`a(n)`$ is an integer.

Integrality of $`a(n)`$ is Sun's first conjecture on this sequence. It was
proved in T. Adamczewski, *OEIS Open*, arXiv:2608.11941 (2026), by the same
termwise method. It is included here because the Lean file proves it again
from scratch.

It is enough to show $`v_p(D(n)) \le v_p(T(k)) + v_p(T(n-k))`$ for every prime
$`p`$.

**The prime 3.** Since

```math
T(k) = \frac{(6k)!}{(3k)!\,(2k)!\,k!}, \qquad \text{(1.1)}
```

Legendre's formula gives
$`2\,v_3(T(k)) = -s_3(6k) + s_3(3k) + s_3(2k) + s_3(k)`$. As $`s_3(6k) = s_3(2k)`$
and $`s_3(3k) = s_3(k)`$,

```math
v_3\big(T(k)\big) = s_3(k). \qquad \text{(1.3)}
```

Next, $`\binom{2n}{n} = 2(2n-1)\cdot\frac{1}{n}\binom{2n-2}{n-1}`$, and
$`\frac{1}{n}\binom{2n-2}{n-1}`$ is a Catalan number, so

```math
(2n-1) \,\Big|\, \binom{2n}{n}. \qquad \text{(1.2)}
```

Therefore $`D(n)`$ divides $`\binom{2n}{n}\binom{3n}{n} = (3n)!/(n!)^3`$, whose
3-adic valuation is $`\tfrac12\big(3s_3(n) - s_3(3n)\big) = s_3(n)`$. Finally
$`s_3(n) \le s_3(k) + s_3(n-k)`$ because $`v_3\binom{n}{k} \ge 0`$. Altogether

```math
v_3(D(n)) \le s_3(n) \le s_3(k)+s_3(n-k) = v_3\big(T(k)\,T(n-k)\big).
```

**A prime $`p \ne 3`$.** Fix $`i \ge 1`$ and write $`M = p^i`$. For an integer $`j`$
with $`x = j \bmod M`$, Kummer's theorem applied to $`\binom{6j}{3j}`$ and
$`\binom{3j}{j}`$ shows that the contribution of the exponent $`i`$ to
$`v_p(T(j))`$ is

```math
g_M(x) = \big[\,2\,(3x \bmod M) \ge M\,\big] + \big[\,x + (2x \bmod M) \ge M\,\big].
```

Writing $`\theta = x/M`$, the two brackets are
$`\lfloor 6\theta\rfloor - 2\lfloor 3\theta\rfloor`$ and
$`\lfloor 3\theta\rfloor - \lfloor 2\theta\rfloor`$, so
$`g_M(x) = \lfloor 6\theta\rfloor - \lfloor 3\theta\rfloor - \lfloor 2\theta\rfloor`$,
that is

```math
g_M(x) = \begin{cases} 0 & x < M/6,\\ 2 & x \ge 5M/6,\\ 1 & \text{otherwise.}\end{cases} \qquad \text{(1.4)}
```

On the other side, with $`w = n \bmod M`$, the contribution of the exponent $`i`$
to $`v_p(D(n)) = v_p(2n-1) + v_p\binom{3n}{n}`$ is

```math
\big[\,M \mid 2n-1\,\big] + h_M(w), \qquad h_M(w) = \big[\,w + (2w \bmod M) \ge M\,\big].
```

**Lemma.** With $`x = k \bmod M`$, $`y = (n-k) \bmod M`$ and $`w = n \bmod M`$,

```math
\big[\,M \mid 2n-1\,\big] + h_M(w) \;\le\; g_M(x) + g_M(y).
```

*Proof.* If $`M \mid 2n-1`$ then $`p`$ is odd and, being different from $`3`$, is at
least $`5`$, so $`M \ge 5`$. In that case $`w = (M+1)/2`$, $`2w \bmod M = 1`$ and
$`w + 1 < M`$, so $`h_M(w) = 0`$. Thus the left side is at most $`1`$.

Suppose the left side equals $`1`$. Then $`w \ge M/3`$: if $`M \mid 2n-1`$ this is
clear from $`w = (M+1)/2`$; if $`h_M(w) = 1`$ and $`w < M/3`$ then $`2w < M`$ and
$`w + 2w < M`$, a contradiction.

If the right side were $`0`$, then by (1.4) $`x < M/6`$ and $`y < M/6`$, so
$`w = x + y < M/3`$. Hence the right side is at least $`1`$. $`\qquad\blacksquare`$

Summing the lemma over $`i \ge 1`$ gives
$`v_p(D(n)) \le v_p(T(k)) + v_p(T(n-k))`$. This finishes Step 1.

The prime $`3`$ needs its own argument because the lemma fails for $`M = 3`$:
there $`M \mid 2n-1`$ gives $`w = 2`$ and $`h_3(2) = 1`$.

## Step 2. A three-term recurrence for $`N(n)`$

Cancelling factorials in (1.1) gives

```math
(k+1)^2\,T(k+1) = 12\,(6k+1)(6k+5)\,T(k). \qquad \text{(2.1)}
```

Put $`T(k) = 0`$ for $`k < 0`$. Then (2.1) holds for every integer $`k`$: for
$`k = -1`$ the left side has the factor $`(k+1)^2 = 0`$, and for $`k \le -2`$ both
sides vanish.

**Proposition.** For every $`n \ge 0`$,

```math
\begin{aligned}
&(n+2)^3 N(n+2) \;-\; 24\,(2n+3)(18n^2+54n+41)\,N(n+1)\\
&\qquad +\; 20736\,(n+1)(3n+1)(3n+5)\,N(n) \;=\; 0.
\end{aligned} \qquad \text{(2.3)}
```

*Proof.* Define the certificate

```math
G(n,k) = k^2\,T(k)\Big[(2k-3n-6)\,T(n+2-k) + 432\,(3n+4-2k)\,T(n+1-k)\Big].
```

For all integers $`n`$ and $`k`$,

```math
\begin{aligned}
&(n+2)^3\,T(k)\,T(n+2-k) - 24(2n+3)(18n^2+54n+41)\,T(k)\,T(n+1-k)\\
&\qquad + 20736(n+1)(3n+1)(3n+5)\,T(k)\,T(n-k) \;=\; G(n,k+1) - G(n,k).
\end{aligned} \qquad \text{(2.2)}
```

Identity (2.2) is a linear combination of three instances of (2.1). Write
$`E(j) = (j+1)^2T(j+1) - 12(6j+1)(6j+5)T(j)`$, which is zero for every integer
$`j`$. Then the difference of the two sides of (2.2) equals

```math
\begin{aligned}
&-\Big[(2k-3n-4)\,T(n+1-k) + 432(3n+2-2k)\,T(n-k)\Big]E(k)\\
&\qquad +\; (2k+n+2)\,T(k)\,\Big[E(n+1-k) - 432\,E(n-k)\Big],
\end{aligned}
```

as one checks by expanding. Now sum (2.2) over $`k = 0,\dots,n+2`$. On the left,
terms with a negative argument vanish, and the three sums are $`N(n+2)`$,
$`N(n+1)`$ and $`N(n)`$. The right side telescopes to $`G(n,n+3) - G(n,0)`$. Both
are zero: $`G(n,0)`$ has the factor $`k^2`$, and $`G(n,n+3)`$ contains only
$`T(-1)`$ and $`T(-2)`$. $`\qquad\blacksquare`$

## Step 3. The power of 2 in $`N(n)`$

**Digit lemma.** For every $`m \ge 0`$,

```math
s_2(m+1) + v_2(m+1) = s_2(m) + 1. \qquad \text{(3.1)}
```

Adding $`1`$ to $`m`$ turns a block of $`t`$ trailing ones into zeros and the next
zero into a one, and then $`v_2(m+1) = t`$.

**Proposition.** For every $`n \ge 1`$,

```math
v_2\big(N(n)\big) = 3\,s_2(n). \qquad \text{(3.2)}
```

*Proof.* By strong induction. The base cases are $`N(1) = 120 = 2^3\cdot 15`$
and $`N(2) = 31320 = 2^3\cdot 3915`$, and $`s_2(1) = s_2(2) = 1`$.

Let $`m \ge 1`$ and assume (3.2) for $`m`$ and $`m+1`$. Write (2.3), with $`n = m`$,
as $`X + B = A`$, where

```math
\begin{aligned}
X &= (m+2)^3 N(m+2),\\
B &= 20736\,(m+1)(3m+1)(3m+5)\,N(m),\\
A &= 24\,(2m+3)(18m^2+54m+41)\,N(m+1).
\end{aligned}
```

Since $`24 = 2^3\cdot 3`$ and both $`2m+3`$ and $`18m^2+54m+41`$ are odd,

```math
v_2(A) = 3 + 3s_2(m+1) = 6 + 3s_2(m) - 3v_2(m+1),
```

using (3.1). Since $`20736 = 2^8\cdot 81`$,

```math
v_2(B) \ge 8 + v_2(m+1) + 3s_2(m).
```

So $`v_2(A) < v_2(B)`$, and therefore $`v_2(X) = v_2(A - B) = v_2(A)`$. That is,

```math
3v_2(m+2) + v_2\big(N(m+2)\big) = 3 + 3s_2(m+1),
```

and by (3.1) applied to $`m+1`$ the right side is $`3v_2(m+2) + 3s_2(m+2)`$.
Hence $`v_2(N(m+2)) = 3s_2(m+2)`$. $`\qquad\blacksquare`$

## Step 4. Conclusion

Since $`2n-1`$ is odd, Legendre's formula gives

```math
v_2\big(D(n)\big) = v_2\binom{3n}{n} = s_2(n) + s_2(2n) - s_2(3n) = 2s_2(n) - s_2(3n). \qquad \text{(4.1)}
```

By Step 1, $`a(n) = N(n)/D(n)`$ is an integer, and by (3.2) and (4.1)

```math
v_2\big(a(n)\big) = 3s_2(n) - \big(2s_2(n) - s_2(3n)\big) = s_2(n) + s_2(3n).
```

Now $`s_2(n) \ge 1`$, with equality exactly when $`n`$ is a power of $`2`$. And
$`s_2(3n) \ge 2`$, because $`3n`$ is not a power of $`2`$. So $`v_2(a(n)) \ge 3`$,
which says $`8 \mid a(n)`$.

Finally $`a(n)/8`$ is odd exactly when $`v_2(a(n)) = 3`$, that is when
$`s_2(n) = 1`$ and $`s_2(3n) = 2`$. If $`n = 2^j`$ then $`3n = 2^j + 2^{j+1}`$ and
both hold. Conversely $`s_2(n) = 1`$ forces $`n`$ to be a power of $`2`$.
$`\qquad\blacksquare`$

## How the pieces map to `Solution.lean`

| Step | Lean lemma |
|---|---|
| (1.2) | `two_mul_sub_one_dvd_centralBinom` |
| (1.3) and the prime 3 | `padicValNat_three_TNat`, `padicValNat_three_den_le` |
| Lemma for $`p \ne 3`$ | `step_ineq_non_three`, `padicValNat_non_three_den_le` |
| Step 1 | `denNat_dvd_term`, `denNat_dvd_numNat` |
| (2.1), (2.2), (2.3) | `TNat_succ`, `wz_pointwise`, `numNat_recurrence` |
| (3.1), (3.2) | `digits_two_succ_add_val`, `padicValNat_two_numNat` |
| Step 4 | `conjecture_3` |
