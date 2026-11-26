# Left to Solve research

Proof manuscripts, literature references, computational checks, and Lean formalizations for 83 entries in [Left to Solve](https://lefttosolve.com/). The work was prepared with OpenAI Codex. Each note identifies the source question and credits earlier results where located.

[Browse all 83 problems](INDEX.md) · [Three proof manuscripts (PDF)](reports/Three_Proofs.pdf) · [Full research report (downloadable HTML)](reports/Left_to_Solve_Research.html) · [Lean submissions](lean/README.md)

## Start with three questions

| Problem | Result in the manuscript |
|---|---|
| [Trimmed eigenvalue sums](notes/01-projection.md) | A variational argument proves the proposed inequality for every nonempty block of eigenvalues of a real positive semidefinite matrix minus a multiple of its diagonal. |
| [Digit mean equals mode](notes/02-entropy.md) | The proposed ratio of 10 fails. The asymptotic count is $C\lambda^n n^{-3/2}$, with $\lambda=9.82786850121986\ldots$. |
| [Palindromic prefix concatenation](notes/03-pal-final.md) | Every word through length two works. At length three exactly the palindromes work. From length four onward exactly the constant words work. |

## Latest results

The [Lean tracker](lean/README.md) records five complete, kernel-checked results from this collection. The latest three establish every divisor-average denominator (A346644), prove the signed Stirling limit (A354478), and refute the proposed digit mean–mode ratio (A379181).

| Written work added after the initial report | Result |
|---|---|
| [Stirling sums](notes/07-sequences.md#signed-error-at-every-fixed-distance-from-the-diagonal) | Signed error and leading constant at each fixed truncation order. |
| [Digit subtraction](notes/06-own.md#a-rate-from-consecutive-decimal-blocks) and [digit range versus mode](notes/06-own.md#an-effective-error-bound-for-a383307) | Rates of convergence for both proposed ratios. |
| [The two factorization problems](notes/06-own.md#exact-exceptional-integers-and-the-common-leading-deficit) | Exact classification of exceptional integers and their common leading counting constant. |
| [Hankel matrices](notes/06-own.md#local-smith-factors-and-denominators-of-every-inverse-entry) | Local Smith exponents and the exact reduced denominator of each inverse entry. |
| [Chebyshev primality](notes/17-chebyshev.md#a-congruence-obstruction-for-the-number-of-prime-factors) | Restrictions on the prime factors of a composite and exhaustive completions for 42,188 prefixes. The full conjecture remains open. |

The downloadable reports preserve the initial research collection.

## Coverage

| Treatment | Entries |
|---|---:|
| Written argument | 44 |
| Counterexample and corrected result | 4 |
| Earlier answer or theorem located | 26 |
| Partial result | 9 |

The index counts catalog entries. One proof can cover several entries. A written argument is a research manuscript. Publication priority, independent peer review, and Lean verification are distinct questions. The [Lean tracker](lean/README.md) records what was actually submitted to the catalog.

## Reproduce the checks

Use Python 3.11 or later. The spectral checks require NumPy and SciPy. The almost-perfect sieve, Chebyshev completion search, and paired-factorization check use SymPy. All other Python scripts use the standard library. From the repository root, run the checks you want to reproduce.

    python checks/digit_growth.py
    python checks/sequences_and_determinants.py
    python checks/four_squares.py
    python checks/eigenvalue_bounds.py
    python checks/almost_perfect_numbers.py 11

Run the Chebyshev completion search with the number of prime factors and the largest permitted prefix prime.

    python checks/chebyshev_completions.py 5 313
    python checks/chebyshev_completions.py 7 67 --audit

The remaining Python checks take no arguments. The final C++17 exhaustive search can be reproduced with:

    c++ -O3 -std=c++17 checks/chebyshev_search.cpp -o chebyshev_search
    ./chebyshev_search 1000000000000

[Recorded verification outputs](verified-output.txt) · [Machine-readable problem index](index.csv)

## Reuse and attribution

The original code and Lean files in this repository are available under the [MIT License](LICENSE). Original research prose is available under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/). Catalog excerpts, source problem statements, and third-party publications retain their existing rights and attribution. The [source notes](SOURCES.md) identify the upstream collections.
