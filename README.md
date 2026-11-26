# Left to Solve research

Proof manuscripts, literature references, computational checks, and Lean formalizations for 83 entries in [Left to Solve](https://lefttosolve.com/). The work was prepared with OpenAI Codex. Each note identifies the source question and credits earlier results where located.

[Browse all 83 problems](INDEX.md) · [Three proof manuscripts (PDF)](reports/Three_Proofs.pdf) · [Full research report (downloadable HTML)](reports/Left_to_Solve_Research.html) · [Lean submissions](lean/README.md)

## Start with three questions

| Problem | Result in the manuscript |
|---|---|
| [Trimmed eigenvalue sums](notes/01-projection.md) | A variational argument proves the proposed inequality for every nonempty block of eigenvalues of a real positive semidefinite matrix minus a multiple of its diagonal. |
| [Digit mean equals mode](notes/02-entropy.md) | The proposed ratio of 10 fails. The asymptotic count is $C\lambda^n n^{-3/2}$, with $\lambda=9.82786850121986\ldots$. |
| [Palindromic prefix concatenation](notes/03-pal-final.md) | Every word through length two works. At length three exactly the palindromes work. From length four onward exactly the constant words work. |

## Coverage

| Treatment | Entries |
|---|---:|
| Written argument | 44 |
| Counterexample and corrected result | 4 |
| Earlier answer or theorem located | 26 |
| Partial result | 9 |

The index counts catalog entries. One proof can cover several entries. A written argument is a research manuscript. Publication priority, independent peer review, and Lean verification are distinct questions. The [Lean tracker](lean/README.md) records what was actually submitted to the catalog.

## Reproduce the checks

Use Python 3.11 or later. The spectral checks require NumPy and SciPy. The two-prime almost-perfect sieve uses SymPy. All other Python scripts use the standard library. From the repository root, run the checks you want to reproduce.

    python checks/digit_growth.py
    python checks/sequences_and_determinants.py
    python checks/four_squares.py
    python checks/eigenvalue_bounds.py
    python checks/almost_perfect_numbers.py 11

Run each other checks/*.py file with Python without arguments. The final C++17 exhaustive search can be reproduced with:

    c++ -O3 -std=c++17 checks/chebyshev_search.cpp -o chebyshev_search
    ./chebyshev_search 1000000000000

[Recorded outputs of the 13 verification programs](verified-output.txt) · [Machine-readable problem index](index.csv)

## Reuse and attribution

The original code and Lean files in this repository are available under the [MIT License](LICENSE). Original research prose is available under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/). Catalog excerpts, source problem statements, and third-party publications retain their existing rights and attribution. The [source notes](SOURCES.md) identify the upstream collections.
