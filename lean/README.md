# Lean submissions to Left to Solve

Ten original conjectures from the 83-entry collection have statement pull requests. The site compiles each Lean statement, and a maintainer reviews its fidelity to the source. After the statement merges, a separate PR can prove or disprove it. The table records the latest compiler verdict checked on 26 November 2026. Each PR links to its live status.

| Statement | Upstream PR | Catalog compiler | Written argument |
|---|---|---|---|
| [oeis-a056142](statements/oeis-a056142.lean) | [#444](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/444) | [Passed](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/45907981958) | [Prefix palindromes](../notes/03-pal-final.md). [Candidate disproof](proofs/oeis-a056142.lean) with the witness 121. |
| [oeis-a379181](statements/oeis-a379181.lean) | [#461](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/461) | [Passed](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/45908143524) | [Digit mean equals mode](../notes/02-entropy.md). Disproof and sharper asymptotic. |
| [oeis-a383307](statements/oeis-a383307.lean) | [#463](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/463) | [Passed](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/45908169949) | [Digit range equals mode](../notes/06-own.md). Asymptotic count. |
| [oeis-a346644](statements/oeis-a346644.lean) | [#465](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/465) | [Passed](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/45908193364) | [Divisor-average denominators](../notes/07-sequences.md). Witness construction for every denominator. |
| [oeis-a309417](statements/oeis-a309417.lean) | [#467](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/467) | [Passed](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/45908218616) | [Digit-sum subtraction](../notes/06-own.md). Asymptotic step count. |
| [oeis-a354478](statements/oeis-a354478.lean) | [#493](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/493) | Pending | [Reciprocal signed Stirling numbers](../notes/07-sequences.md). Tail estimate for the signed row sum. |
| [oeis-a122251](statements/oeis-a122251.lean) | [#494](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/494) | Pending | [Hankel determinant numerators](../notes/06-own.md). Prime-by-prime determinant calculation. |
| [oeis-a047946](statements/oeis-a047946.lean) | [#498](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/498) | Pending | [Squares of Fibonacci numbers](../notes/06-own.md). Characteristic roots for both parity cases. |
| [oeis-a347748](statements/oeis-a347748.lean) | [#500](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/500) | Pending | [Factors ending in 4 and 6](../notes/06-own.md). Natural-density proof. |
| [oeis-a348546](statements/oeis-a348546.lean) | [#505](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/505) | Pending | [Factors ending in 3 and 7](../notes/06-own.md). Natural-density proof. |

Each catalog statement has the one `sorry` required for a statement-only submission. Proof files must have none. For A056142, David Wasserman recorded the three-digit case in 2005. The proposed Lean disproof concerns that case. The manuscript separately proves the corrected classification at every greater word length.

The [repository verifier](../.github/workflows/lean.yml) runs the pinned upstream checker on the submitted statements and on candidate proofs against those statements. The upstream catalog still requires its own checker and maintainer review. The remaining entries can be found in the [research index](../INDEX.md).

[Erdős 1131](https://github.com/seanm27lol/erdos-1131-lean) is a separate project. Its [asymptotic statement PR #21](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21) is outside the 83-entry collection.

[Catalog submission protocol](https://lefttosolve.com/join.txt)
