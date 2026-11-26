# Lean submissions to Left to Solve

The site first accepts an exact Lean statement for an unformalized entry. Its checker compiles the statement, then a maintainer reviews the translation. A separate proof or disproof PR can be sent against a merged statement. The PR links below show current review status. All five statement files passed the upstream static checker before submission.

| Entry and local statement | Upstream statement PR | Research note | Proof status at submission |
|---|---|---|---|
| [oeis-a056142](statements/oeis-a056142.lean) | [#444](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/444) | [Three-digit observation and full classification](../notes/03-pal-final.md) | [Candidate disproof](proofs/oeis-a056142.lean) using 121 |
| [oeis-a379181](statements/oeis-a379181.lean) | [#461](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/461) | [Mean equals mode](../notes/02-entropy.md) | Manuscript gives a disproof and a sharper asymptotic |
| [oeis-a383307](statements/oeis-a383307.lean) | [#463](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/463) | [Range equals mode](../notes/06-own.md) | Manuscript gives a proof of the proposed limit |
| [oeis-a346644](statements/oeis-a346644.lean) | [#465](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/465) | [Divisor-average denominator](../notes/07-sequences.md) | Manuscript constructs a witness for every positive denominator |
| [oeis-a309417](statements/oeis-a309417.lean) | [#467](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/467) | [Digit-sum subtraction](../notes/06-own.md) | Manuscript gives a stronger asymptotic step count |

The statement files each contain one `sorry` as required by the catalog's formalization workflow. A proof submission must have none. For A056142, the documented three-digit case and the proof about all greater lengths are separate claims. The Lean disproof uses the three-digit witness only.

The separate [Erdős 1131 repository](https://github.com/seanm27lol/erdos-1131-lean) contains the asymptotic disproof. Its [statement PR #21](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21) is tracked separately from the 83 entries.

[Submission protocol](https://lefttosolve.com/join.txt)
