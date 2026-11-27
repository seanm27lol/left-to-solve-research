# Order 12 research checkpoint, 27 November 2026

Sean Mahdavian (@seanm27lol) and collaborators, with OpenAI Codex assistance. This research continues the order-12 existence work at source commit [4100242ec70236d9ba325564392f6c75f363acb8](https://github.com/seanm27lol/left-to-solve-research/commit/4100242ec70236d9ba325564392f6c75f363acb8).

* [138 partial lines suffice](./138-extension.md). An exact calculation reduces 48 raw histograms to 39. All 1,270 candidate cuts fail with minimum surplus 796. The smallest root-order lower bound is 529/29. Two independent implementations reproduce all five counts. The human argument received an independent cross-check.
* [139 partial lines suffice](./139-extension.md). An exact calculation reduces 23 raw histograms to five. The exceptional grid case has independent ternary-code and incidence-geometric arguments.
* Only the auxiliary ternary pencil and Boolean-grid lemmas have checked Lean modules here. The two full extensions are paper proofs and require the generalized-line-graph classification. This checkpoint does not construct an order-12 plane or prove its nonexistence.
* Run verify_138_profiles.py and verify_139_profiles.py with Python 3 to reproduce both public certificates. The audit folder contains the independent computational checks. Lean 4.33.1 checked the two modules in the code directory. Their printed axiom reports are alongside them.
* The 140–142 extension was previously formalized and prepared in the original project. The 138 and 139 results have not been submitted as upstream proofs in this research turn. The papers cite the prior 143–156 extension proofs and their authors.
