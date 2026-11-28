# Necessary conditions for consecutive positive cubefull integers

Sean Mahdavian (@seanm27lol), with OpenAI Codex assistance, developed the following Lean proofs. Both use the project's pinned Lean 4.33.1 environment and the cubefull definition in formal-conjectures at commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. The unrestricted existence question remains open.

* For an endpoint $2^a$ with $a\ge3$, either cubefull odd neighbor forces an odd prime $p$ dividing that neighbor with $p^3\mid 2^{p-1}-1$. If every prime factor of $a$ is at most 127, then $2^a-1$ cannot be cubefull, even for arbitrarily large $a$. [Lean proof](./PowerTwoObstructions.lean) · [Axiom report](./power-two-axioms.txt)
* Take a normalized candidate in the Mordell-curve reduction [upstream PR #10002](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10002). For each odd prime $p\mid z$, write $e=v_p(z)$ and $t=v_p(D)$. The bound $p^{8e+t}<z^5$ excludes any such prime-power factor $p^e\ge z^{5/8}$. The source also proves a sharper bound involving the radical of $z/p^e$. [Lean proof](./Global.lean) · [Axiom report](./prime-block-axioms.txt)
