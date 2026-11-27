# The two largest primes in a five-prime Chebyshev candidate

Let $d<e<a<b<c<2d$ be the remaining sign order from the five-prime analysis, with the negative signs at $d,e$. Under the signed reciprocal equation and all the required and forbidden shift conditions, put $g=\gcd(b-1,c-1)$. Then $K=(b-1)/g$ equals 11 or is at least 13. In particular,

$$
\gcd(b-1,c-1)\le \frac{b-1}{11}.
$$

The unrestricted five-prime case and the full Chebyshev primality conjecture remain open in this work.

| Argument | Conclusion |
|---|---|
| [Top-index classification](top_index_theorem.txt) | The only surviving index below nine gives the family $(7,10,23)$. |
| [Lower-shift test for that family](chebyshev-top-exception.md) | The three lower shifts give a finite cover. None of its 308,878 discriminants is a square. |
| [Further indices](chebyshev-top-indices-9-10.md) | Congruences exclude 9 and 12. They leave one family at 10, whose 5,448,422 discriminants also give zero squares. |
| [Endpoint deficit](endpoint_deficit_theorem.txt) | The deficit $2d-c$ is at least 9, with a bound on $d$ at each fixed deficit. |
| [Shared factors](shared_factor_lemma.txt) | The shared factor in the top modulus admits neither 9 nor 25 as a divisor. |

Sean Mahdavian (@seanm27lol) contributed the model-assisted top-index classification, the endpoint and shared-factor arguments, and their verifiers. The lower-shift elimination and the extension to indices 9, 10 and 12 were developed with Codex for this continuation. The earlier middle-gap certificate supplies $a-e\ge502$. Its pinned revision is [a625736](https://github.com/seanm27lol/left-to-solve-research/blob/a6257364d627cf93ab55c836dea48bce831a587b/notes/chebyshev-joint-shifts.md).

Run these commands from this directory with Python 3.8 or later and assertions enabled.

```sh
python3 verify_top_index.py
python3 verify_endpoint_deficit.py
python3 verify_shared_factor_family.py
python3 verify_top_exception.py
python3 verify_top_indices_9_10.py
```

The named catalog question concerns every integer greater than one. The Lean statement submitted for human review preserves both implications. A prepared reduction has three steps. The first proves that every prime passes, following mathlove’s answer and G. Kós’s observation about monic polynomials. The second proves that any passing integer is 2 or is odd and squarefree. The third asks for the exclusion of odd squarefree composites and remains open. The reduction and the two completed proofs are in [the prepared submissions](../../lean/submissions). [Pedja’s original question](https://math.stackexchange.com/questions/2615963/a-congruence-involving-chebyshev-polynomials) · [Statement PR #9657](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9657)
