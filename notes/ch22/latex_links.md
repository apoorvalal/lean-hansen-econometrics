# Chapter 22 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch22_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 22.1 | Theorem 22.1 Assume 1. Sn (θ) converges in probability to S (θ) uniformly over θ ∈ Θ. 2. θ0 uniquely minimizes S(θ) in the sense that for all ϵ > 0, inf θ:∥θ−θ0∥≥ϵ S(θ) > S(θ0). Then ˆθ − →p θ0 as n → ∞. |  |
| Theorem 22.2 | Theorem 22.2 Uniform Law of Large Numbers (ULLN) Assume 1. (Yi , Xi ) are i.i.d. 2. E ⏐⏐ρ (Y , X , θ) ⏐ ⏐ < ∞ for all θ ∈ Θ. 3. Θ is bounded. 4. For some A < ∞ and α > 0, E ⏐⏐ρ (Y , X , θ1) − ρ (Y , X , θ2) ⏐ ⏐ ≤ A ∥θ1 − θ2∥α for all θ1, θ2 ∈ Θ. Then supθ∈Θ &#124;Sn (θ) − S (θ)&#124;− →p 0. |  |
| Theorem 22.3 | Theorem 22.3 Assume the conditions of Theorem 22.1 hold, plus 1. E ψi  2 < ∞. 2. Q (θ) is continuous in θ ∈ N . 3. For some A < ∞ and α > 0, E  ψi (θ1) − ψi (θ2)  2 ≤ A ∥θ1 − θ2∥α for all θ1, θ2 ∈ N . 4. Q > 0. 5. θ0 is in the interior of Θ. Then as n → ∞, p n (ˆθ − θ0 ) − → d N(0,V ) where V = Q −1ΩQ −1. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
