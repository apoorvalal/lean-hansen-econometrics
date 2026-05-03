# FWL Structure Voiceover

Target video:
`animations/media/videos/fwl_structure/1080p15/FWLStructure.mp4`

Output video:
`animations/media/videos/fwl_structure/1080p15/FWLStructure_voiceover.mp4`

The narration follows the proof structure in `HansenEconometrics/Chapter3FWL.lean`.

| start | duration | narration |
|---:|---:|---|
| 0.0 | 5.7 | Here is the formal spine of Frisch Waugh Lovell in Chapter three F W L: compare the full beta two block with the residualized regression. |
| 5.7 | 7.0 | Start with the full regression on from columns X one and X two. The full normal equations split into separate X one and X two blocks. |
| 12.7 | 9.0 | Next build M one, the annihilator for X one. It kills X one, and turns X two and y into the residualized data used by the auxiliary regression. |
| 21.7 | 8.3 | The bridge lemma rewrites the auxiliary residual at the full beta two coefficient as M one applied to the full residual. That is the main algebraic move. |
| 30.0 | 7.0 | Because the full beta two block satisfies those auxiliary normal equations, uniqueness of O L S identifies it with the F W L coefficient. |
| 37.0 | 5.3 | The coefficient identity is then reused to prove the two residual vectors are equal, using the fact that the full residual is already orthogonal to X one. |
| 42.3 | 4.3 | The dependency map shows the proof architecture: block normal equations, annihilator bridges, the auxiliary residual rewrite, then coefficient and residual identities. |
| 46.6 | 4.0 | So the Lean file packages F W L as a chain of reusable theorem-shaped bridges, not as one monolithic calculation. |
