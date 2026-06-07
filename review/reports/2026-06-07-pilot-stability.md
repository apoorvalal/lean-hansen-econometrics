# Pilot stability check — Chapter 10 (2026-06-07)

Two independent runs of the harness on the same two files with no code changes:

- Run 1 (`wf_ca26e873-161`): 15 confirmed findings (1 major, 3 minor, 11 nit)
- Run 2 (`wf_52107a72-598`): 7 confirmed findings (2 major, 1 minor, 4 nit)

LLM reviewers/verifiers are nondeterministic, so the bar is **stable high-signal
findings**, not byte-identical output (see the harness design's success criteria).

## Stable across both runs (the actionable signal)

These appeared in **both** runs (matched by concept, since the runs anchored the
same issue on different decls):

| Finding | Run 1 | Run 2 |
|---|---|---|
| `HigherOrder.lean` has no module docstring | minor (`HigherOrder`) | major (`secondOrder_scaled_probability_transfer`) |
| `Quantiles.lean` has no module docstring | major (`<module>`) | major (`Chapter10Bootstrap.Quantiles`) |
| `bootstrapScalarCDFIndexed` monotonicity duplicates `scalarCDF_mono` (should delegate) | nit/minor | minor |
| `bootstrapScalarCDFIndexed_exists_right_lt_of_lt` should be `private` | nit | nit |

Both runs also independently surfaced the broader **redundancy theme** (the
`bootstrapScalarCDF*` family re-inlines `scalarCDF` instead of delegating) and the
**hygiene theme** (a large population of public same-file `_of_...` / indexed
helpers that have zero cross-file usage and should be `private`).

## Where the runs diverged (the nit tail)

The specific *instances* of the "should be private" pattern differed:

- Run 1 enumerated the `bootstrapScalarCDFIndexed_*` helpers (`_eq_cdf_map`,
  `_level_nonempty_*`, `_level_bddBelow_*`, `_local_right_lt_*`).
- Run 2 enumerated the `lowerCDFQuantile_*` and `bootstrapScalarCDF_*` helpers.

This is **not false positives** — both sets are legitimate; the file simply has
many such helpers, and each run sampled a different subset of a large true
population. Long-identifier nits behaved the same way.

## Conclusion

- **High-signal findings are stable** (both module-docstring gaps + the `scalarCDF`
  delegation redundancy appear in every run). The harness reliably finds the issues
  that matter.
- **The nit tail is coverage-limited, not unstable.** To fully enumerate a large
  pattern (e.g. every should-be-`private` helper), prefer a dedicated single-dimension
  deep pass or a loop-until-dry sweep over relying on a single run.
- The Run-2 mechanical-flag calibration (after the rubric/reviewer tuning committed
  between runs) correctly marked "add module docstring" and "make `private`" as
  `mechanical: true`, where Run 1 had marked them `false`.
