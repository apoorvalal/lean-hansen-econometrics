# Lean proof techniques cheat sheet

A compact cheat sheet for the main proof styles you are likely to encounter while working in Lean / Mathlib.

## Big picture

In Lean, a theorem is a term of some type. In practice, proofs are usually written in one of two styles:

1. **term style**
   - compact
   - often reads like “the proof is this object”
   - common tools: `exact`, `refine`, `simpa`

2. **tactic style**
   - interactive / proof-state driven
   - common tools: `intro`, `have`, `rw`, `cases`, `by_contra`, `induction`

Most real proofs mix both.

---

## 1. Direct proof

This is the simplest style: assume hypotheses and directly build the desired conclusion.

```lean
example {u v : ℕ → ℝ} {a b : ℝ}
    (hu : Tendsto u atTop (𝓝 a))
    (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n => u n + v n) atTop (𝓝 (a + b)) := by
  simpa using hu.add hv
```

Typical tools:
- `exact`
- `refine`
- `simpa`
- `apply`

Use this when a theorem already exists in the library and you are just specializing it.

---

## 2. Proof by contradiction

Lean supports classical reasoning. The standard tactic is:

```lean
by_contra h
```

This turns a goal `P` into the assumption `¬ P` and asks you to derive a contradiction.

Example:

```lean
example (h : x ≠ y) : ¬ x = y := by
  by_contra hxy
  exact h hxy
```

Related tools:
- `by_cases h : P`
- `push_neg`
- classical lemmas / excluded middle

Use this when the cleanest mathematical proof is indirect.

---

## 3. Proof by cases

Case splits are extremely common.

```lean
example (P : Prop) : P ∨ ¬ P := by
  by_cases h : P
  · exact Or.inl h
  · exact Or.inr h
```

Typical tools:
- `by_cases`
- `cases`
- `rcases`
- `obtain`

Use this for:
- boolean / proposition splits
- destructuring sums, options, existentials, conjunctions
- branching proofs

---

## 4. Proof by induction

Induction is built in and natural on inductive types like `ℕ`, lists, trees, etc.

```lean
example (n : ℕ) : n + 0 = n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [ih]
```

Typical tools:
- `induction n with`
- recursive definitions / recursive proofs

Use this when the mathematical object is inductively defined.

---

## 5. Constructive existence proofs

If the theorem says “there exists …”, you provide a witness.

```lean
example : ∃ n : ℕ, n = 3 := by
  refine ⟨3, rfl⟩
```

Typical tools:
- `refine ⟨..., ...⟩`
- `use`

Use this when the proof is naturally constructive.

---

## 6. Rewriting proofs

A huge amount of Lean work is just controlled rewriting.

```lean
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by
  rw [h]
```

Typical tools:
- `rw`
- `nth_rewrite`
- `simp`
- `simp_rw`

Use this when the proof is mostly algebraic or definitional.

---

## 7. Building conjunctions and equivalences

For goals of the form `P ∧ Q` or `P ↔ Q`, the standard move is often:

```lean
constructor
```

Example:

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ
```

For `↔`, `constructor` gives two implication goals.

---

## 8. Destructuring assumptions

Lean often stores assumptions as conjunctions / existentials / sigma types. You unpack them with pattern matching.

```lean
example (h : P ∧ Q) : Q ∧ P := by
  rcases h with ⟨hP, hQ⟩
  constructor
  · exact hQ
  · exact hP
```

Typical tools:
- `rcases`
- `cases`
- `rintro`

Use this when hypotheses contain structure you need to unpack.

---

## 9. Automation / solver tactics

Lean has useful automation for routine subproblems.

Examples:
- `simp`
- `aesop`
- `linarith`
- `ring`
- `norm_num`
- `positivity`
- `omega`

Example:

```lean
example (x y : ℝ) (hx : x ≤ y) : x + 1 ≤ y + 1 := by
  linarith
```

Use these to clean up arithmetic / logical boilerplate after the conceptual part of the proof is done.

---

## 10. `calc` proofs

`calc` is great for multi-step equalities / inequalities.

```lean
example (a b c : ℝ) (h₁ : a = b) (h₂ : b = c) : a = c := by
  calc
    a = b := h₁
    _ = c := h₂
```

Use this when you want the proof to read like a paper derivation.

This is especially useful for matrix algebra and measure-theory equalities.

---

## 11. The role of `simpa`

`simpa` is not a proof philosophy; it is just a convenience tactic.

It means roughly:
- apply the given theorem / term,
- simplify the goal and result until they match.

So if a library theorem already has exactly the right mathematical content, `simpa` is often the cleanest finish.

That is why it appears a lot in library-heavy proofs.

---

## 12. How this maps to mathematical proof strategies

- **direct proof** → `exact`, `refine`, `simpa`, `apply`
- **proof by contradiction** → `by_contra`, `by_cases`
- **proof by induction** → `induction`
- **proof by cases** → `cases`, `rcases`, `by_cases`
- **existence proof** → `use`, `refine ⟨..., ...⟩`
- **equivalence / conjunction proofs** → `constructor`
- **algebraic derivation** → `rw`, `simp`, `calc`
- **routine cleanup** → `linarith`, `ring`, `norm_num`, `positivity`

---

## 13. Practical guidance for this Hansen project

So far, the Hansen formalization work has mostly used the **library specialization** style:
- find the right Mathlib theorem
- restate it in Hansen-style notation
- finish with `simpa`, `rw`, or `calc`

As the project moves deeper into Chapter 3 and beyond, we will likely use more:
- `calc` for matrix/algebra derivations
- `have` for local lemmas
- `constructor` for iff / decomposition statements
- `cases` and `rcases` occasionally
- less induction, since econometrics itself is not very induction-heavy

The main bottleneck is usually not “which proof strategy exists?”
The bottleneck is:
- finding the theorem in Mathlib,
- and making Lean accept the exact formulation/rewriting shape.

---

## 14. Bottom line

Lean supports all the familiar proof patterns:
- direct proof
- contradiction
- induction
- cases
- witness construction
- rewriting
- automation-assisted cleanup

`simpa` is just one particularly common finishing move, not the whole game.
