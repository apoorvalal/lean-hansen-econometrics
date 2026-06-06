theorem foo_same_line (x : Nat) : x = x := rfl

@[simp]
theorem bar_after_attr : True := trivial

private theorem baz_private : True := trivial

noncomputable def myDef : Nat := 0

theorem
    name_on_next_line : True := trivial

@[simp]
theorem
    combo_name : True := trivial

lemma qux_lemma : True := trivial

-- definition_like_word should not be parsed as a decl
