
abbrev EndoRel α := α → α → Prop

inductive ReflTransGen {α} (r: EndoRel α): EndoRel α where
  | refl (x: α): ReflTransGen r x x
  | snoc (x y z: α):
      ReflTransGen r x y →
                   r y z →
      ReflTransGen r x z

def all_nat: EndoRel Nat := λ _ _ ↦ True

example: ReflTransGen all_nat 0 5 := by
  apply ReflTransGen.snoc (y := 0)
  . exact ReflTransGen.refl 0
  . unfold all_nat
    exact True.intro
