
abbrev Rel α β := α → β → Prop
abbrev EndoRel α := Rel α α

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


inductive ReflTransLab {State Label: Type} (r: State → Label → State → Prop)
: State → List Label → State → Prop where
  | refl (s: State): ReflTransLab r s [] s
  | cons (s1 s2 s3: State) (l12: Label) (l23: List Label):
                   r s1 l12 s2 →
      ReflTransLab r s2 l23 s3 →
      ReflTransLab r s1 (l12 :: l23) s3

theorem List.snoc {State Label: Type} {r: State → Label → State → Prop}:
  ∀ (s1 s2 s3: State) (l12: List Label) (l23: Label),
      ReflTransLab r s1 l12 s2 →
                   r s2 l23 s3 →
      ReflTransLab r s1 (l23 :: l12) s3
:= by sorry
