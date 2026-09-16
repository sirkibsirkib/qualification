import Qualification.Utils

structure Lts: Type 1 where mk::
  State: Type
  initial: State
  Label: Type
  trans: State → Label → State → Prop

def lts1: Lts := {
  State := Nat
  initial := 0
  Label := String
  trans s1 l s2 := s2 = s1+1 ∧ l = "inc"
}


def lts2: Lts := {
  State := String
  initial := "init"
  Label := String
  trans _ l _ := l = "inc"
}

notation lts " # " s1 " —" l "⟶ " s2 => Lts.trans lts s1 l s2

example: (lts1: Lts) # (6: Nat) — "inc" ⟶ (7: Nat) := sorry

example: lts2 # "init" —"inc"⟶ "cool" :=
  sorry

structure Model where mk::
  Fluent: Type
  lts: Lts
  holds: lts.State → Fluent → Prop

structure ConAtom (Constant: Type) where
  pred: Constant
  args: List Constant

#print Subtype

def ConModel' (Constant: Type) :=
  { m: Model //
    m.Fluent    = ConAtom Constant
  ∧ m.lts.Label = ConAtom Constant
  }

example: Type 1 := ConModel' String

def Lts.trans_clos (lts: Lts)
: lts.State → List lts.Label → lts.State → Prop :=
  ReflTransLab lts.trans


notation lts "# " s1 "—" l "⟶⋆" s2 => Lts.trans_clos lts s1 l s2
