import Qualification.Utils

structure Lts: Type 1 where mk::
  State: Type
  initial: State
  Label: Type
  trans: State → Label → State → Prop

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
