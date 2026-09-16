import Qualification.Utils


-- in each state, the label is input, and the destination is output
structure Lts: Type 1 where mk::
  State: Type
  initial: State
  Label: Type
  trans: State → Label → State → Prop

notation lts " # " s1 " —" l "⟶ " s2 => Lts.trans lts s1 l s2

def Lts.functional (lts: Lts): Prop :=
  ∀ {s s1 s2: lts.State} {l: lts.Label},
    Lts.trans lts s l s1 →
    Lts.trans lts s l s2 →
    s1 = s2

def Lts.total (lts: Lts): Prop :=
  ∀ {s l}, ∃ s', Lts.trans lts s l s'


#print Lts.functional

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


example: (lts1: Lts) # (6: Nat) — "inc" ⟶ (7: Nat) := sorry

example: lts2 # "init" —"inc"⟶ "cool" :=
  sorry

structure Model where mk::
  Fluent: Type
  lts: Lts
  holds: lts.State → Fluent → Prop


def Model.Rule (m1 m2: Model) :=
  m1.lts.State × m1.lts.State →
  m1.lts.Label →
  List m2.lts.Label

-- we are removing your choice of L2 labels
-- L1 labels are exposed but the consequences in M2
-- are encoded in the (M1 × M2) states.
def Model.compose
  (m1 m2: Model)
  (rules: Rule m1 m2)
: Model
:= {
    Fluent := m1.Fluent ⊕ m2.Fluent
    lts := {
      State := m1.lts.State × m2.lts.State
      initial := (m1.lts.initial, m2.lts.initial)
      Label := m1.lts.Label
      trans := megatrans
    }
    holds := λ ⟨s1, s2⟩ f ↦
      match f with
      | .inl f1 => m1.holds s1 f1
      | .inr f2 => m2.holds s2 f2
  }


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
