

inductive MyNat : Type where
| z : MyNat
| s : MyNat → MyNat

abbrev noConfusionType.{u} (P : Sort u) : MyNat → MyNat → Sort u
| MyNat.z, MyNat.z => P → P
| MyNat.s _, MyNat.z => P
| MyNat.z, MyNat.s _ => P
| MyNat.s a, MyNat.s b => (a = b → P) → P

def noConfusion.{u} (P : Sort u) {x y : MyNat} (h : x = y) : noConfusionType P x y
  := h ▸ ((match x with
  | MyNat.z => id
  | MyNat.s _ => fun h => h rfl) : noConfusionType P x x)

theorem injective {x y : MyNat} (h : MyNat.s x = MyNat.s y) : x = y
  := noConfusion (x = y) h id

theorem neqz {x : MyNat} : ¬MyNat.s x = MyNat.z
  := fun h => noConfusion False h


#print List.rec

inductive Eq2.{u} {α : Sort u} : α → α → Prop where
| refl (a : α) : Eq2 a a

inductive Eq3.{u} {α : Sort u} (a : α) : α → Prop where
| refl : Eq3 a a

#print Eq3.rec

#print Eq.rec
#print Eq2.rec

#check Eq
#print WellFounded.fix
