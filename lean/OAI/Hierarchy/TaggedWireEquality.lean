import OAI.Hierarchy.TaggedRadixPins

namespace OAI
/-! # Masked equality cells for named bit turns at a physical site -/

noncomputable section
namespace Hierarchy.WireTelescope.Equality
open ThreeFlat Routing
open scoped BigOperators Classical

abbrev Pins (n : ℕ) := Fin n × Fin 3

/-- Each cell reads a live flag and the two bits sharing this turn. -/
def network (F : Type*) [Zero F] [One F] (n : ℕ) : BitNetwork F (Fintype.card (Pins n)) where
  cells := n
  internal := 0
  source i j := .pin (Fintype.equivFin _ (i,j))
  table _ b := if b 0=true → b 1=b 2 then 1 else 0

theorem eval (F : Type*) [CommSemiring F] {n : ℕ} (x : Pins n→Bool) :
    TypedWiring.value (network F n) x =
      if ∀ i,x (i,0)=true → x (i,1)=x (i,2) then 1 else 0 := by
  simp only [TypedWiring.value,BitNetwork.eval,BitNetwork.weight,BitNetwork.factor,network,
    BitSource.read,Equiv.symm_apply_apply]
  change (∑ _ : Fin 0→Bool, ∏ i : Fin n, if x (i,0)=true → x (i,1)=x (i,2) then (1:F) else 0) = _
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,
    one_nsmul,Fintype.prod_boole]
  split <;> simp_all

variable {P : Type} [Fintype P] {F : Type*} [CommSemiring F]

def listWire (ts : List (P×P)) (ij : Pins ts.length) : P ⊕ Bool :=
  if ij.2=0 then .inr true else if ij.2=1 then .inl (ts.get ij.1).1 else .inl (ts.get ij.1).2

def listNetwork (F : Type*) [Zero F] [One F] (ts : List (P×P)) : BitNetwork F (Fintype.card P) :=
  Tagged.RadixStage.pullPins (network F ts.length) (listWire ts)

def agrees (ts : List (P×P)) (x : P→Bool) : Prop :=
  ∀ t∈ts,x t.1=x t.2

theorem list_eval (ts : List (P×P)) (x : P→Bool) :
    TypedWiring.value (listNetwork F ts) x = if agrees ts x then 1 else 0 := by
  rw [listNetwork,Tagged.RadixStage.pullPins_value,eval]
  congr 1
  apply propext
  have enabled (i : Fin ts.length) : (Sum.elim x id ∘ listWire ts) (i,0)=true := by rfl
  have left (i : Fin ts.length) : (Sum.elim x id ∘ listWire ts) (i,1)=x (ts.get i).1 := by rfl
  have right (i : Fin ts.length) : (Sum.elim x id ∘ listWire ts) (i,2)=x (ts.get i).2 := by rfl
  simp only [enabled,left,right,true_implies]
  constructor
  · intro h t ht
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ht
    exact h i
  · intro h i
    exact h _ (List.get_mem ..)

theorem list_size (ts : List (P×P)) :
    (listNetwork F ts).cells+(listNetwork F ts).internal=ts.length := by
  simp [listNetwork,Tagged.RadixStage.pullPins,network]

end Hierarchy.WireTelescope.Equality

end
end OAI
