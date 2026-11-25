import OAI.Hierarchy.TaggedWideLeafSupport
import OAI.Hierarchy.TaggedWideStack
import OAI.Hierarchy.TaggedWideFreeEdges

namespace OAI
/-! # The four simultaneous assignments on the selected physical board -/

noncomputable section
namespace Hierarchy.Tagged.WideStack.Leaf
open ProtocolStackContraction
open scoped Classical BigOperators
variable {F : Type*} [CommSemiring F] {T E H P : Type} [Fintype T] [Fintype E] [Fintype H] [Fintype P]
    (b : T→Board F) (cap : E→ℕ)

abbrev Pos := (t:T) × (Slot (b t).Group (b t).D × Fin (b t).width)
abbrev Pin (H P : Type) := Pos b ⊕ ((Bool × ((e:E) × Fin (cap e))) ⊕ (H ⊕ P))
abbrev Choice (H P : Type) := (∀i,(b i).Slots) × (PrivatePorts cap × ((H→Bool) × (P→Bool)))

def voltage (z : ∀i,(b i).Slots) : Pos b→Bool := fun q=>z q.1 q.2.1 q.2.2

def write (z : ∀i,(b i).Slots) (y : PrivatePorts cap) (hist : H→Bool) (p : P→Bool) :
    Pin b cap H P→Bool :=
  Sum.elim (voltage b z) (Sum.elim (fun q=>y q.1 q.2.1 q.2.2) (Sum.elim hist p))

def read (d : Pin b cap H P→Bool) : Choice b cap H P :=
  (fun t s j=>d (.inl ⟨t,s,j⟩),fun side e j=>d (.inr (.inl (side,⟨e,j⟩))),
    fun h=>d (.inr (.inr (.inl h))),fun p=>d (.inr (.inr (.inr p))))

def assignment : (Pin b cap H P→Bool) ≃ Choice b cap H P where
  toFun := read b cap
  invFun c := write b cap c.1 c.2.1 c.2.2.1 c.2.2.2
  left_inv d := by
    funext i
    rcases i with ⟨i,s,j⟩ | (⟨b,e,j⟩ | (h | p)) <;> rfl
  right_inv c := by rcases c with ⟨z,y,h,p⟩; rfl

theorem sum_workspace (f : (Pin b cap H P→Bool)→F) :
    (∑d,f d) = ∑ z,∑ y,∑ h : H→Bool,∑ p : P→Bool,f (write b cap z y h p) := by
  calc
    _ = ∑ c : Choice b cap H P,f ((assignment b cap).symm c) :=
      ((assignment b cap (H:=H) (P:=P)).symm.sum_comp f).symm
    _ = _ := by simp only [Choice,Fintype.sum_prod_type]; rfl

variable (live : ∀t,Edge (b t).counts → Fin (b t).width → Prop)

def placed (a : ∀t,(b t).Labels) : ∀t,(b t).Slots :=
  fun t=>encode (b t).place (fun _=>false) (a t)

def supported (z : ∀t,(b t).Slots) := ∀t,Supported (b t).place (live t) (z t)
def bounded (a : ∀t,(b t).Labels) := ∀t e j,a t e j=true→live t e j

omit [Fintype T] in
theorem supported_placed (a : ∀t,(b t).Labels) :
    supported b live (placed b a) ↔ bounded b live a :=
  forall_congr' fun t=>supported_encode (b t).place (live t) (a t)

/-- This is the positive switch contraction before either the output plane
or the private equalities have been summed. The factor may read all four
assignments together. -/
theorem close_workspace (φ : (∀i,(b i).Slots)→PrivatePorts cap→(H→Bool)→(P→Bool)→F)
    (f : (Pin b cap H P→Bool)→F)
    (readout : ∀ z y h p, f (write b cap z y h p) =
      (∏i,(b i).settings.close (z i))*(if supported b live z then φ z y h p else 0)) :
    (∑d,f d) = ∑ a:∀t,(b t).Labels,if bounded b live a then
      ∑y,∑h,∑p,φ (placed b a) y h p else 0 := by
  let pay (z : ∀i,(b i).Slots) := if supported b live z then ∑y,∑h,∑p,φ z y h p else 0
  rw [sum_workspace b cap f]
  calc
    _ = ∑z,(∏i,(b i).settings.close (z i))*
          (if ∀i,Padding (b i).place (fun _=>false) (z i) then pay z else 0) := by
      apply Finset.sum_congr rfl; intro z _
      by_cases good : supported b live z
      · have pad i := padding_of_supported (b i).place (live i) (good i)
        simp only [readout,good,ite_true,pay,ite_eq_left pad,Finset.mul_sum]
      · simp [readout,good,pay]
    _ = ∑ a,pay (placed b a) := contract b pay
    _ = _ := by
      apply Finset.sum_congr rfl; intro a _
      by_cases v : bounded b live a
      · simp [pay,v,(supported_placed b live a).mpr v]
      · have missing : ¬supported b live (placed b a) := fun q=>v ((supported_placed b live a).mp q)
        simp only [pay,ite_eq_right missing,ite_eq_right v]

end Hierarchy.Tagged.WideStack.Leaf

end
end OAI
