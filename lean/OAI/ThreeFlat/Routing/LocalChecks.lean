import OAI.ThreeFlat.Routing.TypedWiring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI
/-! # Deterministic local certificates as addressed bit networks -/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.LocalChecks

variable {P H G F : Type*} [Fintype P] [Fintype H] [Fintype G]
  (port : G → Type*) [∀ g, Fintype (port g)]
  (wire : ∀ g, port g → P ⊕ H) (test : ∀ g, (port g → Bool) → Prop)

def network [Zero F] [One F] : BitNetwork F (Fintype.card P) :=
  TypedWiring.glue (fun g => TypedWiring.localTable fun s => if test g s then 1 else 0) wire

def Accepts (x : P → Bool) (h : H → Bool) : Prop :=
  ∀ g, test g (Sum.elim x h ∘ wire g)

/-- Expose the certificate wires for subsequent data movement. -/
def exposed [Zero F] [One F] : BitNetwork F (Fintype.card (P ⊕ H)) :=
  TypedWiring.glue (fun g => TypedWiring.localTable fun s => if test g s then 1 else 0)
    (fun g k => (Sum.inl (wire g k) : (P ⊕ H) ⊕ Empty))

theorem exposed_value [CommSemiring F] (x : P → Bool) (h : H → Bool) :
    TypedWiring.value (exposed (F := F) port wire test) (Sum.elim x h) =
      if Accepts port wire test x h then 1 else 0 := by
  rw [exposed,TypedWiring.glue_value,Fintype.sum_unique]
  simp only [Sum.elim_inl,TypedWiring.localTable_value]
  by_cases ha : Accepts port wire test x h
  · rw [ite_eq_left ha]
    exact Finset.prod_eq_one (fun g _ => ite_eq_left (ha g))
  · rw [ite_eq_right ha]
    obtain ⟨g,hg⟩ := Classical.not_forall.mp ha
    exact Finset.prod_eq_zero (Finset.mem_univ g) (ite_eq_right hg)

theorem exposed_cells [Zero F] [One F] :
    (exposed (F := F) port wire test).cells = (network (F := F) port wire test).cells := by
  simp [exposed,network]

theorem eval [CommSemiring F] (x : P → Bool) :
    TypedWiring.value (network (F := F) port wire test) x =
      ∑ h : H → Bool, if Accepts port wire test x h then 1 else 0 := by
  rw [network, TypedWiring.glue_value]
  apply Finset.sum_congr rfl
  intro h _
  simp only [TypedWiring.localTable_value]
  by_cases ha : Accepts port wire test x h
  · rw [ite_eq_left ha]
    exact Finset.prod_eq_one (fun g _ => ite_eq_left (ha g))
  · rw [ite_eq_right ha]
    obtain ⟨g,hg⟩ := Classical.not_forall.mp ha
    exact Finset.prod_eq_zero (Finset.mem_univ g) (ite_eq_right hg)

theorem cells [Zero F] [One F] : (network (F := F) port wire test).cells =
    ∑ g, 2^(Fintype.card (port g)) * (Fintype.card (port g) + 2) := by
  simp [network,TypedWiring.localTable,TableCompiler.localTableNetwork_cells]

theorem cells_le [Zero F] [One F] {d : ℕ} (bound : ∀ g, Fintype.card (port g) ≤ d) :
    (network (F := F) port wire test).cells ≤ Fintype.card G * (2^d*(d+2)) := by
  rw [cells]
  calc
    _ ≤ ∑ _g : G, 2^d*(d+2) := Finset.sum_le_sum (fun g _ =>
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (bound g))
        (Nat.add_le_add_right (bound g) 2))
    _ = _ := by simp

theorem eval_of_unique [CommSemiring F] (x : P → Bool) (good : Prop)
    (unique : good → ∃! h, Accepts port wire test x h)
    (sound : ∀ h, Accepts port wire test x h → good) :
    TypedWiring.value (network (F := F) port wire test) x = if good then 1 else 0 := by
  rw [eval]
  by_cases hg : good
  · obtain ⟨h,ok,only⟩ := unique hg
    rw [ite_eq_left hg,Finset.sum_eq_single h]
    · simp [ok]
    · intro h' _ ne
      exact ite_eq_right (fun h'Ok => ne (only _ h'Ok))
    · simp
  · rw [ite_eq_right hg]
    apply Finset.sum_eq_zero
    intro h _
    exact ite_eq_right (fun a => hg (sound h a))

end ThreeFlat.Routing.LocalChecks

end
end OAI
