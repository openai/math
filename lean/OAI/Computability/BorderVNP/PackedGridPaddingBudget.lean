import OAI.Computability.BorderVNP.PackedGridPadding

/-! # Static charge and sparse packet fields for private neighbor padding -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPadding

open Crossing CellSparse Finset
open scoped Classical
variable {D H : ℕ} {P Q : Type} {bits : P → ℕ} [Fintype Q] {N : Network D P bits}
variable {src dst : Q → N.Site} (packing : N.ChannelPacking src dst H) (v : N.Site)
variable (addr : LocalLane (H := H) (src := src) (dst := dst) v → ℕ)

/-- Padding uses a single one-bit truth table. Its scalar packet and static comparison
matrix both have length six. -/
theorem zeroFactor_size (i : ℕ) : (Packet.factor (zeroFactor i)).length = 6 ∧
    (zeroFactor i).staticMass = 6 := ⟨rfl,rfl⟩

/-- The only nonconstant raw field of a zero factor is its actual relative lane address. -/
theorem zeroFactor_fields {U i : ℕ} (h2 : 2 ≤ U) (hi : i ≤ U) :
    Packet.FactorFields (zeroFactor i) U := by
  simp [Packet.FactorFields,zeroFactor,Factor.FieldBound,Factor.TableBound,hi,h2]
  omega

/-- Every stored padding factor meets the bound when its privately stored lane address
does. This statement concerns the actual appended factor list. -/
theorem factors_fields {U : ℕ} (h2 : 2 ≤ U) (ha : ∀ l, addr l ≤ U) :
    ∀ f ∈ factors packing v addr, Packet.FactorFields f U := by
  rintro f hf
  obtain ⟨l,_,rfl⟩ := List.mem_map.mp hf
  exact zeroFactor_fields h2 (ha l)

/-- Summing the actual scalar word lengths and static matrix masses over the stored
padding tests gives six times their number in either metric. -/
theorem factors_cost :
    ((factors packing v addr).map (fun f => (Packet.factor f).length)).sum =
        6*(factors packing v addr).length ∧
      ((factors packing v addr).map Factor.staticMass).sum = 6*(factors packing v addr).length := by
  unfold factors
  generalize (univ.filter (unused packing v)).toList = ls
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,(zeroFactor_size _).1,
      (zeroFactor_size _).2,ih.1,ih.2,Nat.mul_succ]
    omega

/-- An actual Cayley cell sees no more than one outgoing and one incoming bit word
per generator. The private padding list costs at most that many full cable widths. -/
theorem cayley_ends {G J : Type} [Group G] [Fintype G] [Fintype J] (step : J → G) (g : G) :
    Fintype.card {q : G × J // q.1 = g ∨ q.1 * step q.2 = g} ≤ 2 * Fintype.card J := by
  simp only [Fintype.card_subtype,card_eq_sum_ones,sum_filter]
  apply le_trans (b := ∑ q : G × J, ((if q.1 = g then 1 else 0)+(if q.1*step q.2 = g then 1 else 0)))
  · apply sum_le_sum
    intro q _
    by_cases h : q.1 = g <;> by_cases h' : q.1*step q.2 = g <;> simp [h,h']
  rw [sum_add_distrib,Fintype.sum_prod_type_right,Fintype.sum_prod_type_right]
  have ht (j : J) : (∑ x : G, if x*step j = g then 1 else 0) = 1 := by
    calc
      _ = ∑ x : G, if x = g then 1 else 0 :=
        Equiv.sum_comp (Equiv.mulRight (step j)) (fun x => if x = g then 1 else 0)
      _ = _ := by simp
  simp [ht, two_mul]

end Packing.GridPadding

end BorderVNP
end Computability
end OAI
