import OAI.Computability.BorderVNP.CubeIdentity
import OAI.Computability.BorderVNP.TeamScales

/-! # Fixed packet identities for group assignment over a field -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open VPVNP VPVNP.MotifBase

universe u

/-- One admissible cube packet format, chosen before the processor length. -/
structure PacketFormat (F : Type u) [Field F] (n : ℕ) (η : ℝ) where
  /-- Width of a base antipodal word. -/
  b : ℕ
  /-- Number of supply-edge choices. -/
  h : ℕ
  /-- Number of copies of the packet tables. -/
  K : ℕ
  /-- Width of each selected supply edge. -/
  s : ℕ
  /-- The repeated block contains wires. -/
  blockPositive : 0 < h*b
  /-- There is a legal choice of the table copy. -/
  copiesPositive : 1 ≤ K
  /-- The packet implements the ordinary antipodal-wire identity over this field. -/
  identity : BaseIdentity F (@start n) (@stop n) Prod.fst head (fun _ => b) (onEdge s) K h
  /-- Fixed-width selector words fit the prescribed tolerance. -/
  selector : (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤ η*(h*b : ℕ)
  /-- Each selected summand meets the cube-edge width estimate. -/
  width : ∀ σ : Fin h → Edge (n+1), (∑ e, (payload (onEdge s) σ e : ℝ)) ≤
    2*2^n*Real.sqrt (n+1)*(h*b : ℕ)

/-- The fixed shared-to-raw expansion bound used in the group histogram. -/
def PacketFormat.expansion {F : Type u} [Field F] {n : ℕ} {η : ℝ} (p : PacketFormat F n η) :=
  p.h*p.s+MotifWidths.selectorBits p.K (Fintype.card (Edge (n+1))) p.h+1

/-- The local expansion constant pays for every selected bit and its complete selector. -/
theorem PacketFormat.expansion_le {F : Type u} [Field F] {n : ℕ} {η : ℝ} (p : PacketFormat F n η) :
    p.h*p.s+MotifWidths.selectorBits p.K (Fintype.card (Edge (n+1))) p.h ≤
      p.expansion*(2^n*(p.h*p.b)) :=
  (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos (pow_pos (by decide) _) p.blockPositive))

/-- A single power-of-two dimension and positive tolerance suffice for all
fields. Within each field, an admissible packet block can be chosen arbitrarily
large before specifying the native processor length. -/
theorem exists_packet_format :
    ∃ n k : ℕ, ∃ η : ℝ, n+1 = 2^k ∧ 0 < η ∧ 100*(2/Real.sqrt (n+1)+η) < 1/10^6 ∧
      ∀ (F : Type u) [Field F] (B : ℕ), ∃ p : PacketFormat F n η, B ≤ p.h*p.b := by
  obtain ⟨k,η,hη,rate⟩ := TeamScales.exists_cube_dimension
  let n := 2^k-1
  have dim : n+1 = 2^k := by have h := pow_pos (by decide : 0 < 2) k; dsimp only [n]; omega
  have dimR : (n : ℝ)+1 = (2 : ℝ)^k := by exact_mod_cast dim
  refine ⟨n,k,η,dim,hη,?_,?_⟩
  · rw [dimR,Real.sqrt_eq_rpow,div_eq_mul_inv,← Real.rpow_neg (by positivity),
      show -(1/(2:ℝ)) = -1/2 by ring]
    exact rate
  · intro F inst B
    obtain ⟨b,h,K,s,hB,hpos,hK,identity,selector,width⟩ := antipodal_wire_identity F n B η hη
    exact ⟨⟨b,h,K,s,hpos,hK,identity,selector,width⟩,hB⟩

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
