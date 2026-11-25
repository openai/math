import OAI.Computability.BorderVNP.RoutingISACubeArenaRate
import OAI.Computability.BorderVNP.CubePhysicalDeclarationWords
import OAI.Computability.BorderVNP.CubePhysicalPaddingBalance

/-! # The actual padded cube dimensions in the arena word estimate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube BorderVNP.Cube.Physical

/-- A singleton comes from one ordered pair of labels and one padded bit.
Restricting to pairs which share a symbol can only reduce this cardinality. -/
theorem singleSlots_le (n d blocks bc : ℕ) : Fintype.card (SingleSlot n d blocks bc) ≤ padded n d blocks bc := by
  classical
  have sub := Fintype.card_subtype_le
    (fun p : Label (n+1) d × Label (n+1) d ↦ ¬∀ i, p.1 i ≠ p.2 i)
  have q := Nat.mul_le_mul_right (blocks*bc) sub
  simpa only [SingleSlot,Fintype.card_prod,Fintype.card_fin,Label,Fintype.card_fun,padded,pow_two,
    Nat.mul_comm (blocks*bc)] using q

/-- The declaration cap written in the physical header is bounded in terms
of the actual block count and label alphabet. -/
theorem declaration_le (n d blocks b h s : ℕ) :
    declarationCap n d blocks b h s ≤
      blocks*(d^(n+1))^2*(h*s) + blocks*(h*b)*(d^(n+1))^2 := by
  have count := packet_count n d blocks 1
  have p : Fintype.card (Packet n d blocks) ≤ blocks*(d^(n+1))^2 := by
    simpa only [padded,Nat.mul_one] using (Nat.le_mul_of_pos_right _ (by positivity : 0 < 2^n*1)).trans count
  exact Nat.add_le_add (Nat.mul_le_mul_right (h*s) p) (singleSlots_le n d blocks (h*b))

/-- The selected uniform block count is at most four times the integral
exterior-volume budget. This applies before the summand and profile are chosen. -/
theorem blocksFor_le_four (traffic bc Z : ℕ) :
    blocksFor (traffic:ℝ) bc Z ≤ 4*traffic := by
  unfold blocksFor
  apply Nat.ceil_le.mpr
  push_cast
  by_cases h : bc*Z^2=0
  · have zero : (bc:ℝ)*(Z:ℝ)^2=0 := by exact_mod_cast h
    rw [zero,div_zero]
    positivity
  · have pos : 0 < ((bc*Z^2:ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_of_ne_zero h
    have one : 1 ≤ ((bc*Z^2:ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_of_ne_zero h
    push_cast at pos one
    apply (div_le_iff₀ pos).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left one (show 0 ≤ 4*(traffic:ℝ) by positivity)

variable {ι : Type*} {scale : ι → ℕ}

/-- The geometry allocator supplies the base; the selected square arrays,
declared cap and packet/singleton dimensions need no independent room oracle. -/
theorem selected_arena (base symbols traffic cells cables maxRows teams stride profile : ι → ℕ)
    (n b h K s : ℕ) (addr : Poly scale base) (d : Poly scale symbols) (V : Poly scale traffic)
    (cc : Poly scale cells) (ce : Poly scale cables) (cap : Poly scale maxRows)
    (R : Poly scale teams) (str : Poly scale stride) :
    let B := fun i ↦ blocksFor (traffic i : ℝ) (h*b) ((symbols i)^(n+1))
    let stat := fun i ↦ (⟨base i,symbols i,n+1,B i,profile i,declarationCap n (symbols i) (B i) b h s⟩ :
      CubeHeaderInstall.Inputs)
    Poly scale (fun i ↦ (⟨stat i,n,b,h,K,s,cells i,cables i,maxRows i,teams i,stride i⟩ : Layout).stop) := by
  intro B stat
  have hB : Poly scale B := ((Poly.const 4).mul V).mono (fun i ↦ blocksFor_le_four ..)
  have z := (d.pow (n+1)).pow 2
  have caps : Poly scale (fun i ↦ declarationCap n (symbols i) (B i) b h s) :=
    (((hB.mul z).mul (Poly.const (h*s))).add ((hB.mul (Poly.const (h*b))).mul z)).mono
      (fun i ↦ declaration_le ..)
  exact LengthBounds.arena stat cells cables maxRows teams stride
    ⟨addr,d,Poly.const _,hB,caps,cc,ce,cap,R,str⟩ n b h K s

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
