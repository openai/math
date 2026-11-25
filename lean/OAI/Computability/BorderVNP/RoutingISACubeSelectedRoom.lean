import OAI.Computability.BorderVNP.RoutingISACubeSelectedSize

/-! # A uniform numerical room theorem for the selected native cube arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube BorderVNP.Cube.Physical Filter

/-- Source quantities available before selecting a terminal history. The two
rounded widths are computed by `selected` and never supplied independently. -/
structure Sizes where
  /-- End of the real geometry output. -/
  base : ℕ
  /-- Coordinate alphabet. -/
  symbols : ℕ
  /-- Complete exterior volume allowance, namely the number of teams times the exterior capacity. -/
  traffic : ℕ
  /-- Length-only final cell slots. -/
  cells : ℕ
  /-- Length-only final cable slots. -/
  cables : ℕ
  /-- Emitted literal and shared-row capacity. -/
  maxRows : ℕ
  /-- Actual number of teams. -/
  teams : ℕ
  /-- Host-bank stride. -/
  cellStride : ℕ
  /-- Length-only profile prefix. -/
  profile : ℕ

/-- The exact allocation with the paper's ceiling and its true declaration cap. -/
noncomputable def Sizes.selected (p : Sizes) (n b h K s : ℕ) : Layout :=
  let B := blocksFor (p.traffic:ℝ) (h*b) (p.symbols^(n+1))
  let H := (⟨p.base,p.symbols,n+1,B,p.profile,declarationCap n p.symbols B b h s⟩ :
    CubeHeaderInstall.Inputs)
  ⟨H,n,b,h,K,s,p.cells,p.cables,p.maxRows,p.teams,p.cellStride⟩

/-- A single upper envelope on the eight primitive size numbers of the allocation. -/
def Sizes.Le (p : Sizes) (z : ℕ) : Prop :=
  p.base≤z ∧ p.symbols≤z ∧ p.traffic≤z ∧ p.cells≤z ∧ p.cables≤z ∧ p.maxRows≤z ∧
    p.teams≤z ∧ p.cellStride≤z

/-- One exponent covers every eligible input, independently of the public
allocation, literal contents, team count and realized history. -/
theorem uniform_exponent (n b h K s : ℕ) : ∃ e : ℕ, ∀ (z : ℕ) (p : Sizes), p.Le z →
    (p.selected n b h K s).stop ≤ (z+2)^e := by
  let I := (z : ℕ) × {p : Sizes // p.Le z}
  let z : I → ℕ := Sigma.fst
  let p : I → Sizes := fun i ↦ i.2.val
  have bounded (f : Sizes → ℕ) (H : ∀ i : I, f (p i) ≤ z i) : Poly z (fun i ↦ f (p i)) :=
    ⟨1,fun i ↦ (H i).trans (by simp)⟩
  have real := selected_arena (fun i ↦ (p i).base) (fun i ↦ (p i).symbols) (fun i ↦ (p i).traffic)
    (fun i ↦ (p i).cells) (fun i ↦ (p i).cables) (fun i ↦ (p i).maxRows) (fun i ↦ (p i).teams)
    (fun i ↦ (p i).cellStride) (fun i ↦ (p i).profile) n b h K s
    (bounded _ fun i ↦ i.2.property.1) (bounded _ fun i ↦ i.2.property.2.1)
    (bounded _ fun i ↦ i.2.property.2.2.1) (bounded _ fun i ↦ i.2.property.2.2.2.1)
    (bounded _ fun i ↦ i.2.property.2.2.2.2.1) (bounded _ fun i ↦ i.2.property.2.2.2.2.2.1)
    (bounded _ fun i ↦ i.2.property.2.2.2.2.2.2.1) (bounded _ fun i ↦ i.2.property.2.2.2.2.2.2.2)
  obtain ⟨e,he⟩ := real
  exact ⟨e,fun U P hp ↦ he ⟨U,P,hp⟩⟩

/-- On the diagonal's positive batch sizes, any fixed polynomial envelope on
the true primitive quantities gives room for the whole concrete memory layout.
The cutoff precedes the batch length, public arrays and profile. -/
theorem eventually_selected_word (n b h K s B D E : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ (r : ℕ) (p : Sizes), 1≤r → p.Le (B*(r*t+1)^D) →
      (p.selected n b h K s).stop < 2^((TeamScales.logWidth r t)^(E+2)) := by
  obtain ⟨e,he⟩ := uniform_exponent n b h K s
  filter_upwards [Diagonal.eventually_polynomial_words ((B+2)^e) (D*e) E] with t word
  intro r p hr hp
  let X := (r*t+1)^D
  have pos : 1≤X := Nat.one_le_pow _ _ (by omega)
  have extra : B*X+2≤(B+2)*X := by rw [Nat.add_mul]; omega
  have up := (he _ p hp).trans (Nat.pow_le_pow_left extra e)
  rw [mul_pow] at up
  exact up.trans_lt (by simpa only [X,← pow_mul] using word r hr)

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
