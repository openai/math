import OAI.Computability.VPVNP.CompressorShrinkResidentLayout

/-! # Linear cost of the shrinking resident-directory phases -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkResidentLayout

open Compression Compression.PackingData PairSimulation.LocalHistory

namespace Layout

/-- All native source calls, including the six published head words. -/
def calls (L : Layout) := 20*L.motifs+2*L.sites+6

/-- Calls plus probes: four units per owner, five per append, two per
cleared counter and two per published head. -/
def charge (L : Layout) := 90*L.motifs+4*L.sites+12

theorem end_eq (L : Layout) : L.endAddr = L.first+20*L.motifs+2*L.sites := by
  dsimp [endAddr,rows,counts,owner,size,radix]
  omega

end Layout

variable {a g : ℕ} (X : State a (packingLaneBits a g))

theorem motif_le_slots :
    (shrinkMotifOrder X).length ≤ ShrinkPreimages.oldCount X * 2^a := by
  let d := 2^a
  let c := Shrink.colors a
  have hQ : pieceCount d c ≤ ShrinkPreimages.capacity a := by
    change 3*(2^c*d)/4 ≤ 2^c*d
    omega
  have count := Fintype.card_congr (ShrinkMotifOrder.stateNumber X)
  rw [Fintype.card_fin] at count
  change Fintype.card X.packingData.Motif ≤ _
  rw [count,ShrinkPreimages.oldCount_eq]
  exact (Nat.mul_le_mul_left (ShrinkPreimages.newCount X*d) hQ).trans_eq (by dsimp only [d]; ac_rfl)

/-- Source charge, total report count, arena size, and dispatcher surcharge
are bounded by the selected level's preexisting size unit. Every resident
worker has at most six public words, so eight extra probes per data report
cover the active dispatch-frame reads. -/
theorem cost_units (first : ℕ) :
    let L := layout X first
    let units := ShrinkPreimages.oldCount X * (2^a+1)
    L.charge ≤ 102*units ∧ L.calls ≤ 26*units ∧
      L.endAddr ≤ first + 20*units ∧ L.charge + 8*L.calls ≤ 310*units := by
  intro L units
  have oldPos : 0 < ShrinkPreimages.oldCount X := Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos _)
  have newBound : L.sites ≤ ShrinkPreimages.oldCount X := by
    rw [ShrinkPreimages.oldCount_eq X]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  have motif : L.motifs ≤ ShrinkPreimages.oldCount X*2^a := motif_le_slots X
  have hunit : units = ShrinkPreimages.oldCount X*2^a + ShrinkPreimages.oldCount X := by
    dsimp [units]; rw [Nat.mul_add,Nat.mul_one]
  have hfirst : L.first = first := rfl
  rw [L.end_eq,hfirst]
  dsimp only [Layout.charge,Layout.calls]
  omega

end CompressorRecords.ShrinkResidentLayout

end VPVNP
end Computability
end OAI
