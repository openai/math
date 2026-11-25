import OAI.ThreeFlat.Diagonal.CompressorDemandRank
import OAI.ThreeFlat.Diagonal.CompressorDemandOrdinal

namespace OAI
/-! # Natural-valued reference computations for the physical AB/CD record -/

namespace ThreeFlat.Diagonal.CompressorPacking
open scoped BigOperators Classical
noncomputable section
open Computability.VPVNP.Compression
variable {V H Tag L : Type*} {c d : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable (P : PackingData V H Tag L d c) (code : Arc V H Tag L d c ↪ ℕ)
variable (width : Arc V H Tag L d c → ℕ)

def gatherElements (p : Site V Tag L × Fin d) (h : Fin d) (u : Fin (2^c)) : ℕ :=
  let z := ((Native.tagOrdinal c).symm u,P.slotLabel.symm h)
  if ttAt P p z then width (p,z) else 0

def gatherRanks (m : P.Motif) (dir : Bool) (i : Fin d) (k : Fin (2^c)) : ℕ :=
  let p := P.bundle m
  let u := (Native.tagOrdinal c).symm k
  if acceptedCenter P p dir i u ∧ code (atCenter P p dir i u) < code m.val then 1 else 0

theorem gather_elements (p : Site V Tag L × Fin d) :
    (∑ h, ∑ u, gatherElements P width p h u) = thickWidth P width p := by
  rw [tt_scan]
  let e : BitWord c × H ≃ Fin d × Fin (2^c) :=
    (Equiv.prodComm _ _).trans (Equiv.prodCongr P.slotLabel (Native.tagOrdinal c))
  rw [← Fintype.sum_prod_type' (gatherElements P width p)]
  exact (Fintype.sum_equiv e _ _ (fun z => by simp [gatherElements,e])).symm

theorem gather_ranks (hc : 2 ≤ c) (m : P.Motif) :
    (∑ i, ∑ k, gatherRanks P code m false i k) + (∑ i, ∑ k, gatherRanks P code m true i k) =
      (motifNumbers P code hc m).2.val := by
  rw [motif_position_scan,Fintype.sum_bool,add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Fintype.sum_equiv (Native.tagOrdinal c).symm <;> intro u <;> rfl

theorem gather_pair (hc : 2 ≤ c) (m : P.Motif) :
    let q := 3*(2^c*d)/4
    let total := ∑ h, ∑ u, gatherElements P width (P.bundle m) h u
    let rank := (∑ i, ∑ k, gatherRanks P code m false i k) + ∑ i, ∑ k, gatherRanks P code m true i k
    ![total/q + (if rank < total%q then 1 else 0), width m.val] =
      demandWidth P width (motifNumbers P code hc) m := by
  dsimp only
  rw [gather_elements,gather_ranks P code hc]
  rfl

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
