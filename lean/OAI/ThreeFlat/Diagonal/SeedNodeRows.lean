import OAI.ThreeFlat.Diagonal.InitialMetadataActual
import OAI.ThreeFlat.Diagonal.CursorSeedSites
import OAI.ThreeFlat.RAM.NavigationNodeRows

namespace OAI
/-! # Initial node fields and width rows at their physical addresses -/
namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression RAM RAM.NavigationNodeRows
open CompressorPacking.Native CompressorPacking.Native.ShrinkStage.Halves
open scoped BigOperators Classical Fin.NatCast
noncomputable section
variable (A : Archive)

theorem seed_half_end (r : Fin A.initialSites) (i : Fin (2*A.initialDegree)) :
    A.seedWords 11+8*A.initialDegree*r.val+(4*i.val+2)<A.metadataEnd := by
  have rows : 8*A.initialDegree*(r.val+1)≤8*A.initialDegree*A.initialSites :=
    Nat.mul_le_mul_left _ r.isLt
  have offset : 4*(i.val+1)≤4*(2*A.initialDegree) := Nat.mul_le_mul_left 4 i.isLt
  rw [Nat.mul_add,Nat.mul_one] at rows offset
  change A.initialRecords+7*A.initialSites+8*A.initialDegree*r.val+(4*i.val+2) <
    A.initialRecords+(7+8*A.initialDegree)*A.initialSites
  rw [Nat.add_mul]
  omega

theorem seedWidthStart {W k : ℕ} {U : Type}
    (G : LiftedSlots U A.initialDegree (BitWord k)) (number : U ≃ Fin A.axes) (out : Memory W)
    («meta» : A.InitialNodeMetadata G number (fun _=>A.relayWidth) out)
    (endFit : A.metadataEnd<2^W) (r : Fin A.initialSites) :
    (out (A.seedLayer.incident+r.val*2+1)).val=A.seedWords 11+8*A.initialDegree*r.val := by
  have size := Nat.mul_le_mul_left (8*A.initialDegree) r.isLt.le
  have limit : A.seedWords 11+8*A.initialDegree*r.val<2^W := by
    change A.initialRecords+7*A.initialSites+8*A.initialDegree*r.val<_
    unfold metadataEnd at endFit
    rw [Nat.add_mul] at endFit
    omega
  change (out (A.seedWords 9+r.val*2+1)).val=A.seedWords 11+8*A.initialDegree*r.val
  have h := congrArg Fin.val («meta».halfHeader r 1)
  simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,Fin.val_one,Nat.add_assoc,Fin.val_cast_of_lt limit] using h

/-- S43 reads the actual initial half header and row-width column. Every read lies
inside the immutable seed directory, including the dereferenced width address. -/
theorem InitialNodeMetadata.seedData {W k : ℕ} {U : Type}
    (G : LiftedSlots U A.initialDegree (BitWord k)) (number : U ≃ Fin A.axes) (out : Memory W)
    («meta» : A.InitialNodeMetadata G number (fun _=>A.relayWidth) out)
    (lanes : A.remainingLanes=2^k) (deg : 2*A.initialDegree<2^W)
    (bits : A.relayWidth<2^W) (endFit : A.metadataEnd<2^W) :
    A.seedData.Reads (fun z=>(out z).val) ∧ A.seedData.Below A.metadataEnd (fun z=>(out z).val) := by
  let rows := A.seedRowEquiv number lanes
  have first (r : Fin A.initialSites) : (out (A.seedLayer.incident+r.val*2)).val=2*A.initialDegree := by
    have h := congrArg Fin.val («meta».halfHeader r 0)
    change (out (A.seedWords 9 + r.val*2)).val = 2*A.initialDegree
    simpa only [Matrix.cons_val_zero,Fin.val_zero,Nat.add_zero,Fin.val_cast_of_lt deg] using h
  have next := seedWidthStart A G number out «meta» endFit
  have rowWidth (r : Fin A.initialSites) (i : Fin (2*A.initialDegree)) :
      (out (A.seedWords 11+8*A.initialDegree*r.val+(4*i.val+2))).val=A.relayWidth := by
    let u := rows.symm r
    have same : siteNumber number u=r.val :=
      (A.seedRowEquiv_val number lanes u).symm.trans (congrArg Fin.val (rows.apply_symm_apply r))
    have h := «meta».half u i 2
    change out (A.seedWords 11+((siteNumber number u*(2*A.initialDegree)+i.val)*4+2))=(A.relayWidth:Word W) at h
    rw [same] at h
    have addr : A.seedWords 11+8*A.initialDegree*r.val+(4*i.val+2)=
        A.seedWords 11+((r.val*(2*A.initialDegree)+i.val)*4+2) := by ring
    rw [addr,h,Fin.val_cast_of_lt bits]
  refine ⟨⟨fun _ i=>i.elim0,?_,?_,fun h=>False.elim (h rfl),fun h=>False.elim (h rfl)⟩,
    ⟨fun _ i=>i.elim0,?_,?_,fun h=>False.elim (h rfl),fun h=>False.elim (h rfl)⟩⟩
  · intro r
    simpa only [Archive.seedData,List.length_replicate] using first r
  · intro r i
    let j : Fin (2*A.initialDegree) := ⟨i.val,by simpa only [Archive.seedData,List.length_replicate] using i.isLt⟩
    change (out ((out (A.seedLayer.incident+r.val*2+1)).val+(4*i.val+2))).val = _
    rw [next r]
    exact (rowWidth r j).trans
      (List.getElem_replicate (n := 2*A.initialDegree) (a := A.relayWidth) (i := i.val) i.isLt).symm
  · intro r
    have bound : r.val<A.initialSites := r.isLt
    change A.initialRecords+5*A.initialSites+r.val*2+1<A.initialRecords+(7+8*A.initialDegree)*A.initialSites
    rw [Nat.add_mul]
    omega
  · intro r i
    let j : Fin (2*A.initialDegree) := ⟨i.val,by simpa only [Archive.seedData,List.length_replicate] using i.isLt⟩
    change (out (A.seedLayer.incident+r.val*2+1)).val+(4*i.val+2) < A.metadataEnd
    rw [next r]
    exact A.seed_half_end r j

/-- Both pointers in the node header and every dereferenced width word
lie in S49, which remains live while S43 and S44 are emitted. -/
theorem InitialNodeMetadata.seedFootprint {W k : ℕ} {U : Type}
    (G : LiftedSlots U A.initialDegree (BitWord k)) (number : U ≃ Fin A.axes) (out : Memory W)
    («meta» : A.InitialNodeMetadata G number (fun _=>A.relayWidth) out)
    (lanes : A.remainingLanes=2^k) (deg : 2*A.initialDegree<2^W)
    (bits : A.relayWidth<2^W) (endFit : A.metadataEnd<2^W) :
    A.seedData.Footprint (fun i=>A.initialRecords≤ i ∧ i<A.metadataEnd) (fun z=>(out z).val) := by
  have upper := (InitialNodeMetadata.seedData A G number out «meta» lanes deg bits endFit).2.footprint
  refine ⟨fun _ i=>i.elim0,?_,?_,?_,fun h=>False.elim (h rfl),fun h=>False.elim (h rfl),fun h=>False.elim (h rfl)⟩
  · intro r
    exact ⟨by change A.initialRecords≤A.initialRecords+5*A.initialSites+r.val*2; omega,upper.halves r⟩
  · intro r
    exact ⟨by change A.initialRecords≤A.initialRecords+5*A.initialSites+r.val*2+1; omega,upper.halfPtr r⟩
  · intro r i
    refine ⟨?_,upper.width r i⟩
    rw [seedWidthStart A G number out «meta» endFit r]
    change A.initialRecords≤A.initialRecords+7*A.initialSites+8*A.initialDegree*r.val+(4*i.val+2)
    omega


end
end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
