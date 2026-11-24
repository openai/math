import OAI.Computability.VPVNP.CompressorRecordsSelectedArenaDemand
import OAI.Computability.VPVNP.CompressorRecordsShrinkPreimages

/-! # Two-pass native preimage directory following the selected role rows -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.SelectedFinish

open Compression BurstRAM PrimedStackRAM SelectedArena
open scoped Fin.CommRing Classical

variable {a g w : ℕ} (X : State a (packingLaneBits a g)) (term stride : Word w)

/-- The first address after the selected role records, reserved for the new sites' preimage
counts. -/
def countStart := endAddr X term stride
/-- The address immediately after the count column where the directory stores the old site
identifiers. -/
def rowStart := countStart X term stride + ShrinkPreimages.newCount X
/-- The exclusive upper bound of the preimage directory, after space for every old site
identifier. -/
def stop := rowStart X term stride + ShrinkPreimages.oldCount X
/-- Encode the base address of the selected preimage count column as a machine word. -/
def counts : Word w := Fin.ofNat _ (countStart X term stride)
/-- Encode the base address of the selected preimage rows as a machine word. -/
def rows : Word w := Fin.ofNat _ (rowStart X term stride)

private theorem room_vals (room : stop X term stride ≤ 2^w) :
    Fits X term stride ∧ (counts X term stride).val=countStart X term stride ∧
      (rows X term stride).val=rowStart X term stride := by
  have pos : 0 < ShrinkPreimages.oldCount X := Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos _)
  change countStart X term stride+ShrinkPreimages.newCount X+ShrinkPreimages.oldCount X ≤ 2^w at room
  exact ⟨show countStart X term stride < 2^w by omega,Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (show countStart X term stride+ShrinkPreimages.newCount X < 2^w by omega)⟩

theorem areas (p₀ : Fin 14 → Word w) (bit : Word w) (room : stop X term stride ≤ 2^w) :
    ShrinkPreimages.Areas X (shrinkWords X term stride p₀ bit) (counts X term stride) (rows X term stride) := by
  have fit := (room_vals X term stride room).1
  have col := output_column X term stride p₀ bit fit 0
  change ((shrinkWords X term stride p₀ bit) 10).val = placementBase X term stride+0*positions X at col
  apply ShrinkPreimages.Areas.packed (endAddr X term stride) _ room
  change ((shrinkWords X term stride p₀ bit) 10).val + positions X ≤ placementBase X term stride+4*positions X+_
  omega

/-- The chronological RAM reports for clearing the new sites' counts and collecting their
old-site preimages. -/
structure Passes (w : ℕ) where
  /-- Reports of the pass that zeros one preimage count per new site. -/
  clear : List (Report w)
  /-- Reports of the pass that appends each old site's identifier to its selected owner's
  preimage row. -/
  collect : List (Report w)

/-- The memory handed to the collection pass after the counts have been cleared. -/
def Passes.middle (p : Passes w) (m : Memory w) := after m (eventLog p.clear)
/-- The memory after the clearing and collection passes have both run. -/
def Passes.final (p : Passes w) (m : Memory w) := after (p.middle m) (eventLog p.collect)

theorem Passes.after_append (p : Passes w) (m : Memory w) :
    after m (eventLog (p.clear++p.collect)) = p.final m := by
  simp only [Passes.final,Passes.middle,eventLog,List.flatMap_append,after,List.foldl_append]

/-- The public operands for collecting preimages, including the placement data and the
addresses of the counts and rows. -/
abbrev params (shr : Fin 14 → Word w) := ShrinkPreimages.params X shr (counts X term stride) (rows X term stride)

/-- Evidence that the two preimage scans ran, produced the selected layout's directory,
preserved memory outside it, and incurred their stated cost. -/
structure Collected (shr : Fin 14 → Word w) (layout : Bool) (m : Memory w) (p : Passes w) : Prop where
  clear : let C := (template SliceRAM.clearOps 0).instantiate w (fun _ => counts X term stride)
    runSegment C.program 8 (some 0) m (List.replicate (ShrinkPreimages.newCount X) []) = some p.clear
  collect : let C := (template collectPreimage 3).instantiate w (params X term stride shr)
    runSegment C.program 23 (some 0) (p.middle m) (List.replicate (ShrinkPreimages.oldCount X) []) = some p.collect
  preimages : PreimagesAt (params X term stride shr) (ShrinkPreimages.place X layout) (p.final m) (ShrinkPreimages.oldCount X)
  directory : ShrinkPreimages.Directory X layout (counts X term stride) (rows X term stride) (p.final m)
  frame : ∀ j, j < countStart X term stride ∨ stop X term stride ≤ j → p.final m j = m j
  clearEnd : endState (some 0) p.clear = some (Fin.ofNat _ (ShrinkPreimages.newCount X))
  collectEnd : endState (some 0) p.collect = some (Fin.ofNat _ (ShrinkPreimages.oldCount X))
  clearCount : p.clear.length = ShrinkPreimages.newCount X
  collectCount : p.collect.length = ShrinkPreimages.oldCount X
  cost : RAMBuckets.cost Report.probes (p.clear++p.collect) = 2*ShrinkPreimages.newCount X+5*ShrinkPreimages.oldCount X

/-- Both loops start from the live memory left by the selected placement and
role scans. The count clear makes arbitrary old scratch contents harmless. -/
theorem collect (p₀ : Fin 14 → Word w) (bit : Word w) (layout : Bool) (m : Memory w)
    (room : stop X term stride ≤ 2^w)
    (place : ShrinkRAM.PlacementColumns X.slots X.baseIndex (shrinkWords X term stride p₀ bit) layout m) :
    ∃ p, Collected X term stride (shrinkWords X term stride p₀ bit) layout m p := by
  let shr := shrinkWords X term stride p₀ bit
  have hA := areas X term stride p₀ bit room
  obtain ⟨cs,rs,hc,hr,hpre,dir,frame,hce,hre,hcn,hrn,cost⟩ := ShrinkPreimages.build X hA layout m place
  refine ⟨⟨cs,rs⟩,⟨hc,hr,hpre,dir,?_,hce,hre,hcn,hrn,cost⟩⟩
  intro j hj
  apply frame j
  obtain ⟨_,hc',hr'⟩ := room_vals X term stride room
  obtain ⟨_,hN,hC⟩ := hA.dimensions
  let q := params X term stride shr
  change (j < (counts X term stride).val ∨ (counts X term stride).val+(q 2).val ≤ j) ∧
    (j < (rows X term stride).val ∨ (rows X term stride).val+(q 2).val*(q 4).val ≤ j)
  change (q 2).val = ShrinkPreimages.newCount X at hN
  change (q 4).val = ShrinkPreimages.capacity a at hC
  rw [hc',hr',hN,hC,← ShrinkPreimages.oldCount_eq X]
  change j<countStart X term stride ∨ countStart X term stride+ShrinkPreimages.newCount X+ShrinkPreimages.oldCount X ≤ j at hj
  unfold rowStart
  omega

end CompressorRecords.SelectedFinish

end

end VPVNP
end Computability
end OAI
