import OAI.ThreeFlat.Diagonal.PhysicalSeedLayer
import OAI.ThreeFlat.Diagonal.CompressorHalfValues
import OAI.ThreeFlat.Diagonal.NumberedArchiveSites
import OAI.ThreeFlat.Diagonal.TraceCursorOrdinals

namespace OAI
/-! # Numbering the physical seed rows of an arbitrary mounted cursor

A zero-axis seed site uses the binary lane as its row ordinal. Its absolute node ID
also records the archive's chosen initial node offset.
-/

namespace ThreeFlat.Diagonal.NavigationPass
open RAM.NavigationNodeRows

namespace Archive
open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression RAM RAM.NavigationNodeRows PhysicalStage
open CompressorPacking.Native CompressorPacking.Native.ShrinkStage.Halves
open scoped BigOperators Classical
noncomputable section
variable (A : Archive)

/-- The initial rows have no children or motif incidences. Every cursor half carries the relay word. -/
def seedData : LayerData A.seedLayer where
  child _ i := i.elim0
  halfWidth _ := List.replicate (2*A.initialDegree) A.relayWidth
  motifCopies _ := []

def seedRowEquiv {k : ℕ} {U : Type} (number : U ≃ Fin A.axes) (lanes : A.remainingLanes=2^k) :
    (U × BitWord k) ≃ Fin A.initialSites :=
  ((number.prodCongr (tagOrdinal k)).trans finProdFinEquiv).trans
    (finCongr (by rw [initialSites,lanes]))

theorem seedRowEquiv_val {k : ℕ} {U : Type} (number : U ≃ Fin A.axes) (lanes : A.remainingLanes=2^k)
    (u : U × BitWord k) :
    (A.seedRowEquiv number lanes u).val=siteNumber number u := by
  change (tagOrdinal k u.2).val+2^k*(number u.1).val=(number u.1).val*2^k+(tagOrdinal k u.2).val
  ac_rfl

variable {F : Type} [Field F] (B : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k) (low off slots : ℕ)

def cursorSeedSites (ax : k=A.axes) (lanes : A.remainingLanes=2^k) :
    (B.cursorState hk low off slots).ArchiveSites :=
  ⟨A.seedLayer,A.seedRowEquiv (finCongr ax) lanes⟩

theorem cursorSeedSites_ord (ax : k=A.axes) (lanes : A.remainingLanes=2^k)
    (v : (B.cursorState hk low off slots).Site) :
    ((A.cursorSeedSites B hk low off slots ax lanes).ord v).val=B.cursorOrdinal hk low off slots v.1 v.2 :=
  (A.seedRowEquiv_val (finCongr ax) lanes v).trans rfl

theorem cursorSeedSites_numbered (ax : k=A.axes) (lanes : A.remainingLanes=2^k) :
    (A.cursorSeedSites B hk low off slots ax lanes).Numbered := by
  intro v
  exact A.cursorSeedSites_ord B hk low off slots ax lanes v

/-- On the first axis, the lane ordinal is precisely the number stored in the cursor. -/
theorem cursor_zero (ax : k=A.axes) (lanes : A.remainingLanes=2^k) (lane : BitWord k) :
    ((A.cursorSeedSites B hk low off slots ax lanes).ord ((⟨0,by omega⟩:Fin k),lane)).val=
      (tagOrdinal k lane).val := by
  let axis : Fin k := ⟨0,by omega⟩
  refine (A.cursorSeedSites_ord B hk low off slots ax lanes (axis,lane)).trans ?_
  refine (B.cursorOrdinal_eq hk low off slots axis lane).trans ?_
  change 0*2^k+(tagOrdinal k lane).val=(tagOrdinal k lane).val
  simp

theorem cursor_zero_id (ax : k=A.axes) (lanes : A.remainingLanes=2^k) (lane : BitWord k) :
    (A.cursorSeedSites B hk low off slots ax lanes).id ((⟨0,by omega⟩:Fin k),lane)=
      A.cursor.node+(tagOrdinal k lane).val := by
  exact congrArg (A.cursor.node + ·) (A.cursor_zero B hk low off slots ax lanes lane)

end
end Archive
end ThreeFlat.Diagonal.NavigationPass

end OAI
