import OAI.Hierarchy.DescentExteriorHopTables
import OAI.Hierarchy.DescentExteriorPrintedCalendar

namespace OAI
/-! # The ordinary and reset shape tables use public calendar data -/

namespace Hierarchy.DescentExteriorReplay.HopTables
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentSixParty
open DescentRelativeContacts DescentHostDirectory DescentHostDegree DescentCommonHost DescentDenseHostOrder
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def ordinaryPitch (k degree : ℕ) := (2^(k+1)-1)*(2^packExponent 20 degree+2)
def ordinaryShape (k degree : ℕ) (digit : Block k) :=
  nodeNumber (k-gainExponent 20 degree) (group (k-gainExponent 20 degree) digit)*
    (2^packExponent 20 degree+2)

def resetPitch {n h : ℕ} (board : NonlinearExpanders.Graph n h) (liveDigits height : ℕ) :=
  (roster board liveDigits height).card

def resetShape {n h : ℕ} (board : NonlinearExpanders.Graph n h) (liveDigits height k g : ℕ)
    (digit : Block k) :=
  let sh:=Node.trunk false ((),((k-g,group (k-g) digit),none))
  if good:sh∈roster board liveDigits height then
    (localRank board liveDigits height ⟨sh,good⟩).val else 0

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail : ℕ}
    {W : MarkedWorld F d P bits} {input : Reached W G q ε S k i z D w hist}
    {ctl : ResetRates G S k D n h C f g cut tail}

theorem ordinary_public (input : Reached W G q ε S k i z D w hist) :
    ordinaryPitch k input.placement.degree=ordinaryPitch k D ∧
    ordinaryShape k input.placement.degree=ordinaryShape k D := by rw [input.branch]; exact ⟨rfl,rfl⟩

private theorem chart_eq {a a' height k g dims dims' h : ℕ} (b : NonlinearExpanders.Graph dims h)
    (c : NonlinearExpanders.Graph dims' h) (dim : dims=dims') (board : HEq b c) (live : a=a') :
    resetPitch b a height=resetPitch c a' height ∧
    resetShape b a height k g=resetShape c a' height k g := by
  subst dims'
  cases eq_of_heq board
  subst a'
  exact ⟨rfl,rfl⟩

/-- Stored literal pitch and shape offsets are identical across all reset
choices at this date, including branches with different occupied host subsets. -/
theorem reset_public (b : ClosedReset input ctl) :
    (roster b.reset.graph (b.reset.k-b.terminals.commonDepth) (GroupStage.depthBound D n f g)).card=
      resetPitch ctl.board k (GroupStage.depthBound D n f g) ∧
    b.localTrunk=resetShape ctl.board k (GroupStage.depthBound D n f g) k g := by
  apply chart_eq b.reset.graph ctl.board b.dimension b.graph
  rw [b.keyWidth,b.commonDepth]
  omega

/-- With a single-date directory the selector, pitch pointer and shape-base
pointer are constant zero-indexed words. Only the sparse reset rank reads depend
on the reached history. -/
theorem one_mode {bw count branches : ℕ} (L : Layout) (slot : Hop)
    (m : Memory bw) (h : Room L slot bw count branches) (scale : ℕ) (offset : Fin branches→ℕ)
    (zero : L.mode.read m 0=0) (stride : L.pitches.read m 0=(scale:Word bw))
    (pointer : L.pointers.read m 0=0) (record : ∀j,L.shapes.read m (j.val:Word bw)=(offset j:Word bw)) :
    (∀i : Fin count,slot.hostBase.read (issued L slot count branches m) (i.val:Word bw)=
      ((i.val*scale:ℕ):Word bw)) ∧
    (∀j : Fin branches,slot.localShape.read (issued L slot count branches m) (j.val:Word bw)=
      (offset j:Word bw)) := by
  simpa only [Nat.cast_mul] using selected L slot h 0 0 (scale:Word bw) (fun j=>(offset j:Word bw))
    zero stride pointer (by intro j; simpa using record j)

end
end Hierarchy.DescentExteriorReplay.HopTables

end OAI
