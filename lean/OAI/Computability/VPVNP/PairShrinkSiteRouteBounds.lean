import OAI.Computability.VPVNP.PairSimulationShrinkMapRowRetention
import OAI.Computability.VPVNP.PairShrinkRoleMapStartReads
import OAI.Computability.VPVNP.PairSimulationShrinkRouteReads

/-!
# Reads of the shrinking site's map header and route

The directory scan loads each occurrence in order. Its selected term address
and the layout selector stay below the end of the same compressor level.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSiteBank

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords DescriptorSpace
open ShrinkVertexImage ShrinkMapImage.Registers MapResidentRows MapResidentInputs
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (i : Fin S.steps)
variable {w g : ℕ} {X : State (oldExponent i) (packingLaneBits (oldExponent i) g)}
variable {sel : X.ShrinkSelection B.shrink} {side : Bool} {mem : Memory w} {level term : Word w}
variable (R : MapRowSource X sel side mem level term) (v : Site X)
variable (j : Fin (order X side v).length) {L : Layout} {cur : ℕ} (H : Word w)

private noncomputable local instance siteEq : DecidableEq X.Base := Classical.decEq _

/-- The native guard may increment the map cursor through its exclusive end. -/
theorem mapRoom :
    firstMap B i R v + (order X side v).length < 2 ^ w := by
  rw [length_eq X side v]
  exact (directory_fit X R.first v R.fit).2

/-- The three external probes on the route before the resident gather. -/
theorem route_below (bound : R.InLevel L cur) (before : levelStart L (cur + 1) ≤ H.val) :
    rowCursor X sel side v mem level term R j < H.val ∧
    term.val + (ordinal X (entry X side v j).1).val * 10 < H.val ∧
    (level + 38).val < H.val := by
  let D := ShrinkResidentLayout.layout X R.first
  have owner : (siteIndex X v).val < D.sites := (siteIndex X v).isLt
  have cap : j.val < capacity (oldExponent i) := j.isLt.trans_eq (length_eq X side v)
  have size := ShrinkResidentLayout.size_eq_rows X R.first true
  have whole := (D.ranges true).2.2.2
  rw [size] at whole
  have count := Nat.mul_le_mul_right (capacity (oldExponent i)) owner
  rw [Nat.succ_mul] at count
  have head := (ShrinkResidentLayout.frame X R.first true R.fit).2.2.2.2.2.2
  change ((D.params (oldExponent i) true w 5).val + (siteIndex X v).val * capacity _ + j.val <
    H.val) ∧ _
  rw [head]
  have full : D.rows true + D.sites * capacity (oldExponent i) ≤ H.val :=
    whole.trans (bound.rowsEnd.trans before)
  have rank := (ordinal X (entry X side v j).1).isLt
  have termTop := bound.termEnd.trans before
  have layoutEnd := bound.headerEnd.trans_le before
  refine ⟨?_, by omega, ?_⟩
  · rw [Nat.add_assoc]
    exact (Nat.add_lt_add_left (Nat.add_lt_add_left cap _) _).trans_le
      ((Nat.add_le_add_left count _).trans full)
  · change (level.val + (38 % (2 ^ w))) % (2 ^ w) < _
    exact (Nat.mod_le ..).trans_lt ((Nat.add_le_add_left (Nat.mod_le ..) _).trans_lt layoutEnd)

/-- The actual route probes stay in the worker's permitted cells. -/
theorem route_worker (bound : R.InLevel L cur) (before : levelStart L (cur + 1) ≤ H.val)
    (room : H.val + 31 < 2 ^ w) :
    SourceTransport.Reads (TerminalLink.workerCell H)
      (routeEvents X sel side v mem level term R j) ∧
    SourceTransport.Writes (fun _ ↦ False) (routeEvents X sel side v mem level term R j) := by
  have safe := route_below B i R v j H bound before
  exact ⟨routeEvents_reads X sel side v mem level term R j (TerminalLink.workerCell H)
    (TerminalLink.workerCell_of_lt room safe.1) (TerminalLink.workerCell_of_lt room safe.2.1)
    (TerminalLink.workerCell_of_lt room safe.2.2),
    routeEvents_noWrites X sel side v mem level term R j⟩

/-- The five reads which reload the map header at this site use worker-readable cells. -/
theorem mapStart_worker (bound : R.InLevel L cur) (before : levelStart L (cur + 1) ≤ H.val)
    (room : H.val + 31 < 2 ^ w) (published : Published mem level
      ((ShrinkResidentLayout.layout X R.first).params (oldExponent i) true w 3)
      ((ShrinkResidentLayout.layout X R.first).params (oldExponent i) true w 5) term 10) :
    SourceTransport.Reads (TerminalLink.workerCell H) (List.replicate 4 .tick ++
      headerEvents mem level ((siteIndex X v).val : Word w)) :=
  ShrinkVertexImage.mapStart_worker_reads B i R v H room (bound.headerEnd.le.trans before)
    (bound.rowsEnd.trans before) published

end PairSimulation.ShrinkSiteBank

end VPVNP
end Computability
end OAI
