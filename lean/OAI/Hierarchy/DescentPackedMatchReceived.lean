import OAI.Hierarchy.DescentPackedMatchPhysicalOrder
import OAI.Hierarchy.DescentPackedMatchSourceSeat
import OAI.Hierarchy.DescentPackedMatchProfilePass
import OAI.Hierarchy.DescentPackedProfileOrder

namespace OAI
/-! # Each profile digit at an occupied physical matching seat -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSIMDLookup DescentPackedProfileWindow DescentSixParty DescentStageEdgeReceipt
open DescentKernelHistory.BitDescription DescentTerminalEpochDecoder DescentTerminalEpochFlags Computability.BorderVNP.Crossing
open Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {d k H G M w : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {gadget : PoweredGadget F} {price ε : ℝ}
variable (he : 0≤ε) (A : GroupStage W gadget price ε J V k)
  (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "seat" => sourceSeat he A groups hosts hm
local notation "nWords" => 2^(k+1)*(H*chunks G M)
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home

theorem physical_start (s : Shape) (keys : Fin nWords→Cell (s.outputBits*M))
    (counts : Chronology.Counts seat (countIn he A) (fun r=>laneCounts s M (keys r))) (c : ScanColonies he A.stage) :
    PackedProfileCursor.total (ProfileTable.quota s keys) (seat c).1.val+
      localPrefix (laneCounts s M (keys (seat c).1)) (seat c).2 = beforeSource he A groups hosts c := by
  let pos:=seat
  let ranks:=(sourceChart he A groups hosts).trans Fin.valEmbedding
  have same (a b) : Chronology.rank pos a<Chronology.rank pos b ↔ ranks a<ranks b := by
    rw [Chronology.rank_val,Chronology.rank_val]
    exact seatOf_order k (nativeAddress he A.stage) (nativeAddress_legal he A.stage) groups hosts hm a b
  exact (Chronology.address pos (countIn he A) _ counts c).trans
    (before_padded (Chronology.rank pos) ranks (countIn he A) same c)

theorem received (s : Shape) (keys : Fin nWords→Cell (s.outputBits*M)) (base : ℕ) (o : Memory w)
    (stream : ℕ→Cell s.digit) (choice : (A.stage.result he).Choice)
    (counts : Chronology.Counts seat (countIn he A) (fun r=>laneCounts s M (keys r)))
    (pins : ∀q,(stream q).val=profileAt (inputNumber he A groups hosts) ((scannedRows he A.stage).profile choice) q)
    (read : ∀r : Fin nWords,∀a : Fin M,∀j : Fin s.pairs,
      digit s.digit (finProdFinEquiv (a,j)).val (o (base+r.val)).val =
        if j.val<(laneCounts s M (keys r) a).val then
          (stream (PackedProfileCursor.total (ProfileTable.quota s keys) r.val+
            localPrefix (laneCounts s M (keys r)) a+j.val)).val else 0)
    (c : ScanColonies he A.stage) (e : Matched T A.cap (thinList home color c) (thickList home color c)) :
    let j:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
    ∃u : Fin s.pairs, u.val=j ∧
      digit s.digit (finProdFinEquiv ((seat c).2,u)).val (o (base+(seat c).1.val)).val =
        DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩) := by
  let j:=pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e
  have active : j.val < countIn he A c := j.isLt
  have at_:=counts.live c
  let u : Fin s.pairs := ⟨j.val,(active.trans_le (at_.symm.le.trans (Nat.le_of_lt_succ (laneCounts s M _ _).isLt)))⟩
  refine ⟨u,rfl,?_⟩
  rw [read,ite_eq_left (show u.val<(laneCounts s M _ _).val from active.trans_eq at_.symm),
    physical_start he A groups hosts hm s keys counts c,pins]
  exact consumes he A groups hosts choice c e

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
