import OAI.Hierarchy.DescentOrdinaryRawSeatWords
import OAI.Hierarchy.DescentDonorTerrain
import OAI.Hierarchy.DescentPackedParentIncidence
import OAI.Hierarchy.DescentScalarOwnerBoardRead

namespace OAI
/-! # Recover both actual endpoint paths from the donor's previous physical words -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.ParentIncidence
open DescentSIMDLookup DescentHaloWalkRAM DescentRawCablePanel DescentSharedCableNames
open DescentSixParty DescentSixParty.StarKeys DescentScalarVenueMask
open scoped Classical Fin.CommRing
noncomputable section
variable {r D cap d loc a c : ℕ}

def decodeRows (profile : ℕ) (x : Fin r) (s : Fin cap)
    (raw : Cell (Owners.inputBits r D (2*cap) d))
    (dir : Cell (((Owners.digits r D d*3)*r)*(D+1)))
    (wire : Cell (DescentSignedCableCodec.width D cap)) (seen selected : Bool) : Fin 11→Option (Walk×Walk) :=
  if !seen then fun _=>none else
    let reg:=(encode ((Owners.digits r D d*3)*r) (D+1)).symm dir
    let here:=Owners.addressed (reg 0)
    let remote:=fun j : Fin D=>Owners.addressed (reg j.succ)
    let old:=splitTerrain raw
    let heads:=actorHeads cap profile old.2 old.1 here remote x (s.castLE (by omega))
    match DescentSignedCableCodec.decode D cap wire with
    | none=>fun _=>none
    | some edge=>issue selected heads.old (look here remote (edge.neighbor.val+1,x.val)) heads.born

theorem decoded (profile : ℕ) (x : Fin r) (s : Fin cap) (u : Panel r D (2*cap) d)
    (lay : Bool) (reg : Fin (D+1)→Owners.Register r D d) (wire : DescentSharedCableNames.Stage.Live D cap) (picked : Bool) :
    decodeRows profile x s (Owners.register lay u) (encode _ (D+1) reg) (DescentSignedCableCodec.encode (some wire)) true picked=
      let here:=Owners.addressed (reg 0);let remote:=fun j : Fin D=>Owners.addressed (reg j.succ)
      let heads:=actorHeads cap profile u lay here remote x (s.castLE (by omega))
      issue picked heads.old (look here remote (wire.neighbor.val+1,x.val)) heads.born := by
  simp [decodeRows]

/-- Eleven adjacent slots, including the two absent arms, use one shared lookup
at each old source. The low bit of a gate handles entirely unoccupied sources. -/
def paths (profile : ℕ) (x : Fin r) (s : Fin cap) (side : Bool)
    (raw : Cell (Owners.inputBits r D (2*cap) d)) (dir : Cell (((Owners.digits r D d*3)*r)*(D+1)))
    (wire : Cell (DescentSignedCableCodec.width D cap)) (gates : Cell 2) : Cell (pathBits D*11) :=
  let bit:=(pair 1 1).symm gates
  encode _ 11 (fun j=>pathCell D side (decodeRows profile x s raw dir wire (flag bit.1) (flag bit.2) j))

def liveGate (donor : Donor loc a c) := pair 1 1 (tag donor.live,tag donor.picked)

theorem paths_read (profile : ℕ) (x : Fin r) (s : Fin cap) (side : Bool) (u : Panel r D (2*cap) d) (lay : Bool)
    (reg : Fin (D+1)→Owners.Register r D d) (wire : DescentSharedCableNames.Stage.Live D cap) (donor : Donor loc a c) (seen : donor.live=true) (j : Fin 11) :
    (encode _ 11).symm (paths profile x s side (Owners.register lay u) (encode _ (D+1) reg)
      (DescentSignedCableCodec.encode (some wire)) (liveGate donor)) j=
      let here:=Owners.addressed (reg 0);let remote:=fun j : Fin D=>Owners.addressed (reg j.succ)
      let heads:=actorHeads cap profile u lay here remote x (s.castLE (by omega))
      pathCell D side (issue donor.picked heads.old (look here remote (wire.neighbor.val+1,x.val)) heads.born j) :=by
  simp only [paths,liveGate,Equiv.symm_apply_apply,flag_tag,seen,decoded]

theorem paths_missing (profile : ℕ) (x : Fin r) (s : Fin cap) (side : Bool)
    (raw : Cell (Owners.inputBits r D (2*cap) d)) (dir : Cell (((Owners.digits r D d*3)*r)*(D+1)))
    (wire : Cell (DescentSignedCableCodec.width D cap)) (donor : Donor loc a c) (no : donor.live=false) (j : Fin 11) :
    (encode _ 11).symm (paths profile x s side raw dir wire (liveGate donor)) j=0 :=by
  simp [paths,liveGate,no,decodeRows,pathCell]
end
end Hierarchy.DescentPacking.PackedMatch.Local.ParentIncidence

end OAI
