import OAI.Hierarchy.DescentDonorChipLookup
import OAI.Hierarchy.DescentDonorTerrain

namespace OAI
/-! # Actual rooted endpoints for the absorbed original and both demand arms -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.ParentIncidence
open DescentSIMDLookup DescentSixParty DescentHaloWalkRAM DescentSharedCableNames DescentRawCablePanel
open scoped Classical Fin.CommRing
noncomputable section

def pathBits (D : ℕ) := Nat.clog 2 (breadth D+1)

def pathCell (D : ℕ) (side : Bool) (trace : Option (Walk×Walk)) : Cell (pathBits D) :=
  match trace with
  | none=>0
  | some p=>⟨(ActorPath.index D (if side then p.2 else p.1)).val+1,
      (Nat.succ_lt_succ (ActorPath.index D _).isLt).trans_le (Nat.le_pow_clog (by decide) _)⟩

/-- The original and both demand arms can already be internal to a colony.
The walk records their common location in the *first* quotient. -/
def rawIssue (chosen : Bool) (left right : Walk) (born : Option (Fin 6→Walk)) : Fin 11→Option (Walk×Walk) :=
  fun role => Fin.cases (motive := fun _ => Option (Walk × Walk))
    (some (left,if chosen then left else right))
    (fun k => Fin.addCases (motive := fun _ => Option (Walk × Walk))
      (fun i : Fin 2=>born.map (fun f=>(f (demandDst i),f (demandDst i))))
      (fun j : Fin 8=>born.map (fun f=>(f (supplySrc j),f (supplyDst j)))) k) role

@[simp] theorem raw_original (chosen : Bool) (left right : Walk) (born : Option (Fin 6→Walk)) :
    rawIssue chosen left right born 0=some (left,if chosen then left else right) := rfl
@[simp] theorem raw_arm (chosen : Bool) (left right : Walk) (born : Option (Fin 6→Walk)) (i : Fin 2) :
    rawIssue chosen left right born (Fin.succ (Fin.castAdd 8 i))=
      born.map (fun f=>(f (demandDst i),f (demandDst i))) := by simp [rawIssue]
@[simp] theorem raw_supply (chosen : Bool) (left right : Walk) (born : Option (Fin 6→Walk)) (i : Fin 8) :
    rawIssue chosen left right born (Fin.succ (Fin.natAdd 2 i))=
      born.map (fun f=>(f (supplySrc i),f (supplyDst i))) := by simp [rawIssue]

def rawDecode {r D cap d : ℕ} (profile : ℕ) (x : Fin r) (s : Fin cap)
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
    | some edge=>rawIssue selected heads.old (look here remote (edge.neighbor.val+1,x.val)) heads.born

theorem raw_decoded {r D cap d : ℕ} (profile : ℕ) (x : Fin r) (s : Fin cap) (u : Panel r D (2*cap) d)
    (lay : Bool) (reg : Fin (D+1)→Owners.Register r D d)
    (wire : DescentSharedCableNames.Stage.Live D cap) (picked : Bool) :
    rawDecode profile x s (Owners.register lay u) (encode _ (D+1) reg) (DescentSignedCableCodec.encode (some wire)) true picked=
      let here:=Owners.addressed (reg 0)
      let remote:=fun j : Fin D=>Owners.addressed (reg j.succ)
      let heads:=actorHeads cap profile u lay here remote x (s.castLE (by omega))
      rawIssue picked heads.old (look here remote (wire.neighbor.val+1,x.val)) heads.born := by
  simp [rawDecode]

end
end Hierarchy.DescentPacking.PackedMatch.Local.ParentIncidence

namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup DescentPacking.PackedMatch.Local
open scoped Classical
noncomputable section

variable (f : Shape) (profile b slots : ℕ)
def seatDonor (v : Parts f) (x : Fin f.blocks) (t : Fin f.cap) : Donor 3 f.names f.widths :=
  unpackDonor ((encode _ (f.blocks*f.cap)).symm (chip f f.cap profile b slots v) (finProdFinEquiv (x,t)))

def rawAtSeat (s : Shape) (profile b slots : ℕ) (side : Bool) (v : Parts s) (x : Fin s.blocks) (t : Fin s.cap)
    (role : Fin 11) : Cell (ParentIncidence.pathBits s.degree) :=
  let donor:=seatDonor s profile b slots v x t
  let wire:=(encode _ (s.blocks*(2*s.cap))).symm v.cables (finProdFinEquiv (x,t.castLE (by omega)))
  ParentIncidence.pathCell s.degree side
    (ParentIncidence.rawDecode profile x t v.terrain v.owners wire donor.live donor.picked role)

end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
