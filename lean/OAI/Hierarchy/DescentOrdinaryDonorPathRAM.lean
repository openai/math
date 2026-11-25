import OAI.Hierarchy.DescentOrdinaryDonorPathWord
import OAI.Hierarchy.DescentPackedOperandOrigins

namespace OAI
/-! # One packed row program for all signed parent endpoint paths -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.ParentIncidence.PathRAM
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentRawCablePanel
open DescentHaloWalkRAM DescentSharedCableNames DescentSixParty
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def join {a b : ℕ} (x : Cell a) (y : Cell b) : Cell (a+b):=pair a b (x,y)
@[simp] theorem join_zero (a b : ℕ) : join (0:Cell a) (0:Cell b)=0:=by apply Fin.ext;rfl
@[simp] theorem unpair_zero (a b : ℕ) : (pair a b).symm 0=(0,0):=by rw [Equiv.symm_apply_eq];exact (join_zero a b).symm

variable {r D cap d loc a c H groups M w : ℕ}
local notation "terrainBits" => Owners.inputBits r D (2*cap) d
local notation "peerBits" => ((Owners.digits r D d*3)*r)*(D+1)
local notation "wireBits" => DescentSignedCableCodec.width D cap
local notation "allDonors" => bundleBits loc a c*(r*cap)
local notation "digits" => pathBits D

/-- One previous input cell holds the actual donor slab of a group in
block-first, outgoing-slot-second order. Unoccupied signed cells decode to zero. -/
def scalar (profile : ℕ) (x : Fin r) (s : Fin cap) (side : Bool)
    (owners : Cell (terrainBits+peerBits)) (old : Cell (wireBits+allDonors)) : Cell (digits*11) :=
  let v:=(pair _ _).symm owners
  let e:=(pair _ _).symm old
  if e.1=0 then 0 else
    let donor:=unpackDonor ((encode (bundleBits loc a c) (r*cap)).symm e.2 (finProdFinEquiv (x,s)))
    paths profile x s side v.1 v.2 e.1 (liveGate donor)

theorem scalar_empty (profile : ℕ) (x : Fin r) (s : Fin cap) (side : Bool) :
    scalar (d:=d) (D:=D) (loc:=loc) (a:=a) (c:=c) profile x s side 0 0=0:=by simp [scalar]

theorem scalar_at (profile : ℕ) (x : Fin r) (s : Fin cap) (side : Bool)
    (raw : Cell terrainBits) (reg : Cell peerBits) (signed : DescentSharedCableNames.Stage.Live D cap)
    (rows : Fin (r*cap)→Donor loc a c) :
    scalar profile x s side (join raw reg) (join (DescentSignedCableCodec.encode (some signed))
      (encode _ (r*cap) (fun i=>packDonor (rows i))))=
      paths profile x s side raw reg (DescentSignedCableCodec.encode (some signed)) (liveGate (rows (finProdFinEquiv (x,s)))) :=by
  have live : DescentSignedCableCodec.encode (some signed)≠0:=by
    intro eqn
    have h:=congrArg (DescentSignedCableCodec.decode D cap) eqn
    rw [DescentSignedCableCodec.decode_encode,←DescentSignedCableCodec.empty,DescentSignedCableCodec.decode_encode] at h
    contradiction
  simp [scalar,join,live]

/-- The raw chooser terrain, bounded peer roster registers, old signed column,
and complete old donor slab are the only four variable input expressions. -/
theorem execute (profile : ℕ) (x : Fin r) (s : Fin cap) (side : Bool)
    (left right final : Tables) (owner peers cable donors : Expr) (out : Bank) (m : Memory w)
    (raw : Fin H→Fin groups→Cell terrainBits) (reg : Fin H→Fin groups→Cell peerBits)
    (ink : Fin H→Fin groups→Cell wireBits) (board : Fin H→Fin groups→Cell allDonors)
    (oa : DescentPackedZip.Source owner raw M m) (pa : DescentPackedZip.Source peers reg M m)
    (ca : DescentPackedZip.Source cable ink M m) (da : DescentPackedZip.Source donors board M m)
    (lfit : DescentPackedZip.Fits left owner peers terrainBits peerBits M out.base w)
    (rfit : DescentPackedZip.Fits right cable donors wireBits allDonors M out.base w)
    (lastFit : DescentPackedZip.Fits final (left.read owner peers) (right.read cable donors)
      (terrainBits+peerBits) (wireBits+allDonors) M out.base w)
    (lROM : Static left (@join terrainBits peerBits) M m) (rROM : Static right (@join wireBits allDonors) M m)
    (table : Static final (scalar (D:=D) (d:=d) (loc:=loc) (a:=a) (c:=c) profile x s side) M m)
    (space : out.base+H*chunks groups M<2^w) :
    let e:=final.read (left.read owner peers) (right.read cable donors)
    let result:=image out.base (H*chunks groups M) e m
    (scan w out.base (H*chunks groups M) e).Exec m result (4+H*chunks groups M*(2*e.work+4)) ∧
    Reads out (fun v g=>scalar profile x s side (join (raw v g) (reg v g)) (join (ink v g) (board v g))) M result ∧
    (∀j,j<out.base ∨ out.base+H*chunks groups M≤j → result j=m j) ∧ CheapCode (scan w out.base (H*chunks groups M) e) := by
  intro e result
  have l:=read_data left owner peers out.base lfit (@join terrainBits peerBits) (join_zero _ _) m lROM raw reg oa pa
  have z:=read_data right cable donors out.base rfit (@join wireBits allDonors) (join_zero _ _) m rROM ink board ca da
  have got:=read_data final _ _ out.base lastFit _ (scalar_empty profile x s side) m table _ _ l z
  have fits : e.Fits w out.base:=⟨lastFit.apply,lastFit.right,lastFit.shift,lastFit.left⟩
  refine ⟨scan_exec _ _ _ _ fits space,fun p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H groups M p)).trans (got p),?_,@scan_cheap _ _ _ _⟩
  rintro j (h|h)
  · simp [result,image,fillSegment,Nat.not_le.mpr h]
  · simp [result,image,fillSegment,Nat.not_lt.mpr h]
end
end Hierarchy.DescentPacking.PackedMatch.Local.ParentIncidence.PathRAM

end OAI
