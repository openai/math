import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentDatedSeedLayout
import OAI.Hierarchy.DescentSeedNativeDirectory
import OAI.Hierarchy.DescentSeedSignedRaster
import OAI.Hierarchy.DescentSeedOperandWriter

namespace OAI
/-! # Fixed public initialization for the original dated host

A single procedure produces the signed geometry, seven operand columns,
and the packed matching directory in successive fresh regions. None of
its public operands depends on values of the private proposal words.
-/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSeedRoot DescentPackedSeed DescentInitialHost DescentColonies DescentSIMDLookup
open DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open Catalyst DescentOperandStateBanks
open scoped Classical Fin.CommRing
noncomputable section

variable {F J : Type} [Field F] [Fintype J] [DecidableEq J] {k p R d G H w : ℕ}
    (X : Approximation F k p) (name : J≃Fin G) (digits : Fin R≃J×Block d) (host : Vertex X↪Fin H)

variable (l : Layout)
local notation "N" => l.groupsPerNode
local notation "b" => l.fieldBits
local notation "rack" => DescentSeedInitialTable.rack X host
local notation "vals" => DescentSeedInitialTable.fields X host d G l.packedLanes l.wire l.history l.seedWidth b


local notation "ob" => operandBase X l H G
local notation "db" => directoryBase X l H G d
local notation "top" => endAddress X l H G d

omit [_root_.Field F] in
theorem fences (H G d : ℕ) : l.base≤ operandBase X l H G ∧
    operandBase X l H G≤ directoryBase X l H G d ∧ directoryBase X l H G d≤ endAddress X l H G d := by
  constructor
  · unfold operandBase Signed.Plane.endAddress Signed.Plane.output;omega
  constructor
  · unfold directoryBase Seed.Physical.endAddress Seed.Physical.bankStart Seed.Columns.first Seed.Columns.maskBase Seed.stampStart
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  · exact Nat.le_add_right ..

def program (w : ℕ) : Procedure w :=
  ((Signed.Plane.paddedSetup X (groups:=G) (M:=l.packedLanes) l.base rack).seq
    (Seed.Physical.program X host name digits w ob N (3*N) 1 l.operandBits l.operandLanes)).seq
    (DescentSeedInitialTable.program w db H G l.packedLanes 3 vals)

def signedMem (m : Memory w) := Signed.Plane.paddedMemory X (groups:=G) (M:=l.packedLanes) l.base rack m

def operandMem (m : Memory w) := Seed.Physical.memory X host name digits ob N (3*N) 1 l.operandBits l.operandLanes (signedMem (G:=G) X host l m)
def output (m : Memory w) := DescentSeedInitialTable.image db H G l.packedLanes 3 vals (operandMem X name digits host l m)

def operandClock (H G d : ℕ) :=
  let rows:=CopyOrdinal.words d G l.operandLanes
  let jobs:=7*(3*N)*2^d*H
  (4+10*Signed.size X+(4+10*Seed.count X)+(4+10*rows))+
    (4+10*rows+(4+jobs*(4+34*chunks G l.operandLanes)))

def clock (H G d : ℕ) :=
  Signed.Plane.clock X l.base H G l.packedLanes+operandClock X l H G d+
    (4+10*DescentSeedInitialTable.count H G l.packedLanes 3)

omit [Fintype J] [DecidableEq J] in
/-- Execution applies to every initial bit pattern, including a rejected
selector or an out-of-format exterior witness. -/
theorem execute (m : Memory w) (signedWidth : DescentSignedCableCodec.width 3 256*l.packedLanes≤ w)
    (fieldsFit : l.operandBits*l.operandLanes≤ w) (room : top<2^w) :
    (program X name digits host l w).Exec m (output X name digits host l m) (clock X l H G d) := by
  have F:=fences X l H G d
  have signed:=Signed.Plane.padded_run X (groups:=G) (M:=l.packedLanes) l.base rack m signedWidth
    (F.2.1.trans_lt (F.2.2.trans_lt room))
  have operand:=Seed.Physical.issued X host name digits ob N (3*N) 1 l.operandBits l.operandLanes (signedMem (G:=G) X host l m) (by simpa using fieldsFit) (F.2.2.trans_lt room)
  have bounded : (Seed.Physical.program X host name digits w ob N (3*N) 1 l.operandBits l.operandLanes).Exec
      (signedMem (G:=G) X host l m) (operandMem X name digits host l m) (operandClock X l H G d) := by
    exact Procedure.Spec.mono operand.1 (fun _ h=>h) (fun _ _ h=>h)
      (Seed.Physical.price X host name digits w ob N (3*N) 1 l.operandBits l.operandLanes).2.2
  intro labels registers slots machine
  exact Procedure.Exec.then (Procedure.Exec.then signed.1 bounded)
    (DescentSeedInitialTable.run db H G l.packedLanes 3 vals _ room) machine

omit [Fintype J] [DecidableEq J] in
theorem retain (m : Memory w) (signedWidth : DescentSignedCableCodec.width 3 256*l.packedLanes≤ w)
    (fieldsFit : l.operandBits*l.operandLanes≤ w) (room : top<2^w) (a : ℕ) (outside : a< l.base ∨ top≤ a) :
    output X name digits host l m a=m a := by
  obtain ⟨f₁,f₂,f₃⟩:=fences X l H G d
  have signed:=Signed.Plane.padded_run X (groups:=G) (M:=l.packedLanes) l.base rack m signedWidth
    (f₂.trans_lt (f₃.trans_lt room))
  have operand:=Seed.Physical.issued X host name digits ob N (3*N) 1 l.operandBits l.operandLanes (signedMem (G:=G) X host l m) (by simpa using fieldsFit) (f₃.trans_lt room)
  refine (DescentSeedInitialTable.frame db H G l.packedLanes 3 vals _ a (by change a< db ∨ top≤ a;omega)).trans ?_
  refine (operand.2.2 a (by change a< ob ∨ db≤ a;omega)).trans ?_
  exact signed.2.2 a (by change a< l.base ∨ ob≤ a;omega)

omit [Fintype J] [DecidableEq J] in
/-- Preserve all genuinely computed signed/operand words at their actual
original addresses, including inactive and padded hosts. -/
theorem signed_kept (m : Memory w) (fieldsFit : l.operandBits*l.operandLanes≤ w) (room : top<2^w)
    (a : ℕ) (low : a< ob) : output X name digits host l m a=signedMem (G:=G) X host l m a := by
  have F:=fences X l H G d
  have operand:=Seed.Physical.issued X host name digits ob N (3*N) 1 l.operandBits l.operandLanes (signedMem (G:=G) X host l m) (by simpa using fieldsFit) (F.2.2.trans_lt room)
  exact (DescentSeedInitialTable.frame db H G l.packedLanes 3 vals _ a (Or.inl (low.trans_le F.2.1))).trans
    (operand.2.2 a (Or.inl low))

omit [Fintype J] [DecidableEq J] in
theorem operand_kept (m : Memory w) (a : ℕ) (low : a< db) :
    output X name digits host l m a=operandMem X name digits host l m a :=
  DescentSeedInitialTable.frame db H G l.packedLanes 3 vals _ a (Or.inl low)

omit [Fintype J] [DecidableEq J] in
theorem directory (m : Memory w) :
    Mounted (DescentSeedInitialTable.ports db H G l.packedLanes 3) (DescentSeedInitialTable.roster X host)
      (output X name digits host l m) G l.packedLanes :=
  DescentSeedInitialTable.mounted X host db d l.wire l.history l.seedWidth b _

end
end Hierarchy.DescentDatedSeedStartup

end OAI
