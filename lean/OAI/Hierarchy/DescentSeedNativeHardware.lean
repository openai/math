import OAI.Hierarchy.DescentSeedNativeStartup
import OAI.Hierarchy.DescentSeedInitialTariff

namespace OAI
/-! # Instruction and time bounds of public zero-date geometry -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSeedRoot DescentPackedSeed DescentColonies DescentSIMDLookup DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst DescentOperandStateBanks
open scoped Classical Fin.CommRing
noncomputable section
variable {F J : Type} [Field F] [Fintype J] [DecidableEq J] {k p R d G H w : ℕ}
    (X : Approximation F k p) (name : J≃Fin G) (digits : Fin R≃J×Block d) (host : Vertex X↪Fin H) (l : Layout)
local notation "M" => l.packedLanes
local notation "N" => l.groupsPerNode
local notation "b" => l.fieldBits
local notation "signedWords" => DescentSeedSignedBroadcast.size (Fintype.card (Vertex X)*(2*3)+1) (512*H) G M
local notation "rows" => CopyOrdinal.words d G l.operandLanes
local notation "operands" => Seed.count X*(N*7)
local notation "directory" => DescentSeedInitialTable.count H G M 3

def nameBound (H G d : ℕ) : ℕ :=
  let table:=DescentSeedSignedBroadcast.size (Fintype.card (Vertex X)*6+1) (512*H) G M
  let fieldRows:=CopyOrdinal.words d G l.operandLanes
  (15*(table+1)+91)+
    (15*(Signed.size X+1)+15*(Seed.count X+1)+2*(15*(fieldRows+1))+15+(7*(3*N)*2^d*H)*71)+
    15*(DescentSeedInitialTable.count H G M 3+1)

def clockBound (H G d : ℕ) : ℕ :=
  let table:=DescentSeedSignedBroadcast.size (Fintype.card (Vertex X)*6+1) (512*H) G M
  let fieldRows:=CopyOrdinal.words d G l.operandLanes
  (8+10*table+44*(512*H*chunks G M))+
    ((4+10*Signed.size X+(4+10*Seed.count X)+(4+10*fieldRows))+
      (4+10*fieldRows+(4+(7*(3*N)*2^d*H)*(4+34*chunks G l.operandLanes))))+
    (4+10*DescentSeedInitialTable.count H G M 3)

omit [Fintype J] [DecidableEq J] in
theorem hardware (w : ℕ) :
    CheapCode (program X name digits host l w) ∧
      DescentStaticWordColumn.names (program X name digits host l w)≤ nameBound X l H G d := by
  have signed:=Signed.Plane.control X (groups:=G) («M»:=l.packedLanes) (w:=w) l.base (DescentSeedInitialTable.rack X host)
  have operand:=Seed.Physical.price X host name digits w (operandBase X l H G) N (3*N) 1 l.operandBits l.operandLanes
  have dir:=DescentSeedInitialTable.control w (directoryBase X l H G d) H G M 3
    (DescentSeedInitialTable.fields X host d G M l.wire l.history l.seedWidth b)
  constructor
  · let first := Signed.Plane.paddedSetup X (groups:=G) («M»:=l.packedLanes) (w:=w)
      l.base (DescentSeedInitialTable.rack X host)
    let second := Seed.Physical.program X host name digits w (operandBase X l H G)
      N (3*N) 1 l.operandBits l.operandLanes
    let third := DescentSeedInitialTable.program w (directoryBase X l H G d) H G M 3
      (DescentSeedInitialTable.fields X host d G M l.wire l.history l.seedWidth b)
    change CheapCode ((first.seq second).seq third)
    exact @cheap_seq w (first.seq second) third
      (@cheap_seq w first second (@And.right _ _ signed) (@And.left _ _ operand))
      (@And.right _ _ dir)
  · unfold program nameBound
    rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq,signed.1,dir.1]
    exact Nat.add_le_add_right (Nat.add_le_add_left operand.2.1 _) _

omit [_root_.Field F] in
theorem clock_bound (_mem : Memory w) (_fit : l.operandBits*l.operandLanes≤ w) (_room : endAddress X l H G d<2^w) :
    clock X l H G d≤ clockBound X l H G d := by
  unfold clock clockBound operandClock
  rw [Signed.Plane.clock_eq]

end
end Hierarchy.DescentDatedSeedStartup

/-! # An absolute physical cost per word of the initial public allocation -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSeedRoot DescentPackedSeed DescentColonies DescentSIMDLookup DescentOperandStateBanks
open Catalyst
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) (l : Layout)
local notation "N" => l.groupsPerNode
local notation "M" => l.packedLanes

omit [_root_.Field F] in
theorem tariff_increment (H G d : ℕ) (active : 0< chunks G l.operandLanes) :
    clockBound X l H G d+7*nameBound X l H G d ≤ 1600*(endAddress X l H G d-l.base+1) := by
  let batch:=chunks G l.operandLanes
  let grouped:=H*batch
  let args:=CopyOrdinal.words d G l.operandLanes
  let padded:=2^Nat.clog 2 args
  let table:=DescentSeedSignedBroadcast.size (Fintype.card (Vertex X)*6+1) (512*H) G M
  let jobs:=7*(3*N)*2^d*H
  have space : table+512*H*chunks G M+Signed.size X+Seed.count X+padded+padded+jobs*batch+
      DescentSeedInitialTable.count H G M 3≤ endAddress X l H G d-l.base := by
    change table+512*H*chunks G M+Signed.size X+Seed.count X+padded+padded+
      (7*(3*N)*2^d*H)*batch+DescentSeedInitialTable.count H G M 3 ≤
      (l.base+table+512*H*chunks G M+Signed.size X+Seed.count X+padded+padded+
        (7*(3*N))*(2^d*(H*batch))+2^Nat.clog 2 (grouped+1)+DescentSeedInitialTable.count H G M 3)-l.base
    simp only [Nat.mul_assoc, Nat.add_assoc, Nat.add_sub_cancel_left]
    repeat' apply Nat.add_le_add_left
    exact Nat.le_add_left ..
  exact DescentSeedInitialTable.init_tariff table (512*H*chunks G M) (Signed.size X) (Seed.count X) args
    padded jobs batch (DescentSeedInitialTable.count H G M 3) _ (Nat.le_pow_clog (by decide) _) active space

omit [_root_.Field F] in
theorem tariff (H G d : ℕ) (active : 0< chunks G l.operandLanes) :
    clockBound X l H G d+7*nameBound X l H G d ≤ 1600*(endAddress X l H G d+1) :=
  (tariff_increment X l H G d active).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.sub_le ..) _))

end
end Hierarchy.DescentDatedSeedStartup

end OAI
