import OAI.Hierarchy.DescentSeedTokenProgram
import OAI.Hierarchy.DescentSeedTokenWordBill

namespace OAI
/-! # Paying the authentic two-part global original primitive program -/
namespace Hierarchy.DescentDatedSeedStartup.Primitive
open DescentInitialHost DescentPackedSeed DescentSeedRoot DescentSIMDLookup
open DescentPrimitivePalette DescentCompiler DescentSixParty DescentSeedTokenTransposition Catalyst
open DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {c p : ℕ} (X : Approximation F c p)
variable (D : PoweredGadget F) (op : RotorSpec) (R s Z h k H G M base : ℕ)

def hostFee (r : ℕ) :=1000+115*Fintype.card DescentPackedSeed.Primitive.Plan+300+50000*(5+2*r)

local notation "O" => Fintype.card (Old X)
local notation "A" => DescentPackedSeed.Primitive.pieces h s
local notation "a" => DescentPackedSeed.Primitive.roleBits s
local notation "b" => printedBits D s Z op
local notation "r" => 2^k
local notation "old" => DescentPackedSeed.Primitive.Source.bank X R s h base
local notation "splitAt" => DescentPackedSeed.Primitive.Source.finish X R s h base
local notation "nr" => DescentPackedSeed.Primitive.Source.jobs X R s h
variable (host : Vertex X↪Fin H)
local notation "choose" => select X H host
local notation "unit" => hub D op s Z
local notation "P" => Fintype.card DescentPackedSeed.Primitive.Plan

def privateFee (oldShort newShort : ℕ) :=300*oldShort+50000*(oldShort+2*newShort)

theorem version_cost (w oldShort newShort : ℕ) (oldCount : O ≤ H) (hostCount : 0 < H)
    (replicas : R=G*r) (oldLive : 0 < A) (newLive : 0 < M) (ambient : 2^h ≤ H)
    (overlap : (Overlap.pieces (G*r) A (M*r)+1)*(A+1)*2^(a*A) ≤ H)
    (project : r*2^((a*r)*M) ≤ H) (table : 2^(a*M) ≤ H)
    (oldUse : w+1 ≤ A*oldShort) (newUse : w+1 ≤ M*newShort) :
    (ticks X D op R s Z h k H G M base host w+7*DescentStaticWordColumn.names
        (program X D op R s Z h k H G M base host w))*(w+1) ≤
      H*(w+1)*hostFee r+(H*(G*r))*privateFee oldShort newShort :=by
  have part:=DescentPackedSeed.Primitive.Source.price X R s h w base
  have rest:=DescentSeedTokenTransposition.price splitAt O H G r a A M old choose unit w oldLive (Nat.two_pow_pos _) newLive
  have actual:=Nat.mul_le_mul_right (w+1) (Nat.add_le_add part rest)
  have localRows : nr*(w+1) ≤ H*(w+1)+H*(G*r)*oldShort :=by
    change O*chunks R A*(w+1) ≤ _
    rw [replicas]
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ oldCount)).trans (chunk_work H (G*r) A (w+1) oldShort oldUse)
  have dictionary:=(Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.div_le_self h 2)).trans ambient
  have install:=Nat.mul_le_mul_right (w+1) (Nat.mul_le_mul_left (115*P) dictionary)
  have origin:=Nat.mul_le_mul_right (w+1) hostCount
  have physical:=token_tariff_bits O H G r a A M (w+1) oldShort newShort oldCount (Nat.two_pow_pos _) oldLive hostCount
    overlap project table oldUse newUse
  rw [program,DescentStaticWordColumn.names_seq,ticks]
  calc
    _ ≤ (1000+115*P*2^(h/2)+300*nr+DescentSeedTokenTransposition.tariff O H G r a A M)*(w+1) :=by
      convert actual using 1; ring
    _ ≤ _:=by
      unfold hostFee privateFee
      nlinarith only [localRows,physical,install,origin]

end
end Hierarchy.DescentDatedSeedStartup.Primitive

end OAI
