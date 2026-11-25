import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentSixPartyGadget

namespace OAI
/-! # Local private argument capacity and the fixed physical site population -/

namespace Hierarchy
namespace DescentCompiler.AtomSchedule
variable (S : AtomSchedule)
def localCapacityExponent := 8+S.capGain*(S.rounds+1)
def localGrainExponent := S.capGain*(S.rounds+1)
def localTokenExponent := S.priceExponent+S.localCapacityExponent

end DescentCompiler.AtomSchedule

namespace DescentSixParty
open DescentCompiler
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)

namespace Reached
def siteLimit (S : AtomSchedule) := (S.initialSites*S.copies)*(2^S.hostGain)^S.length

theorem siteLimit_by_home (S : AtomSchedule) :
    S.hostSize S.length*(S.baseGroups*S.radix)=siteLimit S := by
  simp only [siteLimit,AtomSchedule.hostSize,AtomSchedule.copies,mul_pow,pow_succ]
  ring

end Reached

def operandExponent := (8*(G.C+G.k+G.b+2)+3) + S.localGrainExponent + S.capGain

namespace NativeBranch
def privateSlotCapacity (R : ℕ) := (R+1)*S.epochPower^(operandExponent G S+S.localTokenExponent)

def privateSlotBits (R : ℕ) := Nat.log 2 (privateSlotCapacity G S R)+1

theorem packedSiteLimit (S : AtomSchedule) :
    Reached.siteLimit S = (S.initialSites*S.copies)*S.epochPower^(S.hostGain*(S.rounds+1)) := by
  unfold Reached.siteLimit AtomSchedule.epochPower AtomSchedule.length
  rw [←pow_mul,←pow_mul]
  congr 2; ring

theorem private_slot_mass (R : ℕ) :
    Reached.siteLimit S*(privateSlotBits G S R*privateSlotCapacity G S R) ≤
      2*(S.initialSites*S.copies)*(R+1)^2*S.epochPower^
        (S.hostGain*(S.rounds+1)+2*(operandExponent G S+S.localTokenExponent)) := by
  let size:=privateSlotCapacity G S R
  have hT : 0<S.epochPower:=Nat.two_pow_pos _
  have hs : 0<size := by dsimp [size,privateSlotCapacity];positivity
  have log:=Nat.log_le_self 2 size
  have bound : Nat.log 2 size+1≤2*size := by omega
  calc
    Reached.siteLimit S*(privateSlotBits G S R*privateSlotCapacity G S R) ≤
        Reached.siteLimit S*((2*size)*size) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ bound)
    _ = _ := by
      rw [packedSiteLimit, pow_add, Nat.mul_comm 2 (operandExponent G S+S.localTokenExponent), pow_mul]
      dsimp [size,privateSlotCapacity]
      ring

end NativeBranch
end
end DescentSixParty
end Hierarchy

end OAI
