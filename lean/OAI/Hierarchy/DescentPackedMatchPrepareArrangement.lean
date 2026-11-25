import OAI.Hierarchy.DescentPackedMatchFromOld
import OAI.Hierarchy.DescentPackedMatchPrepareSpace

namespace OAI
/-! # Scalar word and old-bank budgets imply all concrete predecessor lookup bounds -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare.ROM
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {k D cap a d M H G w : ℕ}
local notation "r" => 2^k
local notation "p" => 2*cap
local notation "rows" => H*chunks G M
local notation "cellBits" => DescentSignedCableCodec.width D cap

def headBits (H D : ℕ) := Nat.clog 2 (H*D+1)
def sortBase (base k D cap a M H G : ℕ) := base+staticWords k D cap a M H G+2^(Prepare.bits H G M)+2^(headBits H D)

structure OldRoom (act : Bank) (win : Fin r→Bank) (wire : Fin r→Fin p→Bank) (raw : Bank) (H G D M w base : ℕ) : Prop where
  actor : act.Fits w base ∧ H*chunks G M≤act.size
  winner : ∀x,(win x).Fits w base ∧ H*chunks G M≤(win x).size
  signed : ∀x j,(wire x j).Fits w base ∧ H*chunks G M≤(wire x j).size
  rotor : raw.Fits w base ∧ H*D≤raw.size

private theorem fitted (b : Bank) {w cap : ℕ} (before : b.base+b.size≤cap) (room : cap<2^w) : b.Fits w cap :=
  ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (before.trans_lt room),before⟩

private theorem shift_fit (b : Bank) {w a b' : ℕ} (f : b.Fits w a) (le : a≤b') : b.Fits w b' :=
  ⟨f.1,f.2.1,f.2.2.trans le⟩

theorem arranged (base k D cap a d M H G w : ℕ) (act : Bank) (win : Fin (2^k)→Bank) (wire : Fin (2^k)→Fin (2*cap)→Bank) (raw : Bank)
    (old : OldRoom act win wire raw H G D M w base) (key : M*max (DescentSignedCableCodec.width D cap) d≤w/2)
    (small : max H D<2^w) (wide : stop k H G M D cap (sortBase base k D cap a M H G)<2^w) :
    let b:=sortBase base k D cap a M H G;let C:=chart base D a M (Prepare.bits H G M) act win wire
    let R:=roster base k D cap a M H G (headBits H D) raw
    base+staticWords k D cap a M H G≤b ∧ Room C D a d M H G w b ∧ DescentSortedRoster.Room R D H w b := by
  intro b C R
  let count:=H*chunks G M;let shift:=2^((1*2^k)*M);let gate:=2^((1*2^k+a)*M);let dict:=2^(DescentSignedCableCodec.width D cap*M)
  let mask:=2^(Prepare.bits H G M);let header:=2^(headBits H D);let rank:=rankBase base k D cap a M H G
  have rowRoom : count≤ mask := (Nat.le_succ count).trans (Nat.le_pow_clog (by decide) _)
  have headRoom : H*D≤header := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have layout : b=rank+2*(H*D)+mask+header := by
    dsimp [b,rank,sortBase,rankBase,maskBase,chipBase,gateBase,staticWords,mask,header];ring
  have rankAt : rank=base+shift+2^k*gate+dict+count := rfl
  have separation : base+staticWords k D cap a M H G≤b := by dsimp [b,sortBase];omega
  have left : base≤b := (Nat.le_add_right ..).trans separation
  have first : b+H*D≤ stop k H G M D cap b := Nat.le_add_right ..
  have scale : 1≤2^k+2^k*(2*cap) := (Nat.two_pow_pos k).trans_le (Nat.le_add_right ..)
  have remain : count≤(2^k+2^k*(2*cap))*count := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right count scale
  have rowsEnd : b+count<2^w := by change b+H*D+(2^k+2^k*(2*cap))*count<2^w at wide;omega
  have room : b<2^w := (Nat.le_add_right ..).trans_lt rowsEnd
  have rankBefore : rank ≤ b := by
    rw [layout]
    exact ((Nat.le_add_right rank _).trans (Nat.le_add_right _ mask)).trans (Nat.le_add_right _ header)
  have gateEnd : base+shift+2^k*gate ≤ b := by
    apply Nat.le_trans _ rankBefore
    rw [rankAt]
    exact (Nat.le_add_right _ dict).trans (Nat.le_add_right _ count)
  have sf : C.shift.Fits w b := fitted _ ((Nat.le_add_right _ (2^k*gate)).trans gateEnd) room
  have tf (x : Fin (2^k)) : (C.gate x).Fits w b := by
    have span : (x.val+1)*gate≤2^k*gate:=Nat.mul_le_mul_right gate x.isLt
    rw [Nat.add_mul,Nat.one_mul] at span
    apply fitted _ _ room
    change (base+shift+x.val*gate)+gate≤b
    rw [Nat.add_assoc]
    exact (Nat.add_le_add_left span (base+shift)).trans gateEnd
  have df_ : C.dictionary.Fits w b := fitted _ (by change base+shift+2^k*gate+dict≤b;omega) room
  have mf : C.mask.Fits w b := fitted _ (by change base+shift+2^k*gate+dict+mask≤b;omega) room
  have rf : R.origin.Fits w b := fitted _ (by change rank+header≤b;omega) room
  have qf : R.slot.Fits w b := fitted _ (by change rank+H*D+header≤b;omega) room
  refine ⟨separation,⟨?_,?_,old.actor.2,fun x=>(old.winner x).2,wide⟩,?_,(Nat.le_max_left _ _).trans_lt small,(Nat.le_max_right _ _).trans_lt small,first.trans_lt wide⟩
  · intro x;exact ⟨⟨shift_fit _ old.actor.1 left,trivial⟩,⟨shift_fit _ (old.winner x).1 left,trivial⟩,sf,tf x,rfl,rfl⟩
  · intro x j;exact ⟨shift_fit _ (old.signed x j).1 left,df_,mf,(old.signed x j).2,rfl,rowRoom,rowsEnd,key⟩
  · intro bank member;rcases List.mem_cons.mp member with rfl|more
    · exact ⟨shift_fit _ old.rotor.1 left,old.rotor.2⟩
    · rcases List.mem_cons.mp more with rfl|last
      · exact ⟨rf,headRoom⟩
      · obtain rfl:=List.mem_singleton.mp last;exact ⟨qf,headRoom⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare.ROM

end OAI
