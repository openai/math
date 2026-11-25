import OAI.Hierarchy.DescentResetPeerJointAuxReads

namespace OAI
/-! # The actual four scalar origin words retained before the packed broadcast -/
namespace Hierarchy.DescentResetPeerJointPacked.Aux
open DescentDyadicSpan DescentSixParty.Chronology DescentResetPeerJointRAM DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H P O D G M b N : ℕ}

theorem stored_words (base width : ℕ) (A : Sources) (raw : Bank) (name : Fin N→Fin P)
    (now : Fin P→Fin 4→Option (Fin P)) (old : Fin O→Fin D→Option (Fin O))
    (near : Fin P→Fin 3→Option (Fin P)) (m : Memory w)
    (live : N≤H) (room : Room A base H P O D w) (prior : raw.Fits w base) (size : 3*P≤raw.size)
    (stored : Reads A N name now old m)
    (original : ∀v j,m (raw.base+(j:Fin 3).val*P+(v:Fin P).val)=(((near v j).elim P Fin.val : ℕ) : Word w))
    (roof : completeEnd base H P G M b < 2^w) :
    let pgm:=complete w base H P O width D G M b A raw
    let start:=DescentResetPeerJointPacked.endAddress base H P G M b
    ∀(j : Fin 4) (v : Fin H),pgm.image m ((bank start H j).base+v.val)=(value width name old near v j:Word w) := by
  intro pgm start j v
  let offer:=DescentResetPeerJointPacked.phase w base H P O width D G M b A
  let columns:=row A raw base H P O D
  have lo : start ≤ completeEnd base H P G M b:=by unfold completeEnd; omega
  have regs:=registers base width A raw name now old near m room prior size stored original (lo.trans_lt roof)
  let i:=j.val*H+v.val
  have hpos:=Nat.zero_lt_of_lt v.isLt
  have bound : i<4*H:=by
    have enough:=Nat.mul_le_mul_right H j.isLt
    rw [Nat.succ_mul] at enough
    dsimp [i];have h:=v.isLt;omega
  have div : i/H=j.val:=by
    dsimp [i];rw [Nat.mul_comm j.val H,Nat.mul_add_div hpos,Nat.div_eq_of_lt v.isLt,Nat.add_zero]
  have mod_ : i%H=v.val:=by simp [i,Nat.add_mod,Nat.mod_eq_of_lt v.isLt]
  have capture:=DescentFixedRowProgram.read start (4*H) columns (offer.image m) bound
    (fits base H P O D G M b _ _ A raw room prior)
  change DescentFixedRowProgram.image start columns (offer.image m) (4*H) (start+j.val*H+v.val)=_
  rw [Nat.add_assoc]
  apply capture.trans
  change (scalar A raw base P O D (i%H) (i/H)).eval (offer.image m) 0=_
  rw [mod_,div]
  exact sample base width A raw name old near (offer.image m) live room prior size regs v j

end
end Hierarchy.DescentResetPeerJointPacked.Aux

end OAI
