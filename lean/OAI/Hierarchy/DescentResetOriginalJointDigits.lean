import OAI.Hierarchy.DescentResetOriginalZeroHaloRead
import OAI.Hierarchy.DescentResetOriginalScalarValues
import OAI.Hierarchy.DescentResetPeerJointAuxRun

namespace OAI
/-! # Reading the original-number fields from the same prior scene as the joint-rank stage -/
namespace Hierarchy.DescentResetOriginalZeroHalo
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentResetPeerJointRAM DescentResetPeerJointPacked
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M b P O N D : ℕ}

/-- The intervening phases may update the scene above the joint stage. Its two actual
compact scalar columns determine every public and private self/shape operand. -/
theorem run_joint (base issue width z short haloBits : ℕ) (A : DescentResetPeerJointRAM.Sources)
    (raw : Bank) (name : Fin N→Fin P) (now : Fin P→Fin 4→Option (Fin P))
    (old : Fin O→Fin D→Option (Fin O)) (near : Fin P→Fin 3→Option (Fin P))
    (initial before : Memory w) (live : N ≤ H) (room : Room A base H P O D w)
    (bankRoom : raw.Fits w base) (available : 3*P ≤ raw.size) (stored : Reads A N name now old initial)
    (original : ∀v j,initial (raw.base+(j:Fin 3).val*P+(v:Fin P).val)=(((near v j).elim P Fin.val : ℕ) : Word w))
    (distinct : ∀r i j v,old r i=some v → old r j=some v → i=j) (positive : 0<width)
    (shortJoint : width*radix D ≤ 2^b) (shortCorrection : 2*(D+1) ≤ 2^b)
    (order : completeEnd base H P G M b ≤ issue)
    (retained : ∀a,a<completeEnd base H P G M b →
      before a=(Aux.complete w base H P O width D G M b A raw).image initial a)
    (roof : DescentResetOriginalZeroHalo.endAddress issue H G M b < 2^w) :
    let start:=DescentResetPeerJointPacked.endAddress base H P G M b
    let digit:=fun (j : Fin 4) (v : Fin H)=> (⟨Aux.value width name old near v j,
      Aux.value_lt width name old near v j distinct positive shortJoint shortCorrection⟩ : Cell b)
    let pgm:=DescentResetOriginalZeroHalo.phase w issue H G M b z short haloBits D
    pgm.Runs before ∧ Sources issue H G M b z short haloBits D (Aux.bank start H 0)
      (Aux.bank start H 1) (digit 0) (digit 1) (pgm.image before) ∧
    ∀a,a< issue ∨ DescentResetOriginalZeroHalo.endAddress issue H G M b ≤ a → pgm.image before a=before a := by
  intro start digit pgm
  have issueBelow:= (Nat.le_add_right issue (count H G M b)).trans (written_le issue H G M b)
  have high:=order.trans_lt (issueBelow.trans_lt roof)
  have banks (j : Fin 4):=Aux.aux_bank base H P G M b j high
  have fits (j : Fin 4) : (Aux.bank start H j).Fits w issue :=
    ⟨(banks j).1.1,(banks j).1.2.1,(banks j).1.2.2.trans order⟩
  have words:=Aux.stored_words base width A raw name now old near initial live room bankRoom available
    stored original high
  have saved (j : Fin 4) (v : Fin H) :
      before ((Aux.bank start H j).base+v.val)=((digit j v).val:Word w) := by
    rw [retained _ ((Nat.add_lt_add_left (v.isLt.trans_le (banks j).2) _).trans_le (banks j).1.2.2)]
    exact words j v
  exact run issue H G M b z short haloBits D _ _ (digit 0) (digit 1) before
    (fits 0) (fits 1) (banks 0).2 (banks 1).2 (saved 0) (saved 1) roof

end
end Hierarchy.DescentResetOriginalZeroHalo

end OAI
