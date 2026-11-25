import OAI.Hierarchy.DescentResetOriginalAuxBank
import OAI.Hierarchy.DescentResetPeerJointAuxValues
import OAI.Hierarchy.DescentResetSharedBroadcast

namespace OAI
/-! # Eight packed rank fields produced on one compact reset stage -/
namespace Hierarchy.DescentResetPeerJointPacked.Aux
open DescentDyadicSpan DescentSixParty.Chronology DescentResetPeerJointRAM DescentPackedZip DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
open private DescentResetPeerJointPacked.after_count from OAI.Hierarchy.DescentResetPeerJointPacked
noncomputable section
variable {w H P O D G M b N : ℕ}

theorem aux_bank (base H P G M b : ℕ) (j : Fin 4) (roof : completeEnd base H P G M b < 2^w) :
    let start:=DescentResetPeerJointPacked.endAddress base H P G M b
    (bank start H j).Fits w (completeEnd base H P G M b) ∧ H≤(bank start H j).size := by
  intro start
  have u:=Nat.mul_le_mul_right H j.isLt.le
  have extent : start+j.val*H+span H≤completeEnd base H P G M b := by
    unfold completeEnd; dsimp only [start];omega
  exact ⟨⟨span_pos _,(Nat.le_add_left ..).trans_lt (extent.trans_lt roof),extent⟩,span_ge H⟩

theorem expr_fits (base H P G M b : ℕ) (j : Fin 4) (roof : completeEnd base H P G M b < 2^w) :
    (expr base H P G M b j).Fits w (completeEnd base H P G M b) := by
  have lo : DescentResetPeerJointPacked.endAddress base H P G M b≤completeEnd base H P G M b:=by unfold completeEnd;omega
  exact DescentResetSharedBroadcast.fits_existing _ _ _ _ _ _ _ (aux_bank base H P G M b j roof).1 (lo.trans_lt roof) lo

/-- The four raw neighbors and complete prior roster arrive from the earlier
program. The three original raw neighbors still exclude the inserted self. -/
theorem run (base width : ℕ) (A : Sources) (raw : Bank) (name : Fin N→Fin P)
    (now : Fin P→Fin 4→Option (Fin P)) (old : Fin O→Fin D→Option (Fin O))
    (near : Fin P→Fin 3→Option (Fin P)) (m : Memory w)
    (live : N≤H) (room : Room A base H P O D w) (prior : raw.Fits w base) (size : 3*P≤raw.size)
    (stored : Reads A N name now old m)
    (original : ∀v j,m (raw.base+(j:Fin 3).val*P+(v:Fin P).val)=(((near v j).elim P Fin.val : ℕ) : Word w))
    (distinct : ∀r i j z,old r i=some z → old r j=some z → i=j)
    (pos : 0<width) (digitRoom : width*radix D ≤ 2^b) (sigRoom : 2*(D+1)≤2^b)
    (roof : completeEnd base H P G M b < 2^w) :
    let pgm:=complete w base H P O width D G M b A raw
    pgm.Runs m ∧
    (∀j,Source (DescentResetPeerJointPacked.expr base H P G M b j)
      (fun (v : Fin H) (_ : Fin G)=> (⟨DescentResetPeerJointRAM.value O width D old N name now v j,
        DescentResetPeerJointRAM.value_lt old name now v j distinct pos digitRoom⟩ : Cell b))
      M (pgm.image m)) ∧
    (∀j,Source (expr base H P G M b j)
      (fun (v : Fin H) (_ : Fin G)=> (⟨value width name old near v j,
        value_lt width name old near v j distinct pos digitRoom sigRoom⟩ : Cell b)) M (pgm.image m)) ∧
    (∀a,a<base ∨ completeEnd base H P G M b≤a → pgm.image m a=m a) := by
  intro pgm
  let root:=DescentResetPeerJointRAM.endAddress base H P
  let start:=DescentResetPeerJointPacked.endAddress base H P G M b
  let first:=DescentResetPeerJointRAM.phase w base H P O width D A
  let offer:=DescentResetPeerJointPacked.phase w base H P O width D G M b A
  let ny:=DescentResetHaloBroadcast.count H G M b
  let literal:=DescentResetHaloBroadcast.literal b G M (id : Fin H→Fin H)
  let columns:=row A raw base H P O D
  have lo : start≤completeEnd base H P G M b:=by unfold completeEnd;omega
  have rf:=lo.trans_lt roof
  have book : root+ny ≤ start:=DescentResetPeerJointPacked.after_count base H P G M b
  have cut := DescentFixedRowProgram.frame start (4*H) columns (offer.image m)
  have dictionary (i : ℕ) (bound : i<ny) : pgm.image m (root+i)=(literal i:Word w):=
    (cut _ (.inl ((Nat.add_lt_add_left bound root).trans_le book))).trans
      (DescentStaticWordColumn.read root ny literal (first.image m) bound)
  have always:=any base width A raw m room prior roof
  refine ⟨always.1,?_,?_,always.2⟩
  · intro j
    have bf:=DescentResetPeerJointRAM.bank_fits base H P j room.stop
    let src:=jointBank base H P j
    have later : root ≤ start:=(Nat.le_add_right ..).trans book
    have preserve (v:Fin H) : pgm.image m (src.base+v.val)=
        (DescentResetPeerJointRAM.value O width D old N name now v j:Word w) := by
      have inside:src.base+v.val<root:=(Nat.add_lt_add_left (v.isLt.trans_le bf.2) _).trans_le bf.1.2.2
      exact (cut _ (.inl (inside.trans_le later))).trans
        ((DescentStaticWordColumn.frame root ny literal (first.image m) _ (.inl inside)).trans
          (DescentResetPeerJointRAM.read base width N A name now old m live room stored v j))
    exact DescentResetSharedBroadcast.read_existing src root root (id : Fin H→Fin H)
      (fun v=>⟨_,DescentResetPeerJointRAM.value_lt old name now v j distinct pos digitRoom⟩)
      (pgm.image m) bf.1 bf.2 preserve rf dictionary
  · intro j
    have bf:=aux_bank base H P G M b j roof
    have read_out:=stored_words base width A raw name now old near m live room prior size stored original roof j
    exact DescentResetSharedBroadcast.read_existing _ root (completeEnd base H P G M b) (id : Fin H→Fin H)
      (fun v=>⟨_,value_lt width name old near v j distinct pos digitRoom sigRoom⟩)
      (pgm.image m) bf.1 bf.2 read_out rf dictionary

end
end Hierarchy.DescentResetPeerJointPacked.Aux

end OAI
