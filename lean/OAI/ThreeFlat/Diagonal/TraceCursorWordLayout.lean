import OAI.ThreeFlat.Diagonal.TraceCursorBoundary
import OAI.ThreeFlat.Diagonal.TraceFormRead
import OAI.ThreeFlat.Diagonal.LaneRelayNetwork

namespace OAI
/-! # The native outgoing/incoming port words read the two banks of a cursor leaf -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open Computability.VPVNP.Compression LaneCursor LaneCursor.RowLayout HistoryContraction CompressorPacking
open scoped BigOperators Classical
set_option quotPrecheck false
variable {F Pins : Type} [Field F] (B : Block F) {q : ℕ} (hk : 2≤q+1) (low offsets slots : ℕ)
variable (ext : (B.cursorState hk low offsets slots).Site→ℕ) (pin : ∀ v, Pins→Fin (ext v)→Bool)

noncomputable def cursorLayout (externalWidth : (B.cursorState hk low offsets slots).Site → ℕ)
    (readPin : ∀ v,Pins→Fin (externalWidth v)→Bool) : WordLayout (B.cursorState hk low offsets slots).shape.graph (B.cursorState hk low offsets slots).width Pins where
  count _ := 2 * (2^(B.exponent 0))
  order v := Native.ShrinkStage.Halves.portOrder (B.cursorState hk low offsets slots).graph (B.cursorState hk low offsets slots).chart v
  ext := externalWidth
  pin := readPin


theorem cursor_half_width (v : (B.cursorState hk low offsets slots).Site) : ((B.cursorCopies+1)*2)*(offsets*(2^low*(slots*3)))+((B.cursorCopies+1)*2)*(offsets*(2^low*(slots*3)))=(B.cursorLayout hk low offsets slots ext pin).ports.halfBits v := by
  change ((B.cursorCopies+1)*2)*(offsets*(2^low*(slots*3)))+((B.cursorCopies+1)*2)*(offsets*(2^low*(slots*3)))=∑ _ : Fin (2 * (2^(B.exponent 0))), (2^low*(offsets*slots*3))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  rw [←B.cursor_degree]
  change _ = (2 * ((B.cursorCopies + 1) * 2)) * (2 ^ low * (offsets * slots * 3))
  ring

private theorem cursorWord_tag (z : Fin (2^(2^low*(offsets*slots*3)))) (j : Fin (offsets*(2^low*(slots*3)))) :
    cursorWord low offsets slots z (tagOrder offsets low slots j)=
      (MotifBinaryPacking.word (2^low*(offsets*slots*3))).symm z (Fin.cast (by ac_rfl) j) := by
  simp [cursorWord]

theorem cursor_encode (v : (B.cursorState hk low offsets slots).Site) (x : (B.cursorState hk low offsets slots).shape.Half v) :
    (fun j => (B.cursorLayout hk low offsets slots ext pin).ports.encode v x (Fin.cast (B.cursor_half_width hk low offsets slots ext pin v) j)) =
      RelayNetwork.pins (tagOrder offsets low slots) (B.cursorOut hk low offsets slots v.1 v.2 x)
        (B.cursorIn hk low offsets slots v.1 v.2 x) := by
  have same (i : Fin (2 * (2^(B.exponent 0)))) : (B.cursorLayout hk low offsets slots ext pin).ports.lengths v i=(offsets*(2^low*(slots*3))) := by change (2^low*(offsets*slots*3))=(offsets*(2^low*(slots*3))); ac_rfl
  apply (B.cursorLayout hk low offsets slots ext pin).ports.encode_banks v x _ _ _
  · intro s j
    let a := B.cursorOutPort hk low offsets slots v.1 v.2 s
    refine ⟨a,Fin.cast (by ac_rfl : (offsets*(2^low*(slots*3)))=(2^low*(offsets*slots*3))) j,?_,?_⟩
    · refine ((B.cursorLayout hk low offsets slots ext pin).ports.uniform_portBit v (a:=a)
          (Fin.cast (by ac_rfl : offsets*(2^low*(slots*3))=2^low*(offsets*slots*3)) j) same).trans ?_
      have addr : (((B.cursorLayout hk low offsets slots ext pin).ports.port v).symm a).val=s.val := rfl
      simp only [addr]
      rfl
    · exact (cursorWord_tag low offsets slots (x a) j).symm
  · intro s j
    let a := B.cursorInPort hk low offsets slots v.1 v.2 s
    refine ⟨a,Fin.cast (by ac_rfl : (offsets*(2^low*(slots*3)))=(2^low*(offsets*slots*3))) j,?_,?_⟩
    · refine ((B.cursorLayout hk low offsets slots ext pin).ports.uniform_portBit v (a:=a)
          (Fin.cast (by ac_rfl : offsets*(2^low*(slots*3))=2^low*(offsets*slots*3)) j) same).trans ?_
      have addr : (((B.cursorLayout hk low offsets slots ext pin).ports.port v).symm a).val=(2^(B.exponent 0))+s.val := by
        change (2^(B.exponent 0))+((B.cursorState hk low offsets slots).graph.actualTarget ((B.cursorState hk low offsets slots).graph.actualTarget.symm _)).1.2.val=_
        rw [Equiv.apply_symm_apply]
        rfl
      simp only [addr,Nat.add_mul,B.cursor_degree,Nat.add_assoc]
      rfl
    · exact (cursorWord_tag low offsets slots (x a) j).symm

end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
