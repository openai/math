import OAI.Computability.BorderVNP.DiagonalReturnedFragmentRawRows

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Raw retained directory words used by a proposed report before its typed argument call -/

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM Packing

variable {w frame raw : ℕ} {a : Layout} {placed : Memory w} {written out : ℕ → ℕ} {signed : Bool}
    (D : Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
local notation3 (prettyPrint := false) "rs" => D.directory pp lp
local notation3 (prettyPrint := false) "initial" => readings (Directory.ISA.publish placed frame raw (D.directory pp lp))
local notation3 (prettyPrint := false) "layout" => FragmentRows.Layout.fromFrame frame out

/-- The native slotted writer and the report's actual frame preserve the
directory pointer, count and every occupied word of the original raw table. -/
theorem ReportWords.slottedPublication (h : ReportWords a frame initial written out signed)
    {I : Type*} [Fintype I] {cell : I → Fin a.cube.cells} {id : I ↪ ℕ} {width : I → ℕ}
    {pub : Arg → Word w} {pins : Pins.Layout}
    (P : Evaluator.SlottedWriter a.cube D pp lp pins pub placed raw cell id width)
    (frameAt : (pub 0).val=frame) (arenaFit : a.cube.stop<2^w) :
    readings placed (frame+8)=raw ∧ frame+9<raw ∧ (rs).length<2^w ∧
      (∀ i : Fin (rs).length, ∀ x∈(rs)[i.val].words, x<2^w) ∧
      out (frame+8)=initial (frame+8) ∧ out (frame+9)=initial (frame+9) ∧
      ∀ x, raw≤x → x<raw+7*(rs).length → out x=initial x := by
  subst frame
  have lo := P.rawStart
  have hi : raw+7*(rs).length ≤ a.cube.header.header := by simpa only [Nat.mul_comm 7] using P.rawEnd
  obtain ⟨h₀,h₁,h₂,h₃,h₄,h₅,h₆,limit⟩ := a.cube.writer_order
  refine ⟨P.pointers.1,by omega,by omega,P.source_words arenaFit,?_,?_,?_⟩
  · exact h.frame_word 8 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)
  · exact h.frame_word 9 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)
  · intro x xl xh
    exact h.geometry x (by omega) (xh.trans_le hi)

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
