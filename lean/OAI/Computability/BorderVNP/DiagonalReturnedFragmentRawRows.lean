import OAI.Computability.BorderVNP.CubeRouteGuardColumns
import OAI.Computability.BorderVNP.DiagonalSignedFragmentPublication
import OAI.Computability.BorderVNP.FragmentRowsPublishedStream

/-! # The compacted delivery list in the returned signed fragment memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM Packing

variable {w frame raw : ℕ} {a : Layout} {placed : Memory w} {written out : ℕ → ℕ} {signed : Bool}
    (D : Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
local notation3 (prettyPrint := false) "rs" => D.directory pp lp
local notation3 (prettyPrint := false) "initial" => readings (Directory.ISA.publish placed frame raw (D.directory pp lp))
local notation3 (prettyPrint := false) "layout" => FragmentRows.Layout.fromFrame frame out

/-- The fragment scanner on the actual report memory reads the published list
in its entirety and decodes each seven-word row at its original compacted index. -/
theorem ReportWords.returnedRows (h : ReportWords a frame initial written out signed)
    (address : readings placed (frame+8)=raw) (first : frame+112≤raw)
    (stop : raw+7*(rs).length ≤ a.cube.header.header) (count : (rs).length<2^w)
    (fit : ∀ i : Fin (rs).length, ∀ x ∈ (rs)[i.val].words, x<2^w) :
    (List.range (layout).count).map ((layout).row out)=rs ∧
      ∀ i : Fin (rs).length, (layout).row out i.val=(rs)[i.val] := by
  have all := FragmentRows.rows_from_published placed frame raw D pp lp out address (by omega) count fit
    (h.frame_word 8 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide))
    (h.frame_word 9 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide))
    (fun x lx hx => h.geometry x (by omega) (hx.trans_le stop))
  refine ⟨all,fun i => ?_⟩
  have counted : (layout).count=(rs).length := h.compacted_count count
  have inRange : i.val<(List.range (layout).count).length := by simpa only [List.length_range,counted] using i.isLt
  have eq := congrArg (fun ys => ys[i.val]?) all
  simpa only [List.getElem?_map,List.getElem?_eq_getElem inRange,List.getElem_range,Option.map_some,
    List.getElem?_eq_getElem i.isLt,Option.some.injEq] using eq

/-- The actual slotted writer certifies the raw pointer, all seven columns
and the full directory allocation consumed by the reached fragment scan. -/
theorem ReportWords.returnedSlottedRows (h : ReportWords a frame initial written out signed)
    {I : Type*} [Fintype I] {cell : I → Fin a.cube.cells} {id : I ↪ ℕ} {width : I → ℕ}
    {pub : Arg → Word w} {pins : Pins.Layout}
    (P : Evaluator.SlottedWriter a.cube D pp lp pins pub placed raw cell id width)
    (frameAt : (pub 0).val=frame) (arenaFit : a.cube.stop<2^w) :
    (List.range (layout).count).map ((layout).row out)=rs ∧
      ∀ i : Fin (rs).length, (layout).row out i.val=(rs)[i.val] := by
  subst frame
  have stop : raw+7*(rs).length ≤ a.cube.header.header := by simpa only [Nat.mul_comm 7] using P.rawEnd
  obtain ⟨hh,lab,grp,own,pair,host,rec,limit⟩ := a.cube.writer_order
  exact h.returnedRows D pp lp P.pointers.1 P.rawStart stop (by omega) (P.source_words arenaFit)

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
