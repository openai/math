import OAI.Computability.BorderVNP.DiagonalPinnedIssuedReportFrame
import OAI.Computability.BorderVNP.DiagonalEmittedReportFrame
import OAI.Computability.BorderVNP.DiagonalJointSparseWindow
import OAI.Computability.BorderVNP.DiagonalSignedSparseVisit

/-! # The fragment emitter on the original joint return's report memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM FragmentRows SignedTaskArena ScheduleClock TeamContraction.ProcessorSlots
open CellMacro.Generator CompactMachine TeamContraction.JointHeader

variable {R w n : ℕ} (a : SignedTaskArena.Layout) (U : Fin (R+1) → PinStart SparseExterior.driver n w)
    (active : JointPrefix a.id U) (u : Fin (R+1)) (offsets ctl rows : ℕ)
local notation3 (prettyPrint := false) "v" => visits a.id U (active u)
local notation3 (prettyPrint := false) "pub" => (U u).pub
local notation3 (prettyPrint := false) "mac" => install SparseExterior.driver n (U u).routines
local notation3 (prettyPrint := false) "m" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame (pub 0).val (readings m)
local notation3 (prettyPrint := false) "st" => (argumentVisitsEquiv pub mac (v).reports.val.2.1 m).symm (v).arguments

/-- The reported native directory and selected bounds produce the original
emitter and identify its actual register and memory return. Neither a
previous selection of an emitter nor a later cell return is required. -/
theorem issuedEmissionAtFrame (A : StartupArena) {reserve axes groups cap width inputs guesses gates : ℕ}
    (addr : a.FinishAddresses A ctl reserve axes groups cap width w inputs guesses gates)
    (head : (pub 0).val=A.frame) (report : IssuedReportFrame a pub m offsets ctl rows)
    (count : rows≤a.cube.maxRows) :
    ∃ (fit : (f).Fits w (readings m)) (cells : a.fragments.cells=(f).cells) (e : SparseEmission a f m fit cells),
      e.bank=(st).1.val.2.1 ∧ e.output=(st).1.val.2.2 ∧ SparseGeometry a f offsets ctl ∧
      ∀ i : Fin 37, readings m (ctl+i.val)=a.controls i.val := by
  obtain ⟨fr,_,compacted,_,cells,cables,_,words,geom⟩ := report
  have seen := fr.postReportWords a compacted cells cables words geom count
  have low : (pub 0).val+112≤ctl := by rw [head]; exact addr.place.beforeControl
  have below : ctl+37≤a.fragments.quads := (geom.controller.trans (arena_order a).1)
  obtain ⟨e,bank,memory⟩ := FragmentRows.emission_of_return pub mac (v).reports.val.2.1 m a seen.1 seen.2.1
    seen.2.2.1 low below seen.2.2.2.1 seen.2.2.2.2.1 seen.2.2.2.2.2 addr.endFit (st).1.property
  exact ⟨_,_,e,bank,memory,fr.loaded ▸ geom,words⟩

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
