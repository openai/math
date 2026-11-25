import OAI.Computability.NearSquareRoot.SynchronizedBoxPlanDepth

/-! # Chronological physical stage headers for the synchronized transform

The direction and matrix-list index address the finite schedule. Its rows act
on a column vector in reverse order. Each header also carries the kind of the
selected row, so the dispatcher can enter the appropriate physical subroutine.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayerTickets

open IntegerMultiplication Code ShortFourier.BatchWord
open SynchronizedLayers.ScheduleProgram

abbrev Key := Bool × Tally
abbrev Ticket := (Bool × Bool) × Tally × Bool × Tally
abbrev Entry := Bool × Row SlotDescriptor

def header (p : Key × Tally) : Ticket :=
  ((Iter.pick (default : Entry) (directedPlan p.1,p.2)).2.1,
    p.1.2,p.1.1,p.2)

def chronological (p : Key) : List Ticket :=
  (Iter.lineup (ruler (directedPlan p))).reverse.map (fun t => header (p,t))

theorem header_poly : Poly header := by
  have tab : Poly (fun p : Key × Tally => Iter.pick (default : Entry) (directedPlan p.1,p.2)) :=
    ((Easy.fst.poly.compose directedPlan_poly).pair Easy.snd.poly).compose (Iter.facile _).poly
  have code := tab.sndCompose.fstCompose
  exact code.pair ((Easy.fst.sndCompose).poly.pair ((Easy.fst.fstCompose).poly.pair Easy.snd.poly))

theorem chronological_poly : Poly chronological := by
  have list := (directedPlan_poly.compose (Easy.ruler Easy.identity).poly).compose Iter.poly_line
  exact (Poly.identity.pair list.rev).compose (Poly.push (false,[]) [] header_poly)

theorem chronological_length (p : Key) : (chronological p).length = (directedPlan p).length := by
  simp [chronological]

theorem header_at (p : Key) (j : Fin (directedPlan p).length) :
    header (p,tally j.val) = ((directedPlan p)[j.val].2.1,p.2,p.1,tally j.val) := by
  simp only [header, Iter.search _ _ _ j.isLt]

theorem chronological_at (p : Key) (j : Fin (directedPlan p).length) :
    (chronological p)[j.val]'(by rw [chronological_length]; exact j.isLt) =
      header (p,tally ((directedPlan p).length-1-j.val)) := by
  simp [chronological, Iter.lineup, List.getElem_reverse]

end FixedLayerTickets

end NearSquareRoot
end Computability
end OAI
