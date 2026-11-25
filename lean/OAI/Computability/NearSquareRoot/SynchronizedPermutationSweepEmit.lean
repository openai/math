import OAI.Computability.NearSquareRoot.SynchronizedPermutationActiveIDs
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBatchSemantics
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetPhysical
import OAI.Computability.NearSquareRoot.FixedLayerTickets

/-! # Emitting the chronological sequence of batched half-stage descriptors -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord.PermDirectory

open IntegerMultiplication Code Staff Strip Carry SynchronizedPermutationBudget

abbrev HalfTicket := Bool × Tally
abbrev BatchTicket := HalfTicket × Tally

/-- The numerical half-stage and batch in the unary representation expected by
the position and switch table compiler. -/
def batchTicket (a : (Bool × ℕ) × ℕ) : BatchTicket := ((a.1.1,tally a.1.2),tally a.2)

private def regime : Regime Tally := ⟨Code.size,send,Dom.base _⟩

private theorem width_program : Poly (fun u : Tally => tally (SynchronizedPermutationBudget.width u.length)) := by
  have K : Realizes regime List.length := by
    change Poly (fun u : Tally => tally u.length)
    simpa only [recover_tally] using (Code.Poly.identity (X := Tally))
  exact (Realizes.fix 140).times ((Realizes.fix 1).plus (Figure.of_spoken (K.plus (.fix 1))).short_log)

private theorem batches_program : Poly (fun u : Tally =>
    tally (batches (PermHeader.groups u).length u.length)) := by
  have D : Realizes regime (fun u => (PermHeader.groups u).length) := by
    change Poly (fun u => tally (PermHeader.groups u).length)
    simpa only [ruler,tally,List.map_const',id_eq] using PermHeader.groups_poly.compose (Easy.ruler Easy.identity).poly
  have C : Realizes regime (fun u => SynchronizedPermutationBudget.capacity u.length) :=
    Benes.FieldDirectory.capacity_poly
  simp only [batches,Controlled.batchCount,Nat.ceilDiv_eq_add_pred_div]
  exact ((D.plus C).minused (.fix 1)).dividing C

private def halves (u : Tally) : List HalfTicket :=
  (Iter.lineup u).map (false,·) ++ (Iter.lineup u).reverse.map (true,·)

private theorem halves_poly : Poly halves :=
  Poly.app (Iter.poly_line.compose (Poly.maps _ ((Code.Poly.const false).pair Poly.identity)))
    (Iter.poly_line.rev.compose (Poly.maps _ ((Code.Poly.const true).pair Poly.identity)))

private def expand (q : List HalfTicket × List Tally) : List BatchTicket :=
  q.1.flatMap (fun a => q.2.map (a,·))

private theorem expand_poly : Poly expand := by
  let row (p : List Tally × HalfTicket) := polyPush id (p.2,p.1)
  have rowPoly : Poly row := (show Easy (fun p : List Tally × HalfTicket => (p.2,p.1)) by fun_prop).poly.compose
    (Poly.push default [] Poly.identity)
  have tab := (show Easy (fun q : List HalfTicket × List Tally => (q.2,q.1)) by fun_prop).poly.compose
    (Poly.push [] default rowPoly)
  exact tab.compose Easy.flatten.poly

def passOrder (u : Tally) : List BatchTicket :=
  expand (halves (tally (SynchronizedPermutationBudget.width u.length)),
    Iter.lineup (tally (batches (PermHeader.groups u).length u.length)))

theorem passOrder_poly : Poly passOrder :=
  ((width_program.compose halves_poly).pair (batches_program.compose Iter.poly_line)).compose expand_poly

private theorem lineup_tally (n : ℕ) : Iter.lineup (tally n) = (List.range n).map tally := by
  apply List.ext_getElem <;> simp [Iter.lineup]

/-- Exact tape order, including the backward traversal for the return half
of the Beneš network and every bounded batch within each half-stage. -/
theorem passOrder_tally (k : ℕ) :
    passOrder (tally k) = (order k ((CoprimeBox.box k).length/4)).map batchTicket := by
  simp only [passOrder,expand,halves,tally_length,PermHeader.groups_eq,List.length_ofFn,lineup_tally,
    order,Benes.batchOrder,Benes.executionOrder,List.map_append,List.flatMap_append,List.map_flatMap,
    List.flatMap_map,List.map_map,← List.map_reverse]
  rfl

/-- Retain the full row query when generating the header for an individual
half-stage and batch. Each input row uses the same header compiler. -/
def emitted {H : Type} (key : Query × BatchTicket → H) (q : Query) : List H :=
  polyPush key (q,passOrder q.2.1)

theorem emitted_poly {H : Type} [Codec H] [Inhabited H] (key : Query × BatchTicket → H)
    (hk : Poly key) : Poly (emitted key) :=
  (Poly.identity.pair (Easy.snd.fstCompose.poly.compose passOrder_poly)).compose (Poly.push default default hk)

theorem emitted_eq {H : Type} (key : Query × BatchTicket → H) (dir : Bool) (k s : ℕ) :
    emitted key (dir,tally k,tally s) =
      (order k ((CoprimeBox.box k).length/4)).map (fun a => key ((dir,tally k,tally s),batchTicket a)) := by
  simp [emitted,polyPush,passOrder_tally,List.map_map,Function.comp_def]

/-- A Fourier interpreter ticket contains the width, direction and stage index
in the order used by the public dispatcher. -/
def ticketQuery (t : FixedLayerTickets.Ticket) : Query := (t.2.2.1,t.2.1,t.2.2.2)

theorem ticketQuery_easy : Easy ticketQuery := by unfold ticketQuery; fun_prop

end ShortFourier.BatchWord.PermDirectory

end NearSquareRoot
end Computability
end OAI
