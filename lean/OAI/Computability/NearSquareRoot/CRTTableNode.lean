import OAI.Computability.NearSquareRoot.CRTTableCoefficients
import OAI.Computability.NearSquareRoot.CRTTableElimination
import OAI.Computability.NearSquareRoot.CRTTableInput
import OAI.Computability.NearSquareRoot.CRTTablePadded
import OAI.Computability.NearSquareRoot.CRTTableRotation

/-! # Physical table generation for a controlled CRT tree join

One invocation consumes a direction bit, two lists of axis descriptors, and
the supplied control bits in MSF field order. It writes one full lookup table
per target axis. Both checking the control and solving its triangular system
are charged to the fixed polynomial-time stack program.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code

theorem residuals_poly : Poly residuals := by
  apply residuals_poly_of
  have eq : residualStep = subtractMul := by
    funext ⟨v,c,t,a⟩
    rw [← recover_tally (subtractMul (v,c,t,a)), subtractMul_length]
    rfl
  exact eq ▸ subtractMul_poly

abbrev NodeQuery := Bool × List Descriptor × List Descriptor × List Bool

def initialPacket (q : NodeQuery) : ControlPacket :=
  (q.2.1, q.2.2.1, coefficients ((q.2.1 ++ q.2.2.1).map Prod.snd), q.2.2.2)

private theorem packet_poly : Poly initialPacket := by
  have g : Poly (fun q : NodeQuery => (q.2.1 ++ q.2.2.1).map Prod.snd) :=
    (Poly.app (by fun_prop) (by fun_prop)).compose (Poly.maps _ Easy.snd.poly)
  exact (by fun_prop : Poly (fun q : NodeQuery => q.2.1)).pair
    ((by fun_prop : Poly (fun q : NodeQuery => q.2.2.1)).pair
      ((g.compose coefficients_poly).pair (by fun_prop)))

/-- An invalid control emits identity tables. The elimination starts the right
rows at zero, giving the negative shift, which the forward join must negate. -/
def chooseShift (s : (Bool × Bool) × Descriptor × Row) : Tally :=
  bif s.1.1 then
    bif s.1.2 then s.2.2.2.1 else inverseOffset (s.2.2.2.1,s.2.1.2)
  else []

private theorem chooseShift_poly : Poly chooseShift := by
  unfold chooseShift
  apply IntegerMultiplication.Code.Poly.choose (by fun_prop) _ (IntegerMultiplication.Code.Poly.const ([] : Tally))
  exact Poly.choose (by fun_prop) (by fun_prop)
    ((show Poly (fun s : (Bool × Bool) × Descriptor × Row =>
      (s.2.2.2.1,s.2.1.2)) by fun_prop).compose inverseOffset_poly)

def emitAxis (s : (Bool × Bool) × Descriptor × Row) : List Tally :=
  rotation (chooseShift s, s.2.1.2, padded s.2.1)

private theorem emitAxis_poly : Poly emitAxis :=
  (chooseShift_poly.pair ((by fun_prop : Poly (fun s : (Bool × Bool) × Descriptor × Row =>
    s.2.1.2)).pair ((by fun_prop : Poly (fun s : (Bool × Bool) × Descriptor × Row =>
    s.2.1)).compose padded_poly))).compose rotation_poly

def targetRows (q : NodeQuery) : List Row :=
  residuals (ruler q.2.1, (prepareRows (initialPacket q)).2)

private theorem targetRows_poly : Poly targetRows := by
  have l : Easy (fun q : NodeQuery => ruler q.2.1) := by fun_prop
  exact (l.poly.pair (packet_poly.compose prepareRows_poly).sndCompose).compose residuals_poly

/-- A true direction bit selects the inverse permutation. Each list in the
result enumerates the images of all padded coordinates in increasing order. -/
def nodeTables (q : NodeQuery) : List (List Tally) :=
  polyPush emitAxis (((prepareRows (initialPacket q)).1, q.1),
    zipFair ([],[]) ([],[],[]) (q.2.2.1, targetRows q))

theorem nodeTables_poly : Poly nodeTables := by
  have flags := (packet_poly.compose prepareRows_poly).fstCompose.pair
    (by fun_prop : Poly (fun q : NodeQuery => q.1))
  have rows := ((by fun_prop : Poly (fun q : NodeQuery => q.2.2.1)).pair targetRows_poly).compose
    (easy_zip (([],[]) : Descriptor) (([],[],[]) : Row)).poly
  exact (flags.pair rows).compose (Poly.push (false,false) (([],[]),([],[],[])) emitAxis_poly)

theorem emitAxis_entry (s : (Bool × Bool) × Descriptor × Row)
    (j : Fin (padded s.2.1).length) :
    ((emitAxis s)[j.val]'(by simp [emitAxis])).length =
      if j.val < s.2.1.2.length then (j.val + (chooseShift s).length)%s.2.1.2.length
      else j.val := rotation_entry ..

end CRTTable

end NearSquareRoot
end Computability
end OAI
