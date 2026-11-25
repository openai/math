import OAI.Computability.IntegerMultiplication.Strip.Route
import OAI.Computability.NearSquareRoot.BoundedProgram

/-! # Routing one color class by its Boolean masks

One fixed command selects the payloads marked in source order and places them
in the marked destination slots. Source and destination masks are ordinary input
streams, independent of the radix and the address transformation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMColors

open IntegerMultiplication.Code Space

abbrev Data := List Tree × List Bool × List Bool

private def sourcePairs (d : Data) :=
  (cutLists (ruler d.2.1, zipSafe false (.atom false) (d.2.1, d.1))).1

/-- The class stream at destination positions, with at most one payload per slot. -/
def pass (d : Data) : List (List Tree) :=
  Ribbon.dress true (d.2.2, Ribbon.read true (sourcePairs d))

theorem pass_easy : Easy pass := by
  have masks : Easy (fun d : Data => d.2.1) := by fun_prop
  have source : Easy (fun d : Data => d.1) := Easy.fst
  have pairs : Easy sourcePairs :=
    (easy_cut ((Easy.ruler masks).pair (easy_zipSafe false (Tree.atom false) (masks.pair source)))).fstCompose
  exact ((show Easy (fun d : Data => d.2.2) by fun_prop).pair
    (Ribbon.easyRead true pairs)).compose (Ribbon.easyDress true)

private theorem sourcePairs_map (s : List (Bool × Tree)) (mask : List Bool) :
    sourcePairs (s.map Prod.snd, s.map Prod.fst, mask) = s := by
  have prefixEq (r : List (Bool × Tree)) (a : List Bool) (b : List Tree) :
      ((r.map Prod.fst ++ a).zip (r.map Prod.snd ++ b)).take r.length = r := by
    induction r with
    | nil => simp
    | cons x r ih => simpa [List.zip] using congrArg (List.cons x) ih
  simpa only [sourcePairs, cutLists, ruler_length, zipSafe, List.length_map] using
    prefixEq s (List.replicate s.length false) (List.replicate s.length (.atom false))

/-- Equal class subsequences express the within-class order condition used in
the affine address permutation. -/
theorem pass_eq {s d : List (Bool × Tree)} (agree : Ribbon.read true s = Ribbon.read true d) :
    pass (s.map Prod.snd, s.map Prod.fst, d.map Prod.fst) = d.map (Ribbon.keep true) := by
  rw [pass, sourcePairs_map, agree, Ribbon.frame]

/-- A single P192 command processes every mask and every list of payload trees,
using linear time and space in the encoded input size. -/
theorem pass_program : BoundedTask size size (send (X := Data)) (send ∘ pass) := by
  apply (BoundedTask.of_time pass_easy).bound 1 2
  · simp
  · intro d
    change size d + size d + 1 ≤ 2 * (size d + 1)
    omega

end InterchangeROMColors

end NearSquareRoot
end Computability
end OAI
