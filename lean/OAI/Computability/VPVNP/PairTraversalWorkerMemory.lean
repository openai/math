import OAI.Computability.VPVNP.PairTraversalRowExecution

/-!
# Publishing a descriptor header before the identifier scan

The site's source identifiers lie below the header, and the translated row
starts immediately after the two header words. Thus the header writes and
the scan can be interchanged, even if the count was read from a header word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.DescriptorRows

open BurstRAM
open scoped Fin.CommRing

/-- Writing the two saved header values first gives the same complete external
memory as publishing them after the scan. -/
theorem headers_then_scan {w : ℕ} (m : Memory w) (node src : ℕ)
    (countCell base stride : Word w) (count : ℕ)
    (sourceBefore : src + count ≤ node) (fit : node + 2 + count < 2 ^ w) :
    rowMemory src (node + 2) count base stride
      (writeMemory (writeMemory m (node : Word w) ((node + 2 : ℕ) : Word w))
        ((node + 1 : ℕ) : Word w) (m countCell.val)) =
      passMemory m node src (node + 2) countCell base stride count := by
  have nodeVal : (node : Word w).val = node := Nat.mod_eq_of_lt (by omega)
  have nextVal : ((node + 1 : ℕ) : Word w).val = node + 1 := Nat.mod_eq_of_lt (by omega)
  funext i
  simp only [passMemory, rowMemory, writeMemory, nodeVal, nextVal]
  by_cases inside : node + 2 ≤ i ∧ i < node + 2 + count
  · have source : src + (i - (node + 2)) < node := by omega
    simp only [ite_eq_left inside, ite_eq_right (by omega : i ≠ node),
      ite_eq_right (by omega : i ≠ node + 1), ite_eq_right source.ne,
      ite_eq_right (by omega : src + (i - (node + 2)) ≠ node + 1)]
  · simp only [ite_eq_right inside]

end PairSimulation.DescriptorRows

end VPVNP
end Computability
end OAI
