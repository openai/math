import OAI.ThreeFlat.Routing.BitonicSchedule
import OAI.ThreeFlat.Routing.BitonicComparator

namespace OAI
/-! # An ascending bitonic sorter on binary records -/

noncomputable section
open scoped Classical
namespace ThreeFlat.Routing.BitonicSort

open SortNetwork (Payload Records pack)

/-- The unique ascending array of the input words. -/
abbrev sorted {m u : ℕ} (X : Records m u) : Records m u := BitonicSchedule.sorted X

/-- Input bits followed by the proposed sorted output bits. -/
def network (K : Type*) [Zero K] [One K] (m u : ℕ) :
    BitNetwork K (Fintype.card (Payload m u) + Fintype.card (Payload m u)) :=
  BitonicSchedule.network m u (BitonicComparator.network K u)

theorem network_eval {K : Type*} [CommSemiring K] (m u : ℕ) (X Y : Records m u) :
    (network K m u).eval (Fin.append (pack X) (pack Y)) = if Y = sorted X then 1 else 0 :=
  BitonicSchedule.network_eval m u _ (BitonicComparator.network_eval u) X Y

theorem network_cells (K : Type*) [Zero K] [One K] (m u : ℕ) :
    (network K m u).cells ≤ 4096*(u+1)*(2^m)*(m+1)^2 :=
  BitonicSchedule.network_cells m u _ (BitonicComparator.network_cells K u)

theorem network_internal (K : Type*) [Zero K] [One K] (m u : ℕ) :
    (network K m u).internal ≤ 4096*(u+1)*(2^m)*(m+1)^2 :=
  BitonicSchedule.network_internal m u _ (BitonicComparator.network_internal K u)

end ThreeFlat.Routing.BitonicSort

end
end OAI
