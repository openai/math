import OAI.Hierarchy.DescentRetainedMovedRange
import OAI.Hierarchy.DescentRetainedPacketMask

namespace OAI
/-! # The actual home and original-order controls of each retained operand -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSIMDLookup DescentRetainedControl DescentRotorWindowArchive DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentSharedCableNames.Stage DescentSharedLeafLookup DescentSharedBookScan
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (C : DescentResetOperandSetup.Chart)
local notation "L" => C.retained
local notation "D" => C.seven.degree
local notation "H" => (L).hosts
local notation "G" => (L).grouped
local notation "cap" => C.seven.capacity
local notation "field" => C.seven.packetBits
variable (which : C.seven.control.Targets) (X : C.seven.Packets)
variable {n r : ℕ} (own : Fin C.retained.hosts→Fin C.retained.grouped→Fin C.retained.donors→ℕ) (next : Fin C.retained.hosts→Fin C.seven.degree→Option (Fin C.retained.hosts))
    (marks : Fin C.retained.hosts→Fin C.retained.grouped→Fin C.retained.donors→Fin (2*C.seven.capacity)→Option (Live C.seven.degree C.seven.capacity))
    (rank : Fin C.retained.hosts→Fin (width r (2^n) C.seven.degree)→ℕ) (ord : Fin C.retained.hosts→Fin C.retained.grouped→Fin C.retained.donors→Fin C.retained.donors→Bool)
    (quota : Fin C.retained.hosts→Fin C.seven.degree→Fin C.seven.degree→Fin 6→Cell C.seven.packetBits)
variable (h : Fin C.retained.hosts) (g : Fin C.retained.grouped)
    (printed : X h g=encode C.seven.packetBits _ (RootSources.paddedRow own next marks rank ord quota h g))
include printed in
theorem issued_selectors (t : Fin C.placement.shapes) (target : ℕ) (atTarget : which t=some target)
    (positive : 0<field) (fit : ∀d,own h g d<2^field) :
    ownerAt C which X t h g=(fun d=>decide (own h g d/2=target)) ∧
      priorAt C X h g=ord h g := by
  constructor
  · funext d
    simp only [ownerAt,printed,atTarget,Equiv.symm_apply_apply,RootSources.paddedRow,
      observed,inputs,Fin.val_natCast,Nat.mod_eq_of_lt (fit d)]
    simp [eq_comm]
  · funext i j
    simp only [priorAt,printed,Equiv.symm_apply_apply,RootSources.paddedRow,observed]
    cases ord h g i j <;>simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow positive.ne')]

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
