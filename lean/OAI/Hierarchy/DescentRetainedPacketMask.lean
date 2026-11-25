import OAI.Hierarchy.DescentPreparedRotorInputs
import OAI.Hierarchy.DescentRetainedControlWord

namespace OAI
/-! # Measured earlier socket and original-coordinate comparison in the retained route -/
namespace Hierarchy.DescentRetainedControl
open DescentSIMDLookup DescentRotorWindowArchive DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentSharedCableNames.Stage DescentSharedLeafLookup DescentSharedBookScan
open scoped Classical Fin.CommRing
noncomputable section
variable {H G field D L cap n r : ℕ}
variable (own : Fin H→Fin G→Fin L→ℕ) (next : Fin H→Fin D→Option (Fin H))
    (marks : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H→Fin (width r (2^n) D)→ℕ) (ord : Fin H→Fin G→Fin L→Fin L→Bool)
    (quota : Fin H→Fin D→Fin D→Fin 6→Cell field)
theorem padded_selector (h : Fin H) (g : Fin G) (target : ℕ) (pos : 0<field) (fits : ∀j,own h g j<2^field) :
    let raw:=encode field _ (RootSources.paddedRow own next marks rank ord quota h g)
    filter (D:=D) (L:=L) (cap:=cap) (some target) raw =
      vector (fun i=>decide (own h g i/2=target)) (ord h g):=by
  intro raw
  rw [show raw=encode field _ (RootSources.paddedRow own next marks rank ord quota h g) from rfl,from_packet]
  congr 1
  · funext j
    simp only [RootSources.paddedRow,Equiv.symm_apply_apply,observed,inputs,Fin.val_natCast,Nat.mod_eq_of_lt (fits j)]
    simp [eq_comm]
  · funext i j
    simp only [RootSources.paddedRow,Equiv.symm_apply_apply,observed]
    cases e:ord h g i j <;>simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow pos.ne')]

end
end Hierarchy.DescentRetainedControl

end OAI
