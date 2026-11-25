import OAI.Hierarchy.DescentRotorTables
import Mathlib.Data.Fintype.Perm

namespace OAI
/-! # Static lookups for the entries of the fixed finite rotor menu -/

namespace Hierarchy.DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat
open RouteUnits
open scoped Classical BigOperators
noncomputable section

variable {Y : ℕ} (c : Fin Y → Fin Y → ℕ) (C w : ℕ)

abbrev Entry :=
  Equiv.Perm (Fin Y) × Σ v : Fin Y,
    Fin (2^w) × Fin (2^w) × (supplyGraph c).State (fun _ => Fin (2^(C*w))) v

/-- The layout, site, two external words and all incident supply words are
encoded together in one key, independent of the number of replicas. -/
def key (e : Entry c C w) : Fin (Fintype.card (Entry c C w)) := Fintype.equivFin _ e

theorem key_injective : Function.Injective (key c C w) := (Fintype.equivFin _).injective

variable {F : Type*}
variable (tab : Equiv.Perm (Fin Y) → (v : Fin Y) → Fin (2^w) → Fin (2^w) →
  (supplyGraph c).State (fun _ => Fin (2^(C*w))) v → F)

/-- The field entries belong to static advice and are read back verbatim. -/
def rom (i : Fin (Fintype.card (Entry c C w))) : F :=
  let e : Entry c C w := (Fintype.equivFin _).symm i
  tab e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2

theorem rom_read (π : Equiv.Perm (Fin Y)) (v : Fin Y) (x y : Fin (2^w))
    (a : (supplyGraph c).State (fun _ => Fin (2^(C*w))) v) :
    rom c C w tab (key c C w (π,⟨v,x,y,a⟩))=tab π v x y a := by
  let applyEntry (b : Entry c C w) : F := tab b.1 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2
  exact congrArg applyEntry ((Fintype.equivFin (Entry c C w)).symm_apply_apply (π,⟨v,x,y,a⟩))

/-- Every address fits the growing half-word once the input length is large
relative to the fixed rotor. The address alphabet depends only on the previously
chosen finite host and width. -/
theorem eventually_key_fits :
    ∀ᶠ H : ℕ in Filter.atTop,Fintype.card (Entry c C w)≤2^(H/2) := by
  filter_upwards [Filter.eventually_ge_atTop (2*Fintype.card (Entry c C w))] with H big
  exact le_trans (by omega : Fintype.card (Entry c C w)≤H/2) Nat.lt_two_pow_self.le

end
end Hierarchy.DescentRotor

end OAI
