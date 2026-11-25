import OAI.Computability.BorderVNP.FiniteDiagonalCubeHostWeight
import OAI.Computability.BorderVNP.PackedBankInheritedValue
import OAI.Computability.BorderVNP.PackedInheritedFieldWeight

/-! # Expanding the field-valued host into all actual sparse private work tapes

The independently opened endpoints supply each inherited site's incoming
lanes in the same order as the public geometry. Each site's tensor entry
is the sum of its field-weighted observations over all private work bits.
Distributing these sums retains every successful sign and selected scalar
ID, as well as zero-valued observations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open Crossing Packing Packing.Inherited BorderVNP.Cube.Physical
open scoped BigOperators Classical

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits} {F : Type*} [Field F]

/-- The inherited sparse directories realizing the actual field table of
one selected packed host. -/
structure FieldSiteDirectory (N : Network D P bits) (T : N.Tables F) where
  /-- Edge directory capacity. -/
  edgeCapacity : ℕ
  /-- External port directory capacity. -/
  portCapacity : ℕ
  /-- The actual numbered edge and port rows. -/
  edgeID : N.Edge ↪ Fin edgeCapacity
  /-- Public row number of each external port. -/
  portID : P ↪ Fin portCapacity
  /-- Sparse field site attached at each original position. -/
  site : N.Site → Inherited.Site
  /-- Every numbered scalar entry has a fixed field value. -/
  values : ℕ → F
  /-- Incident rows supply the precise width recorded at the site. -/
  incoming : ∀ v, (site v).incoming = Inherited.incoming N v
  /-- Field-valued site realizations, propagated through the genuine history. -/
  models : ∀ v, (site v).Models N edgeID portID v (incoming v) (fieldWeight values) T

namespace FieldSiteDirectory

variable {T : N.Tables F} (S : FieldSiteDirectory N T) (L : FieldPacketPlan N F)

/-- All private work bits of all inherited sparse sites, in their actual local lengths. -/
abbrev Work := ∀ v : N.Site, Fin (S.site v).work → Bool

/-- The incoming lanes, after the two packet endpoints have been opened. -/
noncomputable def input (x : Ports bits) (a : L.Path) (v : N.Site) :
    Fin (S.site v).incoming → Bool :=
  fun k => inputWords N S.edgeID S.portID v
    (fun i => siteWord N L.cell v i a.1 (fun dir j => readEnd a.2.1 a.2.2.1 dir (L.slot j)))
    (fun p => x p.val) (Fin.cast (S.incoming v) k)

/-- Actual scalar contribution of one site's parsed list of signs and table positions. -/
noncomputable def siteValue (x : Ports bits) (a : L.Path) (v : N.Site)
    (work : Fin (S.site v).work → Bool) : F :=
  ((S.site v).observe (Inherited.bits work (S.input L x a v))).elim 0 (fieldWeight S.values)

/-- The row validity tests and private factors are now all evaluated at
fixed bits, without contracting any hidden original or paid site. -/
noncomputable def hostValue (x : Ports bits) (a : L.Path) (work : S.Work) : F :=
  if ∀ z ∉ Set.range L.slot, readEnd a.2.1 a.2.2.1 false z = false ∧ readEnd a.2.1 a.2.2.1 true z = false then
    ∏ v, S.siteValue L x a v (work v)
  else 0

/-- Product of the fully opened host and cube on one complete assignment. -/
noncomputable def pathValue (x : Ports bits) (a : L.Path) (work : S.Work) : F :=
  S.hostValue L x a work * cubeTermWeight L.table (fun _ _ => 1) a.2

/-- Each host entry at independently supplied endpoint words has the full
sum over the real site work bits, including all bottom private choices. -/
theorem host_eq_sum (x : Ports bits) (a : L.Path) :
    L.scalarHost T x a.1 a.2.1 a.2.2.1 = ∑ work : S.Work, S.hostValue L x a work := by
  by_cases hp : ∀ z ∉ Set.range L.slot, readEnd a.2.1 a.2.2.1 false z = false ∧
      readEnd a.2.1 a.2.2.1 true z = false
  · simp only [FieldPacketPlan.scalarHost,hostValue,ite_eq_left hp]
    let read (v : N.Site) := T v
      (fun i => siteWord N L.cell v i a.1 (fun dir j => readEnd a.2.1 a.2.2.1 dir (L.slot j)))
      (fun p => x p.val)
    trans ∏ v, read v
    · exact Fintype.prod_fiberwise L.cell read
    · refine (Finset.prod_congr rfl (fun v _ => (S.models v _ _).symm)).trans ?_
      exact Fintype.prod_sum (S.siteValue L x a)
  · simp only [FieldPacketPlan.scalarHost,hostValue,ite_eq_right hp,Finset.sum_const_zero]

/-- At every full cube assignment, the true scalar weight is the sum of
the sparse physical table products on the fine work assignments. -/
theorem weight_eq_sum (x : Ports bits) (a : L.Path) :
    L.weight T x a = ∑ work : S.Work, S.pathValue L x a work := by
  rw [L.weight_eq_cubeTermWeight]
  simp only [pathValue,← Finset.sum_mul]
  simp only [cubeTermWeight,one_mul]
  rw [S.host_eq_sum L x a]

end FieldSiteDirectory
end FiniteDiagonal

end BorderVNP
end Computability
end OAI
