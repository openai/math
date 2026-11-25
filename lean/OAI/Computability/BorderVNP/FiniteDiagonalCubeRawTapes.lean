import OAI.Computability.BorderVNP.FiniteDiagonalCubeDirectories
import OAI.Computability.BorderVNP.CubePhysicalNativeAssignments

/-! # Actual selector-dependent routed payloads and flat private cell work bits

The flat private vector of each cell starts with its internal cables and
then carries all inherited work slabs. These slabs include every underlying
bottom choice and every value tested by the stored sparse directory. Reading
them at their numbered site intervals is inverse to constructing the raw
private vector, before any field value or sign has been discarded.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldSiteDirectory

open Crossing Packing.CellAddresses BorderVNP.Cube BorderVNP.Cube.Physical Physical.NativeAssignments
open scoped BigOperators Classical

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000

variable {D m teams : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] {T : N.Tables F} (S : FieldSiteDirectory N T) (L : FieldPacketPlan N F)
  (siteID : N.Site ↪ Fin m)
  (owners : (Packet L.dimension L.alphabet L.blocks → Selector L.dimension L.alternatives L.copies) →
    Fin L.alphabet → Fin teams)

/-- The true size of each inherited work slab. -/
abbrev workWidth (v : N.Site) := (S.site v).work

/-- Every bit of the actual flat private region of each cell. -/
abbrev FlatWork := ∀ c : L.Cell, Fin (externalBase N L.cell c S.workWidth) → Bool

/-- Read the unique inherited work word at its real local site interval. -/
noncomputable def workOfFlat (raw : S.FlatWork L) : S.Work := fun v =>
  siteWords N L.cell (L.cell v) siteID S.workWidth
    (privateStaging N L.cell S.workWidth (L.cell v) (raw (L.cell v))) ⟨v,rfl⟩

/-- In each cell the private suffix of the real tape recovers all its
sites' private work vectors at their physical slab offsets. -/
theorem workOfFlat_cell (raw : S.FlatWork L) (c : L.Cell) (v : {v : N.Site // L.cell v = c}) :
    S.workOfFlat L siteID raw v.val =
    siteWords N L.cell c siteID S.workWidth (privateStaging N L.cell S.workWidth c (raw c)) v := by
  rcases v with ⟨v,hv⟩
  subst c
  rfl

/-- One assignment of the actual shared and co-located payload lanes and
one independent physical work vector per cell. -/
abbrev RoutedRaw :=
  Routed (b := L.bitWidth) (s := L.supply) owners × S.FlatWork L

/-- The entire raw field evaluator choice space is the product of the
original site work vectors and all independently assigned post-cube bits. -/
noncomputable def routedRawEquiv : S.RoutedRaw L owners ≃ (S.Work × L.Path) := by
  let expected (work : S.Work) (_ : Routed (b := L.bitWidth) (s := L.supply) owners) :
      Expected N L.cell S.workWidth := fun _ _ v => work v.val
  let extract (_ : Routed (b := L.bitWidth) (s := L.supply) owners) (raw : S.FlatWork L) :=
    S.workOfFlat L siteID raw
  let checked : S.RoutedRaw L owners ≃ CheckedCells N L.cell siteID S.workWidth owners expected extract :=
    { toFun := fun ⟨q,raw⟩ => ⟨q,raw,fun c => funext (fun v => (S.workOfFlat_cell L siteID raw c v).symm)⟩
      invFun := fun ⟨q,raw⟩ => ⟨q,raw.val⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply checked.trans
  apply NativeAssignments.checkedPathEquiv N L.cell S.edgeID siteID S.workWidth owners expected extract
  intro q work raw
  funext v
  exact congrFun (raw.property (L.cell v)) ⟨v,rfl⟩

private theorem sum_prod_explicit {A B K : Type*} [AddCommMonoid K]
    (a : Fintype A) (b : Fintype B) (c : Fintype (A × B)) (f : A × B → K) :
    (∑ i ∈ @Finset.univ A a, ∑ j ∈ @Finset.univ B b, f (i,j)) =
      ∑ v ∈ @Finset.univ (A × B) c, f v := by
  let := a
  let := b
  refine (Fintype.sum_prod_type f).symm.trans ?_
  exact congrArg (fun inst : Fintype (A × B) => ∑ v ∈ @Finset.univ _ inst, f v)
    (Subsingleton.elim _ c)

/-- The sum over actual flat local private vectors and selector-dependent
payloads equals the field tensor on all independently supplied port values. -/
theorem value_eq_raw_sum (x : Ports bits) :
    N.value T x = ∑ raw : S.RoutedRaw L owners,
      let a := S.routedRawEquiv L siteID owners raw
      S.pathValue L x a.2 a.1 := by
  rw [L.value_eq_sum T x]
  calc
    (∑ a : L.Path, L.weight T x a) =
        ∑ a : L.Path, ∑ work : S.Work, S.pathValue L x a work :=
      Finset.sum_congr rfl (fun a _ => S.weight_eq_sum L x a)
    _ = ∑ work : S.Work, ∑ a : L.Path, S.pathValue L x a work := Finset.sum_comm
    _ = ∑ p : S.Work × L.Path, S.pathValue L x p.2 p.1 := sum_prod_explicit _ _ _ (fun p : S.Work × L.Path => S.pathValue L x p.2 p.1)
    _ = _ := ((S.routedRawEquiv L siteID owners).sum_comp (fun p => S.pathValue L x p.2 p.1)).symm

end FiniteDiagonal.FieldSiteDirectory

end BorderVNP
end Computability
end OAI
