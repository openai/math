import OAI.Computability.BorderVNP.FinitePrewireGeometry
import OAI.Computability.BorderVNP.FinitePrewireOuter
import OAI.Computability.BorderVNP.PackedGridBatch

/-! # Prewiring the terminals of any trivalent finite-field input network -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FinitePrewire

open Crossing ParseBatch
open scoped BigOperators Classical

variable {D : ℕ} {X Y I : Type} [Fintype X] [Fintype Y] [Fintype I]
    (f : X → (Y ⊕ I) ⊕ Bool) (B : Network D X (fun _ => 1))

/-- The freely visible Y bits are leaves. All original X terminals have become
internal join cables, with I variables summed by the bounded-degree fanout component. -/
noncomputable abbrev wired := sewn ((outer f).network.inDimension D) B

/-- Install the equality/clamp tests along with the *given* tensor tables of B. -/
noncomputable def wiredTables {A : Type*} [CommSemiring A] (table : B.Tables A) : (wired f B).Tables A :=
  sewnTables ((outer f).network.inDimension D) B ((outer f).tables (test f)) table

/-- Even if many old terminals share one private variable, this contraction
sums that variable once and pins every literal zero before routing. -/
theorem wired_value {A : Type*} [CommSemiring A] (table : B.Tables A) (y : Y → Bool) :
    (wired f B).value (wiredTables f B table) (fun p _ => y p) =
    ∑ h : I → Bool, B.value table (fun x _ => Prewire.readInput f y h x) := by
  refine (value_sewn ((outer f).network.inDimension D) B ((outer f).tables (test f)) table y).trans ?_
  have hv (x : X → Bool) :
      ((outer f).network.inDimension D).value ((outer f).tables (test (A := A) f))
        (fun p _ => p.elim y x) = ∑ h : I → Bool, if x = Prewire.readInput f y h then 1 else 0 :=
    outer_value f y x
  simp_rw [hv,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro h _
  simp [ite_mul]

/-- No local table of the proposed network increases in degree when its ports
become join edges. Several ports may originally be attached at the same site. -/
theorem wired_trivalent (hb : B.Trivalent) : (wired f B).Trivalent :=
  trivalent_sewn _ B (outer_trivalent f) hb

/-- The retained public field bits have distinct physical input leaves. -/
theorem wired_attach_injective : Function.Injective (wired f B).attach :=
  sewn_attach_injective _ B (outer f).distinct_input_leaves

/-- The full prewiring costs at most fifteen sites, edges and terminals per
old visible input bit, in addition to the proposed network's original volume. -/
theorem wired_volume (h : Fintype.card Y + Fintype.card I ≤ Fintype.card X) :
    (wired f B).bitVolume ≤ B.bitVolume + 15*Fintype.card X := by
  have hv := sewn_volume ((outer f).network.inDimension D) B
  have ho : ((outer f).network.inDimension D).bitVolume ≤ 15*Fintype.card X := outer_volume f h
  change (sewn ((outer f).network.inDimension D) B).bitVolume ≤ _
  omega

end FinitePrewire

end BorderVNP
end Computability
end OAI
