import OAI.Computability.BorderVNP.PackedInheritedWorkDirectory
import OAI.Computability.BorderVNP.PackedBottomBoxInterpreter
import OAI.Computability.BorderVNP.PackedBankInheritedSiteCharges
import OAI.Computability.BorderVNP.DiagonalExternalSewFields

/-! # Private work of the true repeated original boxes

The fixed fine/report padding is present only at live original rows. The
remaining work is exactly the physical incoming width of the repeated cable
and exterior rectangles. Computing this width by the virtual scan also
covers empty and zero-copy sites without inspecting any opaque box.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing BottomRepeat BottomReports InheritedBank CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open Diagonal.ExternalSew.FieldExport
open scoped Classical

variable {D s m n C d k w : ℕ} {A : Type} [Fintype A] {bits : A → ℕ} (N : Network D A bits)

/-- Grouping all copies scales the true incoming area by their multiplicity. -/
theorem incoming_wide (copies : ℕ) (v : N.Site) : incoming (wide N copies) v = copies*incoming N v := by
  rw [incoming_eq_widths,incoming_eq_widths,Nat.mul_add]
  unfold incidentWidth portWidth
  rw [Finset.mul_sum,Finset.mul_sum]

variable {σ : Type*} [Fintype σ] (occupied : Fin s → Bool)

/-- Length-only padding on the fixed original site rectangle. The same two
literal wires supply every bit of all rows. -/
noncomputable def bottomPad (w amount : ℕ) : Frame σ (Fin s × Fin w) :=
  (constants σ).select fun z => constPins w (if occupied z.1 then amount else 0) z.2

theorem bottomPad_size (amount : ℕ) : (bottomPad (σ := σ) occupied w amount).size ≤ 2 := by
  simpa only [bottomPad,Frame.select_size] using constants_size σ

variable (F : Fields s m n C d k w σ) (site : N.Site ↪ Fin s) (edge : N.Edge ↪ Fin m) (port : A ↪ Fin n)
variable (copies capFine capReport : ℕ)
local notation3 "G₀" => wide N copies
local notation3 "prefix" => copies*(capFine+capReport)
local notation3 "stride" v => bottomStride (capFine+incoming N v) capReport

/-- The computed original work table agrees with the repeated program for
every opaque factor list, using the true grouped endpoint pins. -/
theorem bottom_covers (x : σ → Bool)
    (rep : Views.EndpointData (wide N copies) F site edge port x)
    (mask : ∀ i, occupied i = true ↔ i ∈ Set.range site)
    (boxes : N.Site → List CellSparse.Factor)
    (room : ∀ v, copies * bottomStride (capFine+incoming N v) capReport < 2^w) :
    let f := (exists_extent F (bottomPad occupied w (copies*(capFine+capReport)))).choose
    Covers site (fun v => (bornWith N edge port v copies capFine (stride v) (boxes v)).work) f x := by
  intro f
  let pad := bottomPad (σ := σ) occupied w prefix
  let temp (v : N.Site) : Site := ⟨prefix,incoming G₀ v,[],[]⟩
  have total (v : N.Site) : (temp v).size = copies * stride v := by
    simp only [temp,Site.size,incoming_wide,bottomStride]
    ring
  have hpad : Covers site (fun v => (temp v).work) pad x := by
    constructor
    · intro v
      have hv := (mask (site v)).mpr ⟨v,rfl⟩
      have fit : prefix < 2^w := (Nat.le_add_right prefix (incoming G₀ v)).trans_lt ((total v).trans_lt (room v))
      simpa only [pad,bottomPad,Frame.select_eval,hv,ite_true,temp,Function.comp_def] using
        constPins_value x w prefix fit
    · intro i hi
      have hn : occupied i = false := Bool.eq_false_iff.mpr (fun h => hi ((mask i).mp h))
      simpa only [pad,bottomPad,Frame.select_eval,hn,Bool.false_eq_true,ite_false,Function.comp_def] using
        constPins_value x w 0 (Nat.two_pow_pos w)
  have h := extent_covers G₀ F site edge port pad rep temp (fun _ => rfl) hpad
    (fun v => (total v).trans_lt (room v)) f ((exists_extent F pad).choose_spec.2 x)
  constructor
  · intro v; exact (h.live v).trans (total v)
  · exact h.hole

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
