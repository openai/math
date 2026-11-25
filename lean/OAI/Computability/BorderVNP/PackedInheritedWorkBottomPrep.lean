import OAI.Computability.BorderVNP.PackedInheritedWorkBottom
import OAI.Computability.BorderVNP.PackedInheritedWorkPrepFrame

/-! # Initial work and extent from the grouped seed's emitted endpoints -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords.BottomPrep

open Crossing CellAddressCircuit CellAddressViews BottomRepeat BottomReports
open Shortening.PublicEndpoints PackedHistoryCircuit Diagonal.ExternalSew.FieldExport VPVNP.VerifierNetwork
open scoped Classical

variable {V E n w : ℕ} {σ Geo Data : Type} [Fintype σ] [Fintype Geo]
    (geom : Frame σ Geo) (read : Inputs Data V E w w → Geo) (ports : Ports n)
    (fits : V ≤ 2^w) (occupied : Fin V → Bool) (copies fine report : ℕ)

private abbrev fields := TerminalCells.endpointFields fits read ports.host ports.width
private noncomputable abbrev work := (exists_extent (fields read ports fits)
  (bottomPad occupied w (copies*(fine+report)))).choose
private noncomputable abbrev widths := (exists_directory (fields read ports fits)
  (work read ports fits occupied copies fine report)).choose

/-- Run the shared geometric seed once, compute the private work slab, and add the current
incidences to obtain the full extent. The original geometric pins are retained in the output. -/
noncomputable def frame : Frame σ (WithWidths Geo V w) :=
  (((widths read ports fits occupied copies fine report).subst (constants Geo)).withInput).subst geom

/-- Cost of both incidence passes and word additions, in addition to the shared seed initializer. -/
theorem frame_size : (frame geom read ports fits occupied copies fine report).size ≤
    geom.size + 2*Prep.charge V E n w := by
  have hs := (exists_directory (fields read ports fits) (work read ports fits occupied copies fine report)).choose_spec.1
  have hw := (exists_extent (fields read ports fits) (bottomPad occupied w (copies*(fine+report)))).choose_spec.1
  have hp := bottomPad_size (σ := Geo ⊕ Bool) (w := w) occupied (copies*(fine+report))
  have he := Views.frame_size (fields read ports fits)
  have hc := constants_size Geo
  change (widths read ports fits occupied copies fine report).size ≤ _ at hs
  change (work read ports fits occupied copies fine report).size ≤ _ at hw
  simp only [frame,Frame.subst_size,Frame.withInput_size,Prep.charge]
  omega

/-- All unaugmented words come from the same original seed initializer. -/
theorem frame_geometry (x : σ → Bool) :
    (frame geom read ports fits occupied copies fine report).eval x ∘ Sum.inl = geom.eval x := by
  funext j
  simp [frame]

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (site : N.Site ↪ Fin V) (edge : N.Edge ↪ Fin E) (dummy : Fin E → N.Site) (port : P ↪ Fin n)
    (boxes : N.Site → List CellSparse.Factor)
local notation3 "birth" v => bornWith N edge port v copies fine (bottomStride (fine+incoming N v) report) (boxes v)

/-- At each occupied row the two actual gate words are the size fields of the executable
repeated box with its own private factors. Both columns evaluate to zero in every hole. -/
theorem frame_covers (x : σ → Bool)
    (ready : Represents (wide N copies) site edge dummy (geom.eval x ∘ read))
    (header : ports.Reads (wide N copies) site port) (width : ∀ j, ports.width j < 2^w)
    (mask : ∀ j, occupied j = true ↔ j ∈ Set.range site)
    (room : ∀ v, (birth v).size < 2^w) (b : Bool) :
    Covers site (fun v => if b then (birth v).size else (birth v).work) (assignedColumn b)
      ((frame geom read ports fits occupied copies fine report).eval x) := by
  let x₀ := geom.eval x
  let y := (constants Geo).eval x₀
  let fld := fields read ports fits
  let wrk := work read ports fits occupied copies fine report
  let both := widths read ports fits occupied copies fine report
  have rep := TerminalCells.named_endpoints fits read ports.host ports.width (wide N copies) site edge dummy port x₀
    ready header.attach header.size width header.hole
  have wr := bottom_covers N occupied fld site edge port copies fine report y rep mask boxes
    (fun v => (Nat.le_add_right _ _).trans_lt (room v))
  have ⟨_,hw,he⟩ := (exists_directory fld wrk).choose_spec
  have h := directory_covers fld wrk (wide N copies) site edge port rep (fun v => birth v)
    (fun _ => rfl) wr room both (hw y) (he y)
  have ev (c : Bool) (i : Fin V) (j : Fin w) :
      (assignedColumn c).eval ((frame geom read ports fits occupied copies fine report).eval x) (i,j) =
        (column both c).eval y (i,j) := by
    simp [assignedColumn,frame,column,both,y,x₀]
  cases b
  · exact h.1.of_bits (ev false)
  · exact h.2.of_bits (ev true)

end Packing.Inherited.WorkWords.BottomPrep

end BorderVNP
end Computability
end OAI
