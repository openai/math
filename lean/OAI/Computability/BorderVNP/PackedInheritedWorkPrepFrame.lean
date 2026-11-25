import OAI.Computability.BorderVNP.PackedInheritedWorkBoundary
import OAI.Computability.BorderVNP.PackedInheritedWorkTransport
import OAI.Computability.BorderVNP.PackedInheritedWorkReturn
import OAI.Computability.BorderVNP.PackedInheritedWorkPorts
import OAI.Computability.BorderVNP.PackedInheritedWorkJoint

/-! # Compiling the subdivision's two width columns for a whole tuple of children -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords.Prep

open Crossing Shortening Shortening.PublicCapacity Shortening.PublicEndpoints
open PackedHistoryCircuit Diagonal.ExternalSew.FieldExport VPVNP.VerifierNetwork
open CellAddressCircuit CellAddressViews
open scoped Classical

variable {s : Shape} {V E w n : ℕ} (extra : ℕ) (hv : V = (s.subdivide extra).sites)
variable {σ B : Type} [Fintype σ]
variable (previous : Fin s.sites × Fin w → σ) (endpoint : Inputs B V E w w → σ)
variable (p : Ports n) (fit : V ≤ 2^w)

/-- Alias each original full extent, and introduce the shared zero for the inserted and
reserved sites. Transport the result to the stage's scheduled site rectangle. -/
noncomputable def workTable : Frame (σ ⊕ Bool) (Fin V × Fin w) :=
  (subdivision extra (Frame.initial (Sum.inl ∘ previous))).select fun z => (Fin.cast hv z.1,z.2)

private abbrev fields := TerminalCells.endpointFields fit endpoint p.host p.width

/-- One physical child's work and full extent. The width adder takes its incidence
area from the actual newly subdivided endpoint directory. -/
noncomputable def cell : Frame σ (Fin V × Bool × Fin w) :=
  (exists_directory (fields endpoint p fit) (workTable extra hv previous)).choose.subst (constants σ)

/-- Complete row cost, including the virtual endpoint sort and the row additions. -/
noncomputable def charge (V E n w : ℕ) :=
  6 + gateBound V E n V w w w + labelBound V E n w w +
    Fintype.card (View V E n V)*w*(60*w+16) + V*3*(100*(w+1)^2)

theorem cell_size : (cell extra hv previous endpoint p fit).size ≤ charge V E n w := by
  have hwork := subdivision_size extra (Frame.initial (Sum.inl ∘ previous : _ → σ ⊕ Bool))
  have hs := (exists_directory (fields endpoint p fit) (workTable extra hv previous)).choose_spec.1
  have hg := Views.frame_size (fields endpoint p fit)
  have hc := constants_size σ
  simp only [Frame.initial_size,zero_add] at hwork
  have h₀ : (workTable extra hv previous).size ≤ 1 := hwork
  simp only [cell,Frame.subst_size,charge]
  exact (Nat.add_le_add hc hs).trans (by omega)

variable {D : ℕ} {Q : Type} [Fintype Q] {bits : Q → ℕ} (N : Network D Q bits)
variable (sites : N.Site ↪ Fin V) (edges : N.Edge ↪ Fin E) (dummy : Fin E → N.Site) (ports : Q ↪ Fin n)
variable (x : σ → Bool) (programs : Site.Programs N)

/-- Reading the two generated rows at a named site gives the work or the full extent of
the actual installed program. Both words vanish on every vacant row. -/
theorem cell_covers
    (raw : Covers sites (fun v => (programs v).program.work) (workTable extra hv previous) ((constants σ).eval x))
    (ready : Represents N sites edges dummy (x ∘ endpoint)) (portOK : p.Reads N sites ports)
    (width : ∀ r, p.width r < 2^w) (room : ∀ v, (programs v).program.size < 2^w) (b : Bool) :
    Covers sites (fun v => if b then (programs v).program.size else (programs v).program.work)
      (column (cell extra hv previous endpoint p fit) b) x := by
  let fld := fields endpoint p fit
  let wrk := workTable extra hv previous
  let y := (constants σ).eval x
  have rep := TerminalCells.named_endpoints fit endpoint p.host p.width N sites edges dummy ports x ready
    portOK.attach portOK.size width portOK.hole
  have ⟨_,hw,he⟩ := (exists_directory fld wrk).choose_spec
  have res := directory_covers fld wrk N sites edges ports rep (fun v => (programs v).program)
    (fun v => (programs v).size) raw room (exists_directory fld wrk).choose (hw y) (he y)
  cases b
  · exact res.1.of_bits (fun _ _ => by simp only [cell,column,Frame.select_eval,Frame.subst_eval,fld,wrk])
  · exact res.2.of_bits (fun _ _ => by simp only [cell,column,Frame.select_eval,Frame.subst_eval,fld,wrk])

variable {k : ℕ} {Old : Type} [Fintype Old] [Fintype B]
local notation3 "old" => WithWidths Old s.sites w
local notation3 "geo" => SavedPins B V E w
local notation3 "allPins" => (Fin k × old) ⊕ (Fin k × geo)

variable (g : Frame (Fin k × Old) (Fin k × SavedPins B V E w))

/-- Read only the old extent of this child. Its geometric inputs are handled by the
common pass over the whole tuple. -/
def prevPin (i : Fin k) (z : Fin s.sites × Fin w) : allPins :=
  .inl (i,.inr (z.1,true,z.2))

/-- Newly computed cable pointer/width fields, selected from this child's geometric rows. -/
def endPin (i : Fin k) (z : Inputs B V E w w) : allPins := .inr (i,.inr (.inr z))

private noncomputable abbrev shapePass : Frame (Fin k × old) (Fin k × geo) :=
  g.subst (Frame.initial fun z => (z.1,.inl z.2))

private noncomputable abbrev children := fun i : Fin k => cell extra hv
  (prevPin (Old := Old) (B := B) (V := V) (E := E) i)
  (endPin (s := s) (Old := Old) i) p fit

/-- Evaluate the geometric subdivision just once, then compute both widths independently
on the endpoint table of each physical child. -/
noncomputable def batch : Frame (Fin k × WithWidths Old s.sites w)
    (Fin k × WithWidths (SavedPins B V E w) V w) :=
  let f := (exists_parallelFrames (children (Old := Old) (B := B) (E := E) (k := k) extra hv p fit)).choose
  (f.withInput.select (fun z => match z.2 with
    | .inl j => .inl (.inr (z.1,j))
    | .inr a => .inr ⟨z.1,a⟩)).subst (shapePass g).withInput

theorem batch_size : (batch extra hv p fit g).size ≤ g.size + 1 + k*charge V E n w := by
  let f := children (Old := Old) (B := B) (E := E) (k := k) extra hv p fit
  have h := (exists_parallelFrames f).choose_spec.1
  have each (i : Fin k) : (f i).size ≤ charge V E n w := cell_size ..
  have total : ∑ i, (f i).size ≤ k*charge V E n w := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)
  change ((exists_parallelFrames f).choose.withInput.select _ |>.subst (shapePass g).withInput).size ≤ _
  simp only [shapePass,Frame.subst_size,Frame.withInput_size,Frame.select_size,Frame.initial_size,zero_add]
  omega

variable (x' : Fin k × WithWidths Old s.sites w → Bool)

/-- The geometric assignment of each child in the augmented pre-frame. -/
theorem batch_geo (i : Fin k) (j : geo) : (batch extra hv p fit g).eval x' (i,.inl j) =
    g.eval (fun z => x' (z.1,.inl z.2)) (i,j) := by
  have eq : (Frame.initial (fun z : Fin k × Old => (z.1,Sum.inl z.2))).eval x' =
      fun z => x' (z.1,.inl z.2) := by funext z; exact Frame.initial_eval ..
  simp [batch,shapePass,Frame.subst_eval,eq]

/-- Each width pin belongs to the child whose incidence pass was evaluated on these
exact geometric outputs. -/
theorem batch_width (i : Fin k) (b : Bool) (r : Fin V) (j : Fin w) :
    (batch extra hv p fit g).eval x' (i,.inr (r,b,j)) =
      (cell extra hv (prevPin i) (endPin i) p fit).eval
        (Sum.elim x' (g.eval (fun z => x' (z.1,.inl z.2)))) (r,b,j) := by
  let f := children (Old := Old) (B := B) (E := E) (k := k) extra hv p fit
  let full := Sum.elim x' (g.eval (fun z => x' (z.1,.inl z.2)))
  have geom : (Frame.initial (fun z : Fin k × Old => (z.1,Sum.inl z.2))).eval x' =
      fun z => x' (z.1,.inl z.2) := by funext z; exact Frame.initial_eval ..
  have eq : (shapePass g).withInput.eval x' = full := by
    funext z
    cases z with
    | inl z => simp [full]
    | inr z => simp [full,shapePass,Frame.subst_eval,geom]
  have h := (exists_parallelFrames f).choose_spec.2 full i (r,b,j)
  simpa only [batch,Frame.subst_eval,Frame.select_eval,Frame.withInput_eval_inr,eq] using h

end Packing.Inherited.WorkWords.Prep

end BorderVNP
end Computability
end OAI
