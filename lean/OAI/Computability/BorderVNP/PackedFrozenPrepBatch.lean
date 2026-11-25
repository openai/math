import OAI.Computability.BorderVNP.PackedFrozenFormats
import OAI.Computability.BorderVNP.PackedInheritedWorkPrepFrame
import OAI.Computability.BorderVNP.PackedTerminalEndpointFields

/-! # One shared physical subdivision pass for an entire tuple of saved tapes

The batched width frame publishes the real new endpoint columns. Each
child reads its old widths and tape directly from its own source rectangle
and appends the records compiled from these returned hop fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.PrepBatch

open Crossing Shortening Shortening.PublicCapacity Shortening.PublicEndpoints
open PackedHistoryCircuit WorkWords Subdivision Diagonal.ExternalSew.FieldExport
open VPVNP.VerifierNetwork ParseBatchSort

variable {k w np extra : ℕ} {s : Shape} (T : Format)
    {Old A B : Type} [Fintype Old] [Fintype B]
local notation3 "newS" => (s.subdivide extra).sites
local notation3 "newE" => (s.subdivide extra).edges
local notation3 "X" => Fin k × T.Output Old s.sites w w
local notation3 "Y" => WithWidths (SavedPins B newS newE w) newS w
local notation3 "J" => (Fin k × T.Output Old s.sites w w) ⊕ (Fin k × WithWidths (SavedPins B newS newE w) newS w)
variable (prior : Inputs A s.sites s.edges w w → Old) (ports : WorkWords.Ports np) (fit : (s.subdivide extra).sites ≤ 2^w)

private def oldRead (i : Fin k) (a : Inputs A s.sites s.edges w w) : J := .inl (i,.inl (.inl (prior a)))
private def newRead (i : Fin k) (a : Inputs B newS newE w w) : J := .inr (i,.inl (.inr (.inr a)))

/-- Old site/cable endpoints in this child's own physical source. -/
def oldFields (i : Fin k) : CellAddressCircuit.Fields s.sites s.edges np 1 w 0 w (J ⊕ Bool) := TerminalCells.endpointFields ((Nat.le_add_right s.sites _).trans fit)
  (oldRead (extra := extra) (B := B) T prior i) ports.host ports.width

/-- The new hop and port directory read from this child's width-bearing geometry result. -/
def newFields (i : Fin k) : CellAddressCircuit.Fields newS newE np 1 w 0 w (J ⊕ Bool) := TerminalCells.endpointFields fit
  (newRead (B := B) (Old := Old) (s := s) (extra := extra) (w := w) T i) ports.host ports.width

/-- Both old per-site numerical fields, before updating the work and complete extent. -/
def siteWord (i : Fin k) (b : Bool) (r : Fin s.sites) (j : Fin w) : J ⊕ Bool :=
  .inl (.inl (i,.inl (.inr (r,b,j))))

/-- An actual successor hop's occupancy in the computed child directory. -/
def hopPresent (i : Fin k) (r : Fin newE) : J ⊕ Bool := .inl (.inr (i,.inl (.inl r)))

/-- The previous chronology at one physical child, forwarded directly from its source slots. -/
noncomputable def earlier (i : Fin k) : Frame (J ⊕ Bool) (Pins T.Rows T.Payload w) :=
  Frame.initial fun r => .inl (.inl (i,.inr r))

local notation3 "F0" => oldFields (B := B) T prior ports fit
local notation3 "F1" => newFields (B := B) (Old := Old) T ports fit
local notation3 "words" => siteWord (B := B) (Old := Old) (extra := extra) T
local notation3 "present" => hopPresent (B := B) (Old := Old) (s := s) (extra := extra) (w := w) T
local notation3 "initial" => earlier (B := B) (Old := Old) (s := s) (extra := extra) (w := w) T
local notation3 "Out" => T.append (Format.subdivision s.edges np extra w)

/-- All frozen records at one child in their actual chronological order. -/
noncomputable def leaf (i : Fin k) : Frame (J ⊕ Bool) (Pins (Out).Rows (Out).Payload w) :=
  Gates.completeTape (F0 i) (F1 i) (words i false) (words i true) (present i) (initial i)

/-- Raw budget of this genuine copy's whole record tape, including all earlier owner queries. -/
noncomputable def leafCharge (i : Fin k) : ℕ :=
  lookupCost s.sites (Fintype.card T.Rows) w w +
    ((Gates.inputs (F0 i) (F1 i) (words i false) (words i true) (present i)).size+1+
      Fintype.card (Gates.Row s.edges np extra)*(4500*(w+1)^2))

theorem leaf_size (i : Fin k) : (leaf (B := B) T prior ports fit i).size ≤ leafCharge (B := B) T prior ports fit i := by
  have h := Gates.completeTape_size (s := s) (extra := extra) (F0 i) (F1 i)
    (words i false) (words i true) (present i) (initial i)
  simp only [earlier,Frame.initial_size,Nat.zero_add] at h
  exact h.trans_le (Nat.add_le_add (rekey_size ..) (Gates.frozen_size ..))

variable (pre : Frame (Fin k × WithWidths Old s.sites w) (Fin k × WithWidths (SavedPins B (s.subdivide extra).sites (s.subdivide extra).edges w) (s.subdivide extra).sites w))

/-- Shared raw pins and computed endpoint fields, with one pair of constants for all children. -/
noncomputable def joint : Frame X (J ⊕ Bool) :=
  (constants J).subst ((pre.subst (Frame.initial fun z : Fin k × WithWidths Old s.sites w => ((z.1,Sum.inl z.2) : X))).withInput)

private noncomputable def copies := (exists_parallelFrames (leaf (k := k) (B := B) T prior ports fit)).choose

/-- One width-bearing geometry pass followed by all real children, with the calculated new
geometry and complete tape joined by output wiring. -/
noncomputable def batch : Frame X (Fin k × (Y ⊕ Pins (Out).Rows (Out).Payload w)) :=
  let f := copies (k := k) (B := B) T prior ports fit
  (f.withInput.select (fun z => match z.2 with
    | .inl g => .inl (.inl (.inr (z.1,g)))
    | .inr r => .inr ⟨z.1,r⟩)).subst (joint T pre)

/-- The gate list charges the shared width-bearing pass once, and each original child once. -/
theorem batch_size : (batch T prior ports fit pre).size ≤ pre.size + 3 +
    ∑ i : Fin k, leafCharge (B := B) T prior ports fit i := by
  have hj : (joint T pre).size ≤ pre.size + 2 := by
    simp only [joint,Frame.subst_size,Frame.withInput_size,Frame.initial_size,Nat.zero_add]
    exact Nat.add_le_add_left (constants_size _) _
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin k) _ => leaf_size (B := B) T prior ports fit i)
  have hf := (exists_parallelFrames (leaf (k := k) (B := B) T prior ports fit)).choose_spec.1
  simp only [batch,Frame.subst_size,Frame.select_size,Frame.withInput_size,copies]
  omega

variable (x : Fin k × T.Output Old s.sites w w → Bool)

/-- The shared prepared geometry and widths are exactly those computed by the original pre-frame. -/
theorem batch_geo (i : Fin k) (j : Y) :
    (batch T prior ports fit pre).eval x (i,.inl j) = pre.eval (fun z => x (z.1,.inl z.2)) (i,j) := by
  have sel : (Frame.initial (fun z : Fin k × WithWidths Old s.sites w => (z.1,Sum.inl z.2))).eval x =
      fun z => x (z.1,.inl z.2) := funext (Frame.initial_eval _ _)
  simp only [batch,Frame.subst_eval,Frame.select_eval,Frame.withInput_eval_inl,joint,constants_eval,Sum.elim_inl,
    Frame.withInput_eval_inr,sel]

/-- Each frozen record bit is read from this very child's previous tape and new endpoint computation. -/
theorem batch_tape (i : Fin k) (j : Pins (Out).Rows (Out).Payload w) :
    (batch T prior ports fit pre).eval x (i,.inr j) =
      (leaf (B := B) T prior ports fit i).eval ((joint T pre).eval x) j := by
  simp only [batch,Frame.subst_eval,Frame.select_eval,Frame.withInput_eval_inr,copies]
  exact (exists_parallelFrames (leaf (k := k) (B := B) T prior ports fit)).choose_spec.2 _ i j

end Packing.Inherited.FrozenTape.PrepBatch

end BorderVNP
end Computability
end OAI
