import OAI.Computability.BorderVNP.CubeRouteProfileDataFrame
import OAI.Computability.BorderVNP.CubeRouteProfileControls

/-! # One extended literal for signed geometry, routing, cube and tally

The chosen reader supplies one 81-word reference-packet extension. Its geometry
words and demand-directory pointers occupy positions disjoint from the cube,
lookup and tally operands. The two representations below give the same packet
word for word, so both native startup proofs apply to one physical execution.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA CubeHeaderInstall Packing RoutingOutputs GeometryAdvice

variable {w : ℕ}

/-- The nine words that belong to routing geometry and the positive-width delivery
directory within the complete reference extension. -/
private def routingFields : List ℕ := [64,65,66,67,68,69,70,87,92]

/-- The complete placement and demand operands on an otherwise supplied reference. -/
def routingExtension (old : Fin 81 → Word w) (D : Directory.Layout) (origin edges cells : ℕ) : Fin 81 → Word w :=
  controlsExtension (directoryFields old D) origin edges cells D.entries (D.teams*D.sites)

private theorem routingExtension_other (old : Fin 81 → Word w) (D : Directory.Layout)
    (origin edges cells : ℕ) (i : Fin 81) (h : i.val+31 ∉ routingFields) :
    routingExtension old D origin edges cells i = old i := by
  simp only [routingFields,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  rw [routingExtension,controlsExtension_other _ _ _ _ _ _ _ (by tauto),
    extension_other _ _ _ _ _ _ (by simp only [List.mem_cons,List.not_mem_nil,or_false]; tauto)]
  unfold directoryFields
  split <;> simp_all

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1500000 in
/-- The natural-valued tally frame already contains each original cube operand.
A second cube overlay recovers the same stored machine word, including its residue. -/
theorem cube_over_signed (task : SignedTaskArena.Layout) (raw team subtotalWidth : ℕ) (old : Fin 81 → Word w) :
    task.cube.extension (task.extension raw team subtotalWidth old) = task.extension raw team subtotalWidth old := by
  have repack (x : Word w) : TeamTapeInputEmit.word w x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  funext i
  fin_cases i <;> first | rfl | exact (repack (TeamTapeInputEmit.word w _)).symm

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1500000 in
/-- Geometry/placement and static cube/header overlays commute on every one of
the 81 positions. This calculation depends only on the published address layout. -/
private theorem commute (ar : CubeArena.Layout) (old : Fin 81 → Word w) (D : Directory.Layout)
    (origin edges cells header d a bc blocks profile cap : ℕ) :
    pinFields (ar.extension (routingExtension old D origin edges cells)) header d a bc blocks profile cap =
      routingExtension (pinFields (ar.extension old) header d a bc blocks profile cap) D origin edges cells := by
  funext i
  fin_cases i <;> rfl

/-- The one literal vector used by the chosen reader in the signed profile, cube
and sparse report. The initial length-dependent values include the task windows,
report arena, host and pair directories, and the originally supplied fields. -/
noncomputable def signedProfileExtension (task : SignedTaskArena.Layout) (old : Fin 81 → Word w)
    (D : Directory.Layout) (origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell : ℕ) :
    Fin 81 → Word w :=
  jointFields (task.cube.extension (routingExtension (task.extension raw team subtotalWidth old) D origin edges cells))
    fresh profile gates outputs width off ell task.cube.header.d task.cube.n task.cube.header.blocks
    task.cube.b task.cube.h task.cube.s

/-- The chosen packet is exactly the extension required by the profile's geometry,
private placement, and populated directory. Its remaining words are the same
tally/cube packet with the secondary cube bootstrap operands installed. -/
theorem signedProfileExtension_geometry (task : SignedTaskArena.Layout) (old : Fin 81 → Word w)
    (D : Directory.Layout) (origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell : ℕ) :
    signedProfileExtension task old D origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell =
      Allocation.fields (controlsExtension (directoryFields
        (pinFields (task.extension raw team subtotalWidth old) (Allocation.stop fresh profile gates outputs width w)
          task.cube.header.d (task.cube.n+1) (task.cube.h*task.cube.b) task.cube.header.blocks profile
          (Cube.Physical.declarationCap task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.s)) D)
        origin edges cells D.entries (D.teams*D.sites)) fresh profile gates outputs width off ell := by
  unfold signedProfileExtension jointFields
  rw [commute,cube_over_signed]
  rfl

/-- Every lookup, fixed task and tally word outside the geometry, directory and
secondary-header writes has exactly the stored signed-task value in the same vector. -/
theorem signedProfileExtension_taskWord (task : SignedTaskArena.Layout) (old : Fin 81 → Word w)
    (D : Directory.Layout) (origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell : ℕ)
    (i : Fin 81) (unused : i.val+31 ∉ [59,60,61,63,64,65,66,67,68,69,70,87,92,96,97,98,99,100,101,104,105,106,107,108,109,110,111]) :
    signedProfileExtension task old D origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell i =
      task.extension raw team subtotalWidth old i := by
  rw [signedProfileExtension_geometry,Allocation.fields_other _ _ _ _ _ _ _ _ i (by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at unused ⊢; tauto)]
  change routingExtension _ D origin edges cells i = _
  rw [routingExtension_other _ _ _ _ _ _ (by
    simp only [routingFields,List.mem_cons,List.not_mem_nil,or_false,not_or] at unused ⊢; tauto)]
  exact pinFields_other _ _ _ _ _ _ _ _ i (by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at unused ⊢; tauto)

/-- The physical group budget (frame 31) stays in the caller's first
reference-extension word, including in the baseline passed to the native
cube scheduler. -/
theorem routingExtension_budgetWord (task : SignedTaskArena.Layout) (old : Fin 81 → Word w)
    (D : Directory.Layout) (origin edges cells raw team subtotalWidth : ℕ) :
    routingExtension (task.extension raw team subtotalWidth old) D origin edges cells 0 = old 0 := by
  rw [routingExtension_other _ _ _ _ _ _ (by decide)]
  apply Fin.ext
  exact Nat.mod_eq_of_lt (old 0).isLt

/-- The selected routing extension sets the indirect control pointer used by the
cell writer; the geometry overlay does not replace this routing slot. -/
theorem signedProfileExtension_controlPointer (task : SignedTaskArena.Layout) (old : Fin 81 → Word w)
    (D : Directory.Layout) (origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell : ℕ)
    (fit : controlsBase origin edges cells D.entries (D.teams*D.sites) < 2^w) :
    (signedProfileExtension task old D origin edges cells raw team subtotalWidth fresh profile gates outputs
      width off ell (61 : Fin 81)).val = controlsBase origin edges cells D.entries (D.teams*D.sites) := by
  rw [signedProfileExtension_geometry,Allocation.fields_other _ _ _ _ _ _ _ _ 61 (by decide)]
  exact Nat.mod_eq_of_lt fit

/-- The five lookup operands and the four native deck operands all survive as the
same signed-task words in the selected reference packet. Indices count from zero
inside the 81-word literal, whose first word goes to frame position 31. -/
theorem signedProfileExtension_lookupWord (task : SignedTaskArena.Layout) (old : Fin 81 → Word w)
    (D : Directory.Layout) (origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell : ℕ)
    (i : Fin 81) (field : i.val ∈ [14,40,49,52,53,16,48,50,51]) :
    signedProfileExtension task old D origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell i =
      task.extension raw team subtotalWidth old i := by
  apply signedProfileExtension_taskWord
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at field ⊢
  omega

/-- Each signed report operand at its specified position is the allocator's
actual unsigned value when it fits in the selected reader word. -/
theorem signedProfileExtension_report (task : SignedTaskArena.Layout) (old : Fin 81 → Word w)
    (D : Directory.Layout) (origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell : ℕ)
    (i : Fin 81) (report : i.val+31 ∈ [33,34,35,36,38,39,40,44,45,46,71,80,89,90,95]) :
    let previous := fun k => (task.cube.extension old ⟨min (k-31) 80,by omega⟩).val
    let value := task.reportFields raw team subtotalWidth previous (31+i.val)
    value < 2^w → (signedProfileExtension task old D origin edges cells raw team subtotalWidth fresh profile
      gates outputs width off ell i).val = value := by
  intro previous value fit
  rw [signedProfileExtension_taskWord]
  · exact Nat.mod_eq_of_lt fit
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at report ⊢
    omega

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
