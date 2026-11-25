import OAI.Computability.NearSquareRoot.InterchangeROMFamilyGeometry
import OAI.Computability.NearSquareRoot.InterchangeROMOuterCompile
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelected

/-! # Binding the three physical center operations to the selected template -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFamily

open IntegerMultiplication IntegerMultiplication.Code CommonRegisters GeneratorSyntax
  NearSquareRoot.Interchange NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request
  NearSquareRoot.InterchangeROMOuter NearSquareRoot.InterchangeROMRepair
  NearSquareRoot.InterchangeROMRepair.Physical

/-- Generated center script, including both row-layout conversions and every
full-width reserve interchange. -/
noncomputable def center (enter leave : Template.Data → Cmd) (x : Template.Data) :=
  stage x.b x.a x.m (enter x) (Selected.program x) (leave x)

theorem effective_center {enter leave : Template.Data → Cmd}
    (he : Effective ltr enter) (hl : Effective ltr leave) : Effective ltr (center enter leave) :=
  effective_stage (Template.Data.primrec_header 1).to_comp (Template.Data.primrec_header 3).to_comp
    (Template.Data.primrec_header 2).to_comp he Selected.effective_program hl

theorem centered_registers {enter leave : Template.Data → Cmd} {E L : ℕ}
    (he : ∀ x, Within E (enter x)) (hl : ∀ x, Within L (leave x)) :
    ∃ R : ℕ, ∀ x, Within R (center enter leave x) := by
  obtain ⟨M,hm⟩ := Selected.program_within
  obtain ⟨S,hs⟩ := InterchangeROMStars.registers
  let R := max (max E L) (max (max 3 M) S)
  refine ⟨R,fun x => within_stage (by dsimp [R]; omega) ?_ ?_ ?_ ?_⟩
  · exact RegisterSelect.within_mono (by dsimp [R]; omega) _ (he x)
  · exact RegisterSelect.within_mono (by dsimp [R]; omega) _ (hm x)
  · exact RegisterSelect.within_mono (by dsimp [R]; omega) _ (hl x)
  · exact RegisterSelect.within_mono (by dsimp [R]; omega) _ (hs x.b x.a x.m)

/-- The three actual operations at the boundary between their individual
machine proofs and the selected recursive family. The main command is the
canonical emitted Hermite program. -/
def ComponentRuns (F : InterchangeROMFront.Core) (enter leave : Template.Data → Cmd)
    (kb kc ku : ℕ) : Prop :=
  ∀ (j t : ℕ) (x : Template.Data) (h : Template.Data.Valid j t x), ∃ B C U : ℕ,
    let parent := InterchangeROMFrame.node F.cmd (center enter leave x) x.b (positions x.a x.m)
    ∀ (q : Request x.b) (ok : Packed (@value (x.modulusIndex+1)) q)
      (hw : positions x.a x.m < q.width),
      Components (p:=x.modulusIndex) (a:=x.a) (m:=x.m) (l:=x.labels) (n:=Raw.rowCount x.m)
        q h.1.2.2.1.two_le (by have := h.1.2.2.2.2.2.1; omega)
        hw ok parent (enter x) (Selected.program x) (leave x) x.calls B C U kb kc ku

theorem NativeFamily.ofComponents (F : InterchangeROMFront.Core) (enter leave : Template.Data → Cmd)
    (he : Effective ltr enter) (hl : Effective ltr leave)
    (E L : ℕ) (er : ∀ x, Within E (enter x)) (lr : ∀ x, Within L (leave x))
    (kb kc ku : ℕ) (c : ComponentRuns F enter leave kb kc ku) : Nonempty NativeFamily := by
  obtain ⟨k,exec⟩ := compile_native F
  obtain ⟨R,hr⟩ := centered_registers er lr
  refine ⟨NativeFamily.fromCenter F (center enter leave) R (max (F.degree+1) (stageDegree kb kc ku k))
    (effective_center he hl) hr (fun j t x legal => ?_)⟩
  obtain ⟨B,C,U,hn⟩ := c j t x legal
  have size := legal_width legal
  have guard := Template.Data.valid_contraction legal
  rw [← bank_width x] at guard
  have result := exec (p:=x.modulusIndex) (a:=x.a) (m:=x.m) (l:=x.labels) (n:=Raw.rowCount x.m)
    legal.1.2.2.1.two_le legal.1.2.2.2.2.2.1 size.1 size.2
    (Generator.targetExponent j) (by unfold Generator.targetExponent; positivity)
    x.calls B C U kb kc ku guard (enter x) (Selected.program x) (leave x) hn
  let degree := max (F.degree+1) (stageDegree kb kc ku k)
  let statement (p : ℕ) := InterchangeROMRecursion.Certified
    (InterchangeROMFrame.controller F.cmd (center enter leave x) x.b (positions x.a x.m))
    (fun i : ThickRequest (Packed (b:=x.b) (@value p)) degree =>
      ⌈(i.val.recordVolume : ℝ)*(i.val.width : ℝ)^Generator.targetExponent j⌉₊)
    (fun i => i.val.recordVolume) (fun i => (job x.b).issue i.val) (fun i => (job x.b).reply i.val)
  exact (congrArg statement (modulus legal)).mp result

end InterchangeROMFamily

end NearSquareRoot
end Computability
end OAI
