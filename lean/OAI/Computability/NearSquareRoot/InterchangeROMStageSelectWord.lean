import OAI.Computability.NearSquareRoot.InterchangeROMAddressWordRaw
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyCost
import OAI.Computability.NearSquareRoot.InterchangeROMStageQuote

/-! # Executing the exact address word selected by a stage operand

The same raw chart lookup supplies both the emitted code and its recursive
price. The interpretation theorem uses the catalog verified by the selected
template. Its exact word ledger is valid for every address and every
choice of payload predicate.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Port
  IntegerMultiplication.Loom IntegerMultiplication.Adic IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims InterchangeROMStage InterchangeAddress
  InterchangeROMRepair.Physical GeneratorSyntax InterchangeSpace

noncomputable def wordCmd (x : Data) : Opcode.Word → Cmd := OpcodeProgram.word x.b (x.a+x.m+x.a)

noncomputable def moveCmd (x : Data) (μ : Frame.Move) : Cmd := x.wordCmd (lookup x.chart μ)

theorem wordCmd_effective {X : Type} [Primcodable X] {d : X → Data} {w : X → Opcode.Word}
    (hd : Computable d) (hw : Computable w) : Effective ltr fun x => (d x).wordCmd (w x) := by
  have num : Primrec (fun x : Data => x.a+x.m+x.a) := Primrec.nat_add.comp
    (Primrec.nat_add.comp (primrec_header 3) (primrec_header 2)) (primrec_header 3)
  exact OpcodeProgram.word_effective ((primrec_header 1).to_comp.comp hd) (num.to_comp.comp hd) hw

theorem moveCmd_effective {X : Type} [Primcodable X] {d : X → Data} {μ : X → Frame.Move}
    (hd : Computable d) (hμ : Computable μ) : Effective ltr fun x => (d x).moveCmd (μ x) :=
  wordCmd_effective hd (primrec_lookup.to_comp.comp (primrec_chart.to_comp.comp hd) hμ)

theorem moveCmd_within : ∃ R, ∀ (x : Data) (μ : Frame.Move), CommonRegisters.Within R (x.moveCmd μ) := by
  obtain ⟨R,hR⟩ := OpcodeProgram.word_within
  exact ⟨R,fun x μ => hR _ _ _⟩

/-- Charge of the concrete spelling selected by the oriented chart lookup. -/
def wordAllowance (c : OpcodeProgram.Clocks) (x : Data) (μ : Frame.Move)
    (h : InterchangeROMAddress.Header) (N : ℕ) (row : Tree) : Allowance :=
  let ops := lookup x.chart μ
  let tick := fun o => OpcodeProgram.cost c x.b (x.a+x.m+x.a) o h N row row
  let peak := childPeak tick ops
  ⟨(ops.map tick).sum+(ops.length+1)*(110*((send h).count+1)),
    InterchangeBatch.dataSpace row.count (send h).count peak,
    InterchangeBatch.returnSpace (send h).count peak⟩

abbrev stageRows (x : Data) (P G S : Tape) (f : ℕ) [NeZero x.b] :=
  arrays (Equiv.refl (Fin (x.a+x.m+x.a))) (line x.b f) P G S

theorem operand_admissible {j threshold : ℕ} {x : Data} (h : Valid j threshold x)
    (μ : (roleRealization h).NativeMove) :
    Opcode.admissible x.b (x.a+x.m+x.a) (lookup x.chart ((roleRealization h).operand μ)) = true := by
  rw [lookup_operand h μ,Opcode.admissible_encode_iff]
  exact AddressROM.instructions_legal (catalog h) (radix_gt_one h) (catalog_valid h) μ

theorem operand_decode {j threshold : ℕ} {x : Data} (h : Valid j threshold x)
    (μ : (roleRealization h).NativeMove) :
    Opcode.decodeWord (lookup x.chart ((roleRealization h).operand μ)) (operand_admissible h μ) =
      AddressROM.instructions (catalog h) μ := by
  apply List.map_injective_iff.mpr Opcode.encode_injective
  exact (Opcode.encode_decodeWord _ _).trans (lookup_operand h μ)

theorem operand_perm {j threshold f : ℕ} {x : Data} [NeZero x.b] (h : Valid j threshold x)
    (μ : (roleRealization h).NativeMove) (P G S : Tape) :
    let word := lookup x.chart ((roleRealization h).operand μ)
    let ops := Opcode.decodeWord word (operand_admissible h μ)
    recreation (Equiv.refl _) P G S f ops (Opcode.legal_decodeWord word (operand_admissible h μ)) =
      (nativeLayout h P G S f).perm μ := by
  dsimp only
  have replace (ops : List (Lag (Fin (x.a+x.m+x.a)) x.b))
      (legal : ∀ m ∈ ops, m.legal (ranking (Equiv.refl _)))
      (eqn : ops = AddressROM.instructions (catalog h) μ) :
      recreation (Equiv.refl _) P G S f ops legal = (nativeLayout h P G S f).perm μ := by
    subst ops
    exact AddressROM.native_move (catalog h) (radix_gt_one h) (catalog_valid h) μ P G S f
  exact replace _ _ (operand_decode h μ)

/-- One fixed choice of physical resource constants serves all selected
templates, all native moves, and all solid header shapes. -/
theorem selected_word_run : ∃ c : OpcodeProgram.Clocks, ∀ {j threshold f l : ℕ}
    {x : Data} [NeZero x.b] (h : Valid j threshold x) (μ : (roleRealization h).NativeMove)
    (P G S : Tape) (_ : solid P) (_ : solid G) (_ : solid S)
    (v : x.Address P G S f → Tree) (good : Tree → Prop) (_ : ∀ a, good (v a)),
    let hdr := InterchangeROMAddress.header f P G S
    let rows := x.stageRows P G S f
    let operand := (roleRealization h).operand μ
    let src := stripe rows v
    let dst := stripe rows (v ∘ ((nativeLayout h P G S f).perm μ).symm)
    let a := wordAllowance c x operand hdr rows.count src
    ∃ qs, qs.length = wordPrice h μ ∧
      (∀ q∈qs, OpcodeProgram.Valid (b:=x.b) f rows.count l P G S good q) ∧
      InterchangeROMSequence.Step (Request.job x.b) (x.moveCmd operand) (send hdr)
        src dst qs a.time a.cap a.depth := by
  obtain ⟨c,run⟩ := OpcodeProgram.run_raw
  refine ⟨c,?_⟩
  intro j threshold f l x nz h μ P G S p g s v good hv
  have res := run P G S p g s (radix_gt_one h) l
    (lookup x.chart ((roleRealization h).operand μ)) (operand_admissible h μ) v good hv
  dsimp only at res
  rw [operand_perm h μ P G S] at res
  exact res

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
