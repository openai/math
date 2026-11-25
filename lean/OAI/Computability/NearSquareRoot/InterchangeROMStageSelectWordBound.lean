import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectWord
import OAI.Computability.NearSquareRoot.InterchangeROMAddressWordBound

/-! # Computed local costs of selected native movement words -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom
  InterchangeROMStage InterchangeAddress GeneratorSyntax

/-- Geometry-independent factor of the supplied literal chart operation. -/
def moveWeight (M C K e : ℕ) (x : Data) (μ : Frame.Move) : ℕ :=
  OpcodeProgram.wordWeight M C K e x.b (x.a+x.m+x.a) (lookup x.chart μ)

theorem computable_moveWeight {X : Type} [Primcodable X] (M C K e : ℕ) {d : X → Data}
    {μ : X → Frame.Move} (hd : Computable d) (ho : Computable μ) :
    Computable fun z => moveWeight M C K e (d z) (μ z) := by
  have len : Primrec (fun x : Data => x.a+x.m+x.a) := Primrec.nat_add.comp
    (Primrec.nat_add.comp (primrec_header 3) (primrec_header 2)) (primrec_header 3)
  exact OpcodeProgram.computable_wordWeight (Computable.const _) (Computable.const _)
    (Computable.const _) (Computable.const _) ((primrec_header 1).to_comp.comp hd) (len.to_comp.comp hd)
    (primrec_lookup.to_comp.comp (primrec_chart.to_comp.comp hd) ho)

/-- Positive uniform bound on every operand, including reverse chart words
and the default empty word. -/
def moveWeightMax (M C K e : ℕ) (x : Data) : ℕ :=
  let cost := OpcodeProgram.wordWeight M C K e x.b (x.a+x.m+x.a)
  (1 + cost []) + x.chart.foldr (fun w n => cost w + cost (w.reverse.map rewindOp) + n) 0

private theorem chart_sum_le {A : Type} (f : A → ℕ) {l : List A} {a : A} (h : a ∈ l) :
    f a ≤ l.foldr (fun w n => f w+n) 0 := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl|h
    · exact Nat.le_add_right _ _
    · exact (ih h).trans (Nat.le_add_left _ _)

theorem moveWeight_le (M C K e : ℕ) (x : Data) (μ : Frame.Move) :
    moveWeight M C K e x μ ≤ moveWeightMax M C K e x := by
  let cost := OpcodeProgram.wordWeight M C K e x.b (x.a+x.m+x.a)
  let sum := x.chart.foldr (fun w n => cost w + cost (w.reverse.map rewindOp) + n) 0
  change cost (lookup x.chart μ) ≤ 1 + cost [] + sum
  rcases μ with _ | ⟨b,i⟩
  · change cost [] ≤ _
    omega
  · by_cases hi : i < x.chart.length
    · let w := x.chart[i]
      have hw : w ∈ x.chart := List.getElem_mem hi
      have hs : cost w + cost (w.reverse.map rewindOp) ≤ sum :=
        chart_sum_le (fun w => cost w+cost (w.reverse.map rewindOp)) hw
      have he : FlatAtlas.chart x.chart i = w := List.getD_eq_getElem _ _ hi
      cases b <;> simp only [lookup,he,Bool.false_eq_true,ite_false,ite_true] <;> omega
    · have he : FlatAtlas.chart x.chart i = [] := by simp [FlatAtlas.chart,List.getD,hi]
      cases b <;> simp only [lookup,he,Bool.false_eq_true,ite_false,ite_true,List.reverse_nil,List.map_nil] <;> omega

theorem computable_moveWeightMax (M C K e : ℕ) : Computable (moveWeightMax M C K e) := by
  let cost (x : Data) := OpcodeProgram.wordWeight M C K e x.b (x.a+x.m+x.a)
  have len : Primrec (fun x : Data => x.a+x.m+x.a) := Primrec.nat_add.comp
    (Primrec.nat_add.comp (primrec_header 3) (primrec_header 2)) (primrec_header 3)
  have hc : Computable₂ cost := (OpcodeProgram.computable_wordWeight (Computable.const _) (Computable.const _)
    (Computable.const _) (Computable.const _) ((primrec_header 1).to_comp.comp Computable.fst)
    (len.to_comp.comp Computable.fst) Computable.snd).to₂
  let rev (w : Opcode.Word) := w.reverse.map rewindOp
  have hr : Primrec rev := Primrec.list_map Primrec.list_reverse (primrec_rewindOp.comp Primrec.snd).to₂
  let combine (x : Data) (v : Opcode.Word × ℕ) := cost x v.1 + cost x (rev v.1) + v.2
  have hs : Computable₂ combine := (Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp (hc.comp Computable.fst (Computable.fst.comp Computable.snd))
      (hc.comp Computable.fst (hr.to_comp.comp (Computable.fst.comp Computable.snd))))
    (Computable.snd.comp Computable.snd)).to₂
  exact Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp (Computable.const 1)
    (hc.comp Computable.id (Computable.const []))) (computable_foldr primrec_chart.to_comp (Computable.const 0) hs)

/-- All selected words use one common absolute tuple of compiler constants.
Their actual child sums and peaks remain available in `Step`. -/
theorem selected_word_run_scaled : ∃ M C K e : ℕ, 1 ≤ e ∧ ∀ {j threshold f l : ℕ}
    {x : Data} [NeZero x.b] (h : Valid j threshold x) (μ : (roleRealization h).NativeMove)
    (P G S : Tape) (_ : solid P) (_ : solid G) (_ : solid S)
    (v : x.Address P G S f → Tree) (good : Tree → Prop) (_ : ∀ a, good (v a)),
    let hdr := InterchangeROMAddress.header f P G S
    let rows := x.stageRows P G S f
    let operand := (roleRealization h).operand μ
    let src := stripe rows v
    let dst := stripe rows (v ∘ ((nativeLayout h P G S f).perm μ).symm)
    let F := moveWeight M C K e x operand * OpcodeProgram.geometry e hdr rows.count src src
    ∃ qs, qs.length = wordPrice h μ ∧
      (∀ q∈qs, OpcodeProgram.Valid (b:=x.b) f rows.count l P G S good q) ∧
      InterchangeROMSequence.Step (Request.job x.b) (x.moveCmd operand) (send hdr) src dst qs F F F := by
  obtain ⟨M,C,K,e,he,run⟩ := OpcodeProgram.run_raw_scaled
  refine ⟨M,C,K,e,he,?_⟩
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
