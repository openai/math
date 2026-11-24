import OAI.Computability.VPVNP.EvaluatorCallbackSafety
import OAI.Computability.VPVNP.EvaluatorWeightedSafety

/-! # Mounting the streamed readers in the digit scheduler

Each scalar read operates on the unary label and the weighted payload. The
digit table, exponent counters and repeat stack retain their contents during
that read. Their lengths enter only the space bound for the enclosing machine.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.MatrixCallbacks

open RAMTape SliceArithmetic EvaluatorRoutineSafety EvaluatorChronologicalLoop
open EvaluatorDigitFetch (bank)
open EvaluatorMonomialSchedule

variable {P : Type} [DecidableEq P] {p e w v : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K] {c : Vector p e}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (dim : BurstRAM.Word v) (extra : Stacks P)

local notation "payloadBank" => (fun i next q a ↦ WeightedStep.bank φ w dim i next q a extra)
local notation "work" => (EvaluatorDigitFetch.Port.work (P := WeightedStep.Port P))

private theorem fixedFrame_bounded (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (read : FiniteRoutine (ReadPort P)) (label time peak cap : ℕ) (hpeak : peak ≤ cap)
    (matrix : Matrix (Fin dim.val) (Fin dim.val) K)
    (hr : ReadsEntryWithin φ dim extra read w label time peak matrix)
    (frame : Stacks (WeightedStep.Port P) → Stacks (Host P))
    (hwork : ∀ s k, frame s (.work k) = s k)
    (hlabel : ∀ s, frame s (.addr .labelIndex) = List.replicate label true)
    (hrest : ∀ x y k, (∀ j, work j ≠ k) → frame x k = frame y k)
    (hroom : ∀ (i : Fin dim.val) (next q : List Bool), next.length ≤ v → q.length ≤ e*w →
      ∀ (a : K) k, (frame (payloadBank i next q a) k).length + WeightedStep.localTicks v e w ≤ cap) :
    Bounded (machine read).body (stackFits cap) (frame ∘ payload φ dim extra w)
      (frame ∘ payload φ dim extra w) (WeightedStep.ticks v e w time) := by
  let ambient := frame (fun _ ↦ [])
  have hwp : Function.Injective work := fun _ _ h ↦ EvaluatorDigitFetch.Port.work.inj h
  have hi (s) : installStacks work ambient s = frame s :=
    installStacks_frame hwp (hwork s) (hrest s _)
  have h := WeightedStep.callback_bounded φ work hwp ambient extra dim he hw (read.onPorts mount)
    matrix cap time (by simpa only [hi] using hroom) (by
      intro s j
      let word := BurstRAM.wordBits (Fin.castLE dim.isLt.le j : BurstRAM.Word v)
      let pre := payloadBank s.1 word [] s.2
      let post := payloadBank s.1 word (WeightedStep.bits φ w (matrix s.1 j)) s.2
      have hm : Function.Injective (mount (P := P)) := by
        intro a b hh; rcases a with (⟨⟩ | a) <;> rcases b with (⟨⟩ | b) <;> cases hh <;> rfl
      have get (b : Stacks (WeightedStep.Port P)) (k : ReadPort P) :
          frame b (mount k) = queryBank (List.replicate label true) b k := by
        cases k with
        | inl => exact hlabel b
        | inr k => exact hwork b k
      obtain ⟨d, hd, run⟩ := hr s j
      have mounted := FiniteRoutine.BoundedRun.onPorts (a := read) hm (frame pre) (run.mono_cap hpeak) (fun k _ ↦
        (Nat.le_add_right _ _).trans (hroom s.1 word [] (by simp [word]) (by simp) s.2 k))
      have first := installStacks_frame hm (get pre) (base := frame pre) (fun _ _ ↦ rfl)
      have last := installStacks_frame hm (get post) (base := frame pre) (fun k hk ↦
        hrest post pre k (fun j ↦ hk (.inr j)))
      rw [first, last] at mounted
      exact ⟨d, hd, by simpa only [hi] using mounted⟩)
  simpa only [hi, Function.comp_def, payload, machine] using h

variable {t Z : ℕ} (es : Fin t → BurstRAM.Word Z) (d : List Bool)
    (extraSpace : ℕ) (hextra : ∀ k, (extra k).length ≤ extraSpace)

local notation "footprint" => WeightedStep.bankSpace v e w extraSpace
local notation "reserve" => WeightedStep.localTicks v e w
local notation "tableBits" => EvaluatorRadixRows.packedTable d.length (TapeWord.value d) (List.ofFn es)
local notation "pay" => payload φ dim extra w

/-- Callback capacity available on all digit columns. -/
def workspace (v e w extraSpace peak : ℕ) :=
  WeightedStep.bankSpace v e w extraSpace + WeightedStep.localTicks v e w + peak

include hextra in
omit [DecidableEq P] in
theorem payload_length (peak : ℕ) (s : Fin dim.val × K) :
    stackFits (workspace v e w extraSpace peak) (pay s) := by
  intro k
  exact (WeightedStep.bank_length φ extra dim extraSpace hextra s.1 [] [] (by simp) (by simp) s.2 k).trans
    (by unfold workspace; omega)

include hextra in
omit [DecidableEq P] in
private theorem frame_room (i j labels cols : ℕ) (hi : i+labels ≤ t) (hj : j+cols ≤ Z) (peak : ℕ)
    (idx : Fin dim.val) (next q : List Bool) (hn : next.length ≤ v) (hq : q.length ≤ e*w) (a : K)
    (k : Host P) :
    (bank tableBits t Z d.length i j labels cols (payloadBank idx next q a) k).length + reserve ≤
      schedulerSpace (tableBits).length t Z d.length (workspace v e w extraSpace peak) := by
  have hb := WeightedStep.bank_length φ extra dim extraSpace hextra idx next q hn hq a
  have hs := bank_length tableBits t Z d.length footprint (fun _ : Unit ↦ payloadBank idx next q a)
    (fun _ ↦ hb) hi hj () k
  unfold schedulerSpace bankSpace workspace
  unfold bankSpace at hs
  dsimp only at hs ⊢
  omega

include hextra in
/-- All paths of a Frobenius callback at a reachable column. -/
theorem frobenius_bounded (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (read : FiniteRoutine (ReadPort P)) (time peak : ℕ)
    (matrix : Matrix (Fin dim.val) (Fin dim.val) K)
    (hr : ReadsEntryWithin φ dim extra read w 0 time peak matrix)
    (j : Fin Z) (cols : ℕ) (hj : j.val+cols < Z) :
    Bounded (machine read).body
      (stackFits (schedulerSpace (tableBits).length t Z d.length (workspace v e w extraSpace peak)))
      (fun x ↦ bank tableBits t Z d.length 0 j 0 cols (pay x))
      (fun x ↦ bank tableBits t Z d.length 0 j 0 cols (pay x)) (WeightedStep.ticks v e w time) := by
  apply fixedFrame_bounded φ dim extra he hw read 0 time peak _ _ matrix hr
    (bank tableBits t Z d.length 0 j 0 cols) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  · intro x y k hk; cases k <;> first | rfl | exact (hk _ rfl).elim
  · exact frame_room φ dim extra es d extraSpace hextra 0 j 0 cols (by omega) hj.le peak
  · unfold schedulerSpace bankSpace workspace; omega

include hextra in
/-- All paths of a multiplication callback, including early rejection by the
basis-index chooser. The temporary digit holds exactly one field-cardinality
word when the repeated callback is entered. -/
theorem label_bounded (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (read : FiniteRoutine (ReadPort P)) (time peak : ℕ)
    (matrix : Fin t → Matrix (Fin dim.val) (Fin dim.val) K)
    (hr : ∀ i, ReadsEntryWithin φ dim extra read w i.val time peak (matrix i))
    (i : Fin t) (j : Fin Z) (labels cols : ℕ) (hi : i.val+labels < t) (hj : j.val+cols < Z)
    (digit : List Bool) (hsize : digit.length = d.length) :
    let frame (s : Stacks (WeightedStep.Port P)) := EvaluatorDigitRepeat.frame
      EvaluatorDigitFetch.Port.digit EvaluatorDigitFetch.Port.borrow
      (bank tableBits t Z d.length i j labels cols s) digit []
    Bounded (machine read).body
      (stackFits (schedulerSpace (tableBits).length t Z d.length (workspace v e w extraSpace peak)))
      (frame ∘ pay) (frame ∘ pay) (WeightedStep.ticks v e w time) := by
  intro frame
  apply fixedFrame_bounded φ dim extra he hw read i.val time peak _ _ (matrix i) (hr i) frame
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  · intro x y k hk; cases k <;> first | rfl | exact (hk _ rfl).elim
  · intro idx next q hn hq a k
    have hh := frame_room φ dim extra es d extraSpace hextra i j labels cols hi.le hj.le peak idx next q hn hq a k
    cases k with
    | digit | borrow => simp [frame, EvaluatorDigitRepeat.frame, hsize, schedulerSpace, bankSpace, workspace]; omega
    | _ => exact hh
  · unfold schedulerSpace bankSpace workspace; omega

end Evaluator.MatrixCallbacks

end VPVNP
end Computability
end OAI
