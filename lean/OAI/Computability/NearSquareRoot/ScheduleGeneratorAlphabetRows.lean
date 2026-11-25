import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhaseReady
import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhaseRead
import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhaseWork
import OAI.Computability.NearSquareRoot.ScheduleGeneratorNumberedTable

/-! # Compiling a varying finite source alphabet to one computable ROM family -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Phase
open CommonAlphabet IntegerMultiplication
variable {A Q : ℕ → Type} {I : Type}
variable (a : ∀ x, Numbering (A x)) (q : ∀ x, Numbering (Q x)) (i : Numbering I)
  (ha : Computable fun x => (a x).size) (hq : Computable fun x => (q x).size)
  (blank : ∀ x, A x) (hb : Computable fun x => ((a x).equiv (blank x)).val)
  (rows : ℕ → ℕ × ℕ → Option (ℕ × ℕ)) (hrws : Computable₂ rows)

private def scan (w b : ℕ) (r : List ℕ) :
    (ℕ × List (List ℕ) × ℕ) ⊕ (ℕ × List ℕ × ℕ) → Option (State × Actions) :=
  Sum.elim (fun v => some (execRead w b r v)) (fun v => some (execRewind w r v))

private def active (w ni b : ℕ) (r : List ℕ) :
    (ℕ × Actions × ℕ × ℕ) ⊕ (ℕ × List (List ℕ) × ℕ) ⊕ (ℕ × List ℕ × ℕ) → Option (State × Actions) :=
  Sum.elim (fun v => some (execWork w ni b r v)) (scan w b r)

def next (x : ℕ) (r : List ℕ) : State → Option (State × Actions) :=
  Sum.elim (execReady a i ha rows x r) (active (a x).size i.size ((a x).equiv (blank x)).val r)

variable {X : Type} [Primcodable X]

private theorem computable_scan {w b : X → ℕ} {r : X → List ℕ}
    {v : X → (ℕ × List (List ℕ) × ℕ) ⊕ (ℕ × List ℕ × ℕ)}
    (hw : Computable w) (hb : Computable b) (hr : Computable r) (hv : Computable v) :
    Computable fun x => scan (w x) (b x) (r x) (v x) :=
  Computable.sumCasesOn hv
    (Computable.option_some.comp (computable_execRead (hw.comp Computable.fst)
      (hb.comp Computable.fst) (hr.comp Computable.fst) Computable.snd)).to₂
    (Computable.option_some.comp (computable_execRewind (hw.comp Computable.fst)
      (hr.comp Computable.fst) Computable.snd)).to₂

private theorem computable_active {w b : X → ℕ} {r : X → List ℕ} (ni : ℕ)
    {v : X → (ℕ × Actions × ℕ × ℕ) ⊕ (ℕ × List (List ℕ) × ℕ) ⊕ (ℕ × List ℕ × ℕ)}
    (hw : Computable w) (hb : Computable b) (hr : Computable r) (hv : Computable v) :
    Computable fun x => active (w x) ni (b x) (r x) (v x) :=
  Computable.sumCasesOn hv
    (Computable.option_some.comp (computable_execWork (hw.comp Computable.fst)
      (Computable.const ni) (hb.comp Computable.fst) (hr.comp Computable.fst) Computable.snd)).to₂
    (computable_scan (hw.comp Computable.fst) (hb.comp Computable.fst)
      (hr.comp Computable.fst) Computable.snd).to₂

include hb hrws in
theorem computable_next {x : X → ℕ} {r : X → List ℕ} {v : X → State}
    (hx : Computable x) (hr : Computable r) (hv : Computable v) :
    Computable fun k => next a i ha blank rows (x k) (r k) (v k) :=
  Computable.sumCasesOn hv
    (computable_execReady a i ha rows hrws (hx.comp Computable.fst)
      (hr.comp Computable.fst) Computable.snd).to₂
    (computable_active i.size ((ha.comp hx).comp Computable.fst) ((hb.comp hx).comp Computable.fst)
      (hr.comp Computable.fst) Computable.snd).to₂

set_option quotPrecheck false
local notation "p" => states a q i (fun x => (a x).size) (ha := ha) (hq := hq) (hw := ha)
local notation "dataReads" => cached (fun _ => Numbering.ternary) i (Computable.const 3)

/-- The numerical rule has precisely the interface used by ROM generation.
The state and read-tuple ordinals are those of the existing block controller. -/
def packed (x : ℕ) (s : ℕ × ℕ) : Option (ℕ × ℕ) :=
  (next a i ha blank rows x ((dataReads).decode x s.2) ((p).decode x s.1)).map fun z =>
    ((p).encode x z.1,(ternaryActions i).encode x z.2)

include hb hrws in
theorem computable_packed : Computable₂ (packed a q i ha hq blank rows) := by
  apply Computable.option_map (computable_next a i ha blank hb rows hrws Computable.fst
    ((dataReads).decode_eff.comp Computable.fst (Computable.snd.comp Computable.snd))
    ((p).decode_eff.comp Computable.fst (Computable.fst.comp Computable.snd)))
  exact (((p).encode_eff.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)).pair
    ((ternaryActions i).encode_eff.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.snd))).to₂

variable (machine : ∀ x, TM.Rule (A x) (Q x) I)
  (hcorrect : ∀ x z r, rows x (((q x).equiv z).val, (i.arrow (a x) |>.equiv r).val) =
    (machine x z r).map (fun v => (((q x).equiv v.1).val,
      (i.arrow ((a x).prod Numbering.move) |>.equiv v.2).val)))

local notation "code" => fun x => oneHot (a x).equiv (blank x)
local notation "num" => fun x => Numbering.controller (a x) (q x) i (a x).size

include hcorrect in
theorem observe_next (x : ℕ) (s : PC (A x) (Q x) I (a x).size) (r : I → Option Bool) :
    observe a q i (fun j => (a j).size) x ((CommonAlphabet.rule (code x) (machine x)) s r) =
      next a i ha blank rows x (ranks i r) (view a q i (fun j => (a j).size) x s) := by
  cases s with
  | ready z c => exact observe_ready a q i ha rows blank machine hcorrect x z c r
  | work z op mode j => exact observe_work a q i x (blank x) (machine x) z op mode j r
  | readBlock z buf j => exact observe_read a q i blank machine x z buf j r
  | rewind z c j => exact observe_rewind a q i x (blank x) (machine x) z c j r

include hcorrect in
theorem packed_correct (x : ℕ) (s : PC (A x) (Q x) I (a x).size) (r : I → Option Bool) :
    packed a q i ha hq blank rows x (((num x).equiv s).val,(i.arrow Numbering.ternary |>.equiv r).val) =
      ((CommonAlphabet.rule (code x) (machine x)) s r).map
        (fun z => (((num x).equiv z.1).val,(i.arrow (Numbering.ternary.prod Numbering.move) |>.equiv z.2).val)) := by
  unfold packed
  rw [(p).decode_rank,(dataReads).decode_rank,states_view]
  change (next a i ha blank rows x (ranks i r) (view _ _ _ _ _ _)).map _ = _
  rw [← observe_next a q i ha blank rows machine hcorrect]
  cases he : CommonAlphabet.rule (code x) (machine x) s r with
  | none => rfl
  | some u =>
    rcases u with ⟨y,o⟩
    change some ((p).encode x (view a q i (fun t => (a t).size) x y),(ternaryActions i).encode x (moves i o)) = _
    rw [← states_view a q i (fun t => (a t).size) (ha := ha) (hq := hq) (hw := ha) x y]
    exact congrArg some (Prod.ext ((p).encode_view x y) ((ternaryActions i).encode_view x o))

end Generator.Phase

end NearSquareRoot
end Computability
end OAI
