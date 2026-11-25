import OAI.Computability.NearSquareRoot.ScheduleGeneratorSourceProgram
import OAI.Computability.NearSquareRoot.ScheduleGeneratorAlphabetRows
import OAI.Computability.NearSquareRoot.ScheduleGeneratorReadStart
import OAI.Computability.NearSquareRoot.ScheduleGeneratorExpandRows
import OAI.Computability.NearSquareRoot.ScheduleGeneratorCompactOneHot

/-! # Effective four-letter machine installation from arbitrary numbered source machines -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.PublicProgram
open CommonAlphabet IntegerMultiplication TM

/-- Decode the two designated literal output symbols by their finite addresses. -/
def decode {A : Type} (a : Numbering A) (bit : Bool → A) (s : A) : Option Bool :=
  if a.equiv s = a.equiv (bit false) then some false
  else if a.equiv s = a.equiv (bit true) then some true else none

theorem decode_blank {A : Type} (a : Numbering A) (bit : Bool → A) (b : A)
    (hb : ∀ v, b ≠ bit v) : decode a bit b = none := by simp [decode, hb]

theorem decode_bit {A : Type} (a : Numbering A) (bit : Bool → A)
    (h : bit false ≠ bit true) (b : Bool) : decode a bit (bit b) = some b := by
  cases b <;> simp [decode,Ne.symm h]

private def bitRank (z o n : ℕ) : ℕ := if n = z then 1 else if n = o then 2 else 0

private theorem bitRank_eq {A : Type} (a : Numbering A) (bit : Bool → A) (x : A) :
    bitRank (a.equiv (bit false)).val (a.equiv (bit true)).val (a.equiv x).val =
      (Numbering.ternary.equiv (decode a bit x)).val := by
  simp only [bitRank,decode,Fin.val_inj]
  split <;> first | rfl | split <;> rfl

private theorem computable_bitRank {z o : ℕ → ℕ} (hz : Computable z) (ho : Computable o) :
    Computable₂ fun j n => bitRank (z j) (o j) n := by
  have h : Primrec fun p : ℕ × ℕ × ℕ => bitRank p.1 p.2.1 p.2.2 :=
    Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) Primrec.fst) (Primrec.const 1)
      (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
        (Primrec.const 2) (Primrec.const 0))
  exact h.to_comp.comp ((hz.comp Computable.fst).pair ((ho.comp Computable.fst).pair Computable.snd))

/-- Effective transition rows of the public candidate before ROM installation. -/
theorem effective_rows {A Q : ℕ → Type} {I : Type} [DecidableEq I]
    (a : ∀ j, Numbering (A j)) (q : ∀ j, Numbering (Q j)) (i : Numbering I)
    (bit : ∀ j, Bool → A j) (sep blank : ∀ j, A j) (inp out : I)
    (m : ∀ j, Rule (A j) (Q j) I) (entry : ∀ j, Q j)
    (ha : Computable fun j => (a j).size) (hq : Computable fun j => (q j).size)
    (hf : Computable fun j => ((a j).equiv (bit j false)).val)
    (ht : Computable fun j => ((a j).equiv (bit j true)).val)
    (hs : Computable fun j => ((a j).equiv (sep j)).val)
    (hb : Computable fun j => ((a j).equiv (blank j)).val)
    (he : Computable fun j => ((q j).equiv (entry j)).val)
    (rows : Routing.Rows) (hr : Computable₂ rows)
    (correct : ∀ j z r, rows j (((q j).equiv z).val,((i.arrow (a j)).equiv r).val) =
      (m j z r).map fun v => (((q j).equiv v.1).val,((i.arrow ((a j).prod Numbering.move)).equiv v.2).val)) :
    let codec j := oneHot (a j).equiv (blank j)
    EffectiveRows Numbering.publicLetter (Numbering.publicIndex i.option)
      (fun j => Numbering.pipeline (a j) (Numbering.controller (a j) (q j) i (a j).size).align (a j).size)
      (fun j => Pipeline.sourceMachine (codec j) (bit j) (sep j) (decode (a j) (bit j))
        inp out (m j) (entry j)) := by
  let c j := oneHot (a j).equiv (blank j)
  let digit j := decode (a j) (bit j)
  let rank j := bitRank ((a j).equiv (bit j false)).val ((a j).equiv (bit j true)).val
  obtain ⟨ex,_,hx,hxc⟩ := ExpandRows.oneHot_family a bit sep blank ha hf ht hs hb
  obtain ⟨_,hc,hcc⟩ := CompactRows.compile_family a blank digit rank ha hb (computable_bitRank hf ht)
    (fun j x => bitRank_eq (a j) (bit j) x)
  let u j := Numbering.controller (a j) (q j) i (a j).size
  have hctrl : Computable fun j => (u j).size := (Phase.states a q i (fun j => (a j).size) ha hq ha).size_eff
  have base : EffectiveRows Numbering.ternary i u (fun j => CommonAlphabet.rule (c j) (m j)) :=
    ⟨Phase.packed a q i ha hq blank rows, Phase.computable_packed a q i ha hq blank hb rows hr,
      Phase.packed_correct a q i ha hq blank rows m correct⟩
  have core := (base.commonBlank Numbering.publicLetter (fun _ => (none : Option Bool))).align
    out (none : Public.Letter) Public.sep (fun j => readStart (c j) (entry j)) hctrl
    (Phase.readStart_rank a q i ha hq c ha entry he)
  exact PipelineRows.effective_pipeline a (fun j => (u j).align) i.option c bit sep digit
    (some inp) (some out) _ (fun _ => .boot) ha (PipelineRows.computable_align_size u hctrl)
    ha (Computable.const 0) ⟨ex,hx,hxc⟩ core ⟨_,hc,hcc⟩

/-- Given effective state and alphabet sizes, distinguished addresses, and numerical
source transitions, the ROM of the entire public machine is computable. Its entries run
the literal input expander, block simulator, folded head realignment and output decoder. -/
theorem computable_rom {A Q : ℕ → Type} {I : Type} [DecidableEq I] {M : ℕ}
    (a : ∀ j, Numbering (A j)) (q : ∀ j, Numbering (Q j)) (i : Numbering I)
    (bit : ∀ j, Bool → A j) (sep blank : ∀ j, A j) (inp out : I)
    (m : ∀ j, Rule (A j) (Q j) I) (entry : ∀ j, Q j)
    (enum : Universal.Tag Public.Letter (Pipeline.Index (Option I)) ≃ Fin (M+1))
    (ha : Computable fun j => (a j).size) (hq : Computable fun j => (q j).size)
    (hf : Computable fun j => ((a j).equiv (bit j false)).val)
    (ht : Computable fun j => ((a j).equiv (bit j true)).val)
    (hs : Computable fun j => ((a j).equiv (sep j)).val)
    (hb : Computable fun j => ((a j).equiv (blank j)).val)
    (he : Computable fun j => ((q j).equiv (entry j)).val)
    (rows : Routing.Rows) (hr : Computable₂ rows)
    (correct : ∀ j z r, rows j (((q j).equiv z).val,((i.arrow (a j)).equiv r).val) =
      (m j z r).map fun v => (((q j).equiv v.1).val,((i.arrow ((a j).prod Numbering.move)).equiv v.2).val)) :
    let codec j := oneHot (a j).equiv (blank j)
    Computable fun j =>
      (Pipeline.sourceProgram (a j) (q j) i (codec j) (bit j) (sep j) (decode (a j) (bit j))
        inp out (m j) (entry j)).map (fun t => (enum t).val) := by
  let c j := oneHot (a j).equiv (blank j)
  let u j := Numbering.controller (a j) (q j) i (a j).size
  have hctrl : Computable fun j => (u j).size := (Phase.states a q i (fun j => (a j).size) ha hq ha).size_eff
  exact PipelineRows.computable_program a (fun j => (u j).align) i.option c bit sep
    (fun j => decode (a j) (bit j)) (some inp) (some out) _ (fun _ => .boot) enum ha
    (PipelineRows.computable_align_size u hctrl) ha
    (effective_rows a q i bit sep blank inp out m entry ha hq hf ht hs hb he rows hr correct)

end Generator.PublicProgram

end NearSquareRoot
end Computability
end OAI
