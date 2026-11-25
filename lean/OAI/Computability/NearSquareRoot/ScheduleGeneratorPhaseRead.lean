import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhase
import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhaseLists
import OAI.Computability.NearSquareRoot.ScheduleGeneratorOneHot

/-! # Computable read-block transition of the fixed-width controller -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Phase

open CommonAlphabet IntegerMultiplication

/-- Store the current track symbols and advance. On the last column the decoder
turns each buffered block into a cached symbol and the controller starts rewinding. -/
def execRead (w blank : ℕ) (r : List ℕ) (v : ℕ × List (List ℕ) × ℕ) : State × Actions :=
  let buf := PhaseLists.stash v.2.2 v.2.1 r
  let next := bif decide (v.2.2+1 < w) then read v.1 buf (v.2.2+1)
    else rewind v.1 (buf.map (OneHot.decode blank)) 0
  (next, r.map fun t => (t,2))

theorem computable_execRead {X : Type} [Primcodable X] {w blank : X → ℕ}
    {r : X → List ℕ} {v : X → ℕ × List (List ℕ) × ℕ}
    (hw : Computable w) (hb : Computable blank) (hr : Computable r) (hv : Computable v) :
    Computable fun x => execRead (w x) (blank x) (r x) (v x) := by
  have hq := Computable.fst.comp hv
  have hj := Computable.snd.comp (Computable.snd.comp hv)
  have buf := PhaseLists.computable_stash hj (Computable.fst.comp (Computable.snd.comp hv)) hr
  have adv := Computable.succ.comp hj
  have inside : Computable (fun x => read (v x).1 (PhaseLists.stash (v x).2.2 (v x).2.1 (r x))
      ((v x).2.2+1)) :=
    Computable.sumInr.comp (Computable.sumInr.comp (Computable.sumInl.comp (hq.pair (buf.pair adv))))
  have parsed := computable_map (fallback := fun _ => []) buf
    (OneHot.primrec_decode.to_comp.comp (hb.comp Computable.fst) Computable.snd).to₂ (Computable.const [])
  have donePhase : Computable (fun x => rewind (v x).1
      ((PhaseLists.stash (v x).2.2 (v x).2.1 (r x)).map (OneHot.decode (blank x))) 0) :=
    Computable.sumInr.comp (Computable.sumInr.comp (Computable.sumInr.comp (hq.pair (parsed.pair (Computable.const 0)))))
  exact (Computable.cond (Primrec.nat_lt.decide.to_comp.comp adv hw) inside donePhase).pair
    (computable_map (fallback := fun _ => 0) hr (Computable.snd.pair (Computable.const 2)).to₂ (Computable.const 0))

variable {A Q : ℕ → Type} {I : Type}
variable (a : ∀ x, Numbering (A x)) (q : ∀ x, Numbering (Q x)) (i : Numbering I)

theorem observe_read (blank : ∀ x, A x) (m : ∀ x, TM.Rule (A x) (Q x) I) (x : ℕ)
    (z : Q x) (buf : I → Letters (a x).size) (j : Fin (a x).size) (r : I → Option Bool) :
    observe a q i (fun t => (a t).size) x
      (CommonAlphabet.rule (oneHot (a x).equiv (blank x)) (m x) (.readBlock z buf j) r) =
      some (execRead (a x).size ((a x).equiv (blank x)).val (ranks i r)
        (((q x).equiv z).val, i.all.map (fun l => (List.finRange (a x).size).map
          fun k => (Numbering.ternary.equiv (buf l k)).val), j.val)) := by
  let e := (a x).equiv
  let c := oneHot e (blank x)
  have width : c.width = (a x).size := rfl
  have st := PhaseLists.stash_view i buf j r
  simp only [PhaseLists.bufferView, PhaseLists.fin_all] at st
  have dec (b : Letters (a x).size) :
      OneHot.decode (e (blank x)).val ((List.finRange (a x).size).map fun k => (Numbering.ternary.equiv (b k)).val) =
        (e (c.dec b)).val := by
    simpa only [List.ofFn_eq_map] using OneHot.decode_oneHot e (blank x) b
  change observe a q i (fun t => (a t).size) x (CommonAlphabet.rule c (m x) (.readBlock z buf j) r) = _
  unfold execRead
  simp only [observe, CommonAlphabet.rule]
  change some (view a q i (fun t => (a t).size) x (atIndex c.width _ _ (j.val+1)), _) = _
  by_cases h : j.val+1 < (a x).size
  · simp [atIndex, width, h, view, ranks, st]
    constructor <;> intros <;> rfl
  · simp [atIndex, width, h, view, ranks, st, List.map_map, Function.comp_def, dec, c, e, first]
    constructor <;> intros <;> rfl

end Generator.Phase

end NearSquareRoot
end Computability
end OAI
