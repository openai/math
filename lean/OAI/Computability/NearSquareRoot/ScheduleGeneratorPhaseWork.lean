import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhase
import OAI.Computability.NearSquareRoot.ScheduleGeneratorOneHot
import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhaseLists

/-! # Numerical write, align, and rewind transitions of the one-hot simulator -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Phase
open CommonAlphabet IntegerMultiplication

/-- During the two alignment sweeps, the physical head moves left or stays put. -/
def alignMove (mode direction : ℕ) : ℕ :=
  if mode = 1 then (if direction = 2 then 1 else 0)
  else (if direction = 0 then 0 else 1)

/-- Advance one write or alignment cell, resetting the read buffers after the second alignment. -/
def execWork (w ni blank : ℕ) (r : List ℕ) (v : ℕ × Actions × ℕ × ℕ) : State × Actions :=
  let (q, o, m, j) := v
  let state := if j + 1 < w then work q o m (j+1)
    else if m = 0 then work q o 1 0
    else if m = 1 then work q o 2 0
    else read q (List.replicate ni (List.replicate w 0)) 0
  let ops := if m = 0 then o.map (fun p => (OneHot.encode p.1 blank j, 2))
    else List.zipWith (fun p d => (d, alignMove m p.2)) o r
  (state, ops)

/-- Rewind all tracks simultaneously, restoring the cached-symbol state at the block boundary. -/
def execRewind (w : ℕ) (r : List ℕ) (v : ℕ × List ℕ × ℕ) : State × Actions :=
  let (q, a, j) := v
  (if j + 1 < w then rewind q a (j+1) else ready q a, r.map (fun d => (d,0)))

variable {X R : Type} [Primcodable X] [Primcodable R]

private theorem ifEq {n : X → ℕ} (hn : Computable n) (k : ℕ) {a b : X → R}
    (ha : Computable a) (hb : Computable b) :
    Computable fun x => if n x = k then a x else b x :=
  (Computable.cond (Primrec.eq.decide.to_comp.comp hn (Computable.const k)) ha hb).of_eq
    fun _ => by simp

private theorem ifLt {j w : X → ℕ} (hj : Computable j) (hw : Computable w) {a b : X → R}
    (ha : Computable a) (hb : Computable b) :
    Computable fun x => if j x < w x then a x else b x :=
  (Computable.cond (Primrec.nat_lt.decide.to_comp.comp hj hw) ha hb).of_eq fun _ => by simp

private theorem work_eff {q m j : X → ℕ} {o : X → Actions} (hq : Computable q)
    (ho : Computable o) (hm : Computable m) (hj : Computable j) :
    Computable fun x => work (q x) (o x) (m x) (j x) :=
  Computable.sumInr.comp (Computable.sumInl.comp (hq.pair (ho.pair (hm.pair hj))))

private theorem alignMove_eff : Primrec₂ alignMove :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1) (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0) (Primrec.const 1))

theorem computable_execWork {w ni blank : X → ℕ} {r : X → List ℕ} {v : X → ℕ × Actions × ℕ × ℕ}
    (hw : Computable w) (hi : Computable ni) (hb : Computable blank) (hr : Computable r) (hv : Computable v) :
    Computable fun x => execWork (w x) (ni x) (blank x) (r x) (v x) := by
  have hq := Computable.fst.comp hv
  have ho := Computable.fst.comp (Computable.snd.comp hv)
  have hm := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hv))
  have hj := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hv))
  have hn := Primrec.nat_add.to_comp.comp hj (Computable.const 1)
  apply Computable.pair
  · apply ifLt hn hw (work_eff hq ho hm hn)
    apply ifEq hm 0 (work_eff hq ho (Computable.const 1) (Computable.const 0))
    apply ifEq hm 1 (work_eff hq ho (Computable.const 2) (Computable.const 0))
    exact Computable.sumInr.comp (Computable.sumInr.comp (Computable.sumInl.comp
      (hq.pair ((computable_replicate hi (computable_replicate hw (Computable.const 0))).pair (Computable.const 0)))))
  · apply ifEq hm 0
    · apply computable_map ho _ (Computable.const (0,0))
      exact ((OneHot.computable_encode (Computable.fst.comp Computable.snd)
        (hb.comp Computable.fst) (hj.comp Computable.fst)).pair (Computable.const 2)).to₂
    · apply computable_zipWith (f := fun x p => (p.2, alignMove (v x).2.2.1 p.1.2)) ho hr
      exact ((Computable.snd.comp Computable.snd).pair (alignMove_eff.to_comp.comp
        (hm.comp Computable.fst) (Computable.snd.comp (Computable.fst.comp Computable.snd)))).to₂

theorem computable_execRewind {w : X → ℕ} {r : X → List ℕ} {v : X → ℕ × List ℕ × ℕ}
    (hw : Computable w) (hr : Computable r) (hv : Computable v) :
    Computable fun x => execRewind (w x) (r x) (v x) := by
  have hq := Computable.fst.comp hv
  have ha := Computable.fst.comp (Computable.snd.comp hv)
  have hj := Computable.snd.comp (Computable.snd.comp hv)
  have hn := Primrec.nat_add.to_comp.comp hj (Computable.const 1)
  apply Computable.pair
  · apply ifLt hn hw
    · exact Computable.sumInr.comp (Computable.sumInr.comp (Computable.sumInr.comp (hq.pair (ha.pair hn))))
    · exact Computable.sumInl.comp (hq.pair ha)
  · exact computable_map hr (Computable.snd.pair (Computable.const 0)).to₂ (Computable.const 0)

private theorem alignMove₁ (d : TM.Move) :
    alignMove 1 (Numbering.move.equiv d).val = (Numbering.move.equiv (turn₁ d)).val := by
  cases d <;> rfl

private theorem alignMove₂ (d : TM.Move) :
    alignMove 2 (Numbering.move.equiv d).val = (Numbering.move.equiv (turn₂ d)).val := by
  cases d <;> rfl

variable {A Q : ℕ → Type} {I : Type}
variable (a : ∀ x, Numbering (A x)) (q : ∀ x, Numbering (Q x)) (i : Numbering I)
variable (x : ℕ) (blank : A x) (m : TM.Rule (A x) (Q x) I)

theorem observe_work (z : Q x) (op : I → A x × TM.Move) (mode : Mode)
    (j : Fin (a x).size) (r : I → Option Bool) :
    observe a q i (fun n => (a n).size) x
      (CommonAlphabet.rule (oneHot (a x).equiv blank) m (.work z op mode j) r) =
      some (execWork (a x).size i.size ((a x).equiv blank).val (ranks i r)
        (((q x).equiv z).val, i.all.map (fun t =>
          (((a x).equiv (op t).1).val,(Numbering.move.equiv (op t).2).val)),
          (Numbering.mode.equiv mode).val, j.val)) := by
  have hm₀ : (Numbering.mode.equiv .write).val = 0 := rfl
  have hm₁ : (Numbering.mode.equiv .align₁).val = 1 := rfl
  have hm₂ : (Numbering.mode.equiv .align₂).val = 2 := rfl
  have hw : (oneHot (a x).equiv blank).width = (a x).size := rfl
  cases mode <;> by_cases h : j.val + 1 < (a x).size <;>
    simp [CommonAlphabet.rule, atIndex, hw, h, observe, view, execWork, moves, ranks, hm₀, hm₁, hm₂,
      List.map_map, Function.comp_def,
      OneHot.encode_oneHot, alignMove₁, alignMove₂, readStart, Numbering.all] <;> try rfl
  simp [Option.map, emptyBuffer, List.map_const', first, hold,
    show (Numbering.ternary.equiv none).val = 0 from rfl]

theorem observe_rewind (z : Q x) (c : I → A x) (j : Fin (a x).size) (r : I → Option Bool) :
    observe a q i (fun n => (a n).size) x
      (CommonAlphabet.rule (oneHot (a x).equiv blank) m (.rewind z c j) r) =
      some (execRewind (a x).size (ranks i r)
        (((q x).equiv z).val, i.all.map (fun t => ((a x).equiv (c t)).val), j.val)) := by
  have hw : (oneHot (a x).equiv blank).width = (a x).size := rfl
  by_cases h : j.val + 1 < (a x).size <;>
    simp [CommonAlphabet.rule, atIndex, hw, h, observe, view, execRewind, moves, ranks, List.map_map, Function.comp_def] <;> rfl

end Generator.Phase

end NearSquareRoot
end Computability
end OAI
