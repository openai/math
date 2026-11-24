import OAI.Computability.VPVNP.RankQueryStackExpressions

/-!
# Fixed bit-stack compilation of Schur descriptor and child requests

A decision tree computes each of six result words from the immutable eight
inputs. Each test compiles its two expressions to separate scratch intervals.
The same scratch bank is reused for the selected subtree and the remaining
output words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Dispatch

open BurstRAM PrivateRAM RAMTape

namespace Code

variable {r w : ℕ}

/-- Scratch-register allowance for computing one output field, counting its leaf expressions
and both sides of every test. -/
def need (field : Fin 6) : Code → ℕ
  | .emit f => (f field).nodes
  | .test x y yes no => x.nodes+y.nodes+yes.need field+no.need field

/-- Sum of expression weights used to bound the word width for one field of the dispatch tree. -/
def bits (field : Fin 6) : Code → ℕ
  | .emit f => (f field).weight
  | .test x y yes no => x.weight+y.weight+yes.bits field+no.bits field

/-- Compile the tests and leaves that compute a single output field into register instructions. -/
def fieldCode (arg : Fin 8 → Fin r) (out : Fin r) (slot : ℕ → Fin r) (field : Fin 6) : Code → RegCode r
  | .emit f => .seq ((f field).compile arg slot 0) (.copy out (slot 0))
  | .test x y yes no =>
    .seq (x.compile arg slot 0) <| .seq (y.compile arg slot x.nodes) <|
      .test (slot 0) (slot x.nodes) (yes.fieldCode arg out slot field) (no.fieldCode arg out slot field)

theorem fieldCode_preserves (c : Code) (arg : Fin 8 → Fin r) (out : Fin r) (slot : ℕ → Fin r)
    (field : Fin 6) (rs : Regs r w) (j : Fin r) (hout : j ≠ out)
    (hs : ∀ i < c.need field, slot i ≠ j) : (c.fieldCode arg out slot field).exec rs j = rs j := by
  induction c generalizing rs with
  | emit f =>
    simp only [fieldCode, RegCode.exec, Function.update_of_ne hout]
    apply Expr.preserves
    intro i _ hi
    exact hs i (by simpa [need] using hi)
  | test x y yes no ihy ihn =>
    simp only [fieldCode, RegCode.exec]
    have hsx : ∀ i, 0 ≤ i → i < 0+x.nodes → slot i ≠ j := fun i _ h => hs _ (by simp only [need]; omega)
    have hsy : ∀ i, x.nodes ≤ i → i < x.nodes+y.nodes → slot i ≠ j := fun i _ h => hs _ (by simp only [need]; omega)
    have hy : ∀ i < yes.need field, slot i ≠ j := fun i h => hs i (by simp only [need]; omega)
    have hn : ∀ i < no.need field, slot i ≠ j := fun i h => hs i (by simp only [need]; omega)
    split_ifs <;> first | rw [ihy _ hy] | rw [ihn _ hn]
    all_goals rw [y.preserves _ _ _ _ _ hsy, x.preserves _ _ _ _ _ hsx]

theorem fieldCode_correct (c : Code) (arg : Fin 8 → Fin r) (out : Fin r) (slot : ℕ → Fin r)
    (field : Fin 6) (p cap : ℕ) (env : Fin 8 → ℕ) (rs : Regs r w)
    (he : ∀ i, env i < 2^p) (hr : ∀ i, (rs (arg i)).val = env i)
    (hn : c.need field ≤ cap) (hb : (p+1)*c.bits field ≤ w)
    (hinj : ∀ i < cap, ∀ j < cap, slot i = slot j → i = j)
    (hsep : ∀ i < cap, ∀ j, slot i ≠ arg j) :
    ((c.fieldCode arg out slot field).exec rs out).val = c.eval env field := by
  induction c generalizing rs with
  | emit f =>
    simp only [fieldCode, RegCode.exec, Function.update_self, Code.eval]
    exact (f field).compile_correct env arg slot cap 0 rs
      ((f field).fits_mono ((f field).fits_weight p env he) hb) hr (by simpa [need] using hn) hinj hsep
  | test x y yes no ihy ihn =>
    let xs := (x.compile arg slot 0).exec rs
    let ys := (y.compile arg slot x.nodes).exec xs
    have hsize : x.nodes+y.nodes+yes.need field+no.need field ≤ cap := hn
    have hwidth : (p+1)*x.weight+(p+1)*y.weight+(p+1)*yes.bits field+(p+1)*no.bits field ≤ w := by
      simpa only [bits, Nat.mul_add] using hb
    have hx := x.compile_correct env arg slot cap 0 rs
      (x.fits_mono (x.fits_weight p env he) (by omega)) hr (by omega) hinj hsep
    have hxs (j : Fin 8) : (xs (arg j)).val = env j := by
      change ((x.compile arg slot 0).exec rs (arg j)).val = _
      rw [x.preserves _ _ _ _ _ (fun i _ hi => hsep i (by omega) j), hr]
    have hy := y.compile_correct env arg slot cap x.nodes xs
      (y.fits_mono (y.fits_weight p env he) (by omega)) hxs (by omega) hinj hsep
    have hys (j : Fin 8) : (ys (arg j)).val = env j := by
      change ((y.compile arg slot x.nodes).exec xs (arg j)).val = _
      rw [y.preserves _ _ _ _ _ (fun i _ hi => hsep i (by omega) j), hxs]
    have hkeep : ys (slot 0) = xs (slot 0) := by
      apply y.preserves
      intro i hi hc heq
      have := x.nodes_pos
      have := hinj i (by omega) 0 (by omega) heq
      omega
    have htest : ys (slot 0) = ys (slot x.nodes) ↔ x.eval env = y.eval env := by
      rw [Fin.ext_iff, hkeep, show (xs (slot 0)).val = _ from hx, show (ys (slot x.nodes)).val = _ from hy]
    change ((if ys (slot 0) = ys (slot x.nodes) then (yes.fieldCode arg out slot field).exec ys
      else (no.fieldCode arg out slot field).exec ys) out).val = _
    rw [Code.eval]
    by_cases hh : x.eval env = y.eval env
    · simp only [ite_eq_left hh, ite_eq_left (htest.mpr hh)]
      exact ihy ys hys (by omega) (by omega)
    · simp only [ite_eq_right hh, ite_eq_right (fun h => hh (htest.mp h))]
      exact ihn ys hys (by omega) (by omega)

/-- Total scratch allowance obtained by summing the register requirements of all six output
fields. -/
def scratch (c : Code) := ∑ i : Fin 6, c.need i
/-- Sum of the six output fields' width factors for the compiled dispatcher. -/
def wordFactor (c : Code) := ∑ i : Fin 6, c.bits i

/-- Inputs occupy slots zero through seven, and the result words occupy slots
eight through thirteen. The scratch interval starts at fourteen. -/
def inReg (cap : ℕ) (i : Fin 8) : Fin (14+cap) := ⟨i.val, by omega⟩
/-- Physical output register for field `i`, following the eight input registers. -/
def outReg (cap : ℕ) (i : Fin 6) : Fin (14+cap) := ⟨8+i.val, by omega⟩
/-- Scratch register at offset `i` from the end of the fourteen input and output registers,
indexed modulo the bank size. -/
def workReg (cap : ℕ) (i : ℕ) : Fin (14+cap) := Fin.ofNat _ (14+i)

private theorem workReg_val {cap i : ℕ} (h : i < cap) : (workReg cap i).val = 14+i :=
  Nat.mod_eq_of_lt (by omega)

private theorem input_separate {cap i : ℕ} (h : i < cap) (j : Fin 8) : workReg cap i ≠ inReg cap j := by
  intro he
  have := congrArg Fin.val he
  simp only [workReg_val h, inReg] at this
  omega

private theorem output_separate {cap i : ℕ} (h : i < cap) (j : Fin 6) : workReg cap i ≠ outReg cap j := by
  intro he
  have := congrArg Fin.val he
  simp only [workReg_val h, outReg] at this
  omega

private theorem in_ne_out (cap : ℕ) (i : Fin 8) (j : Fin 6) : inReg cap i ≠ outReg cap j := by
  intro he
  have := congrArg Fin.val he
  simp only [inReg,outReg] at this
  omega

private theorem out_inj (cap : ℕ) : Function.Injective (outReg cap) := by
  intro i j he
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val he)

/-- Reuse one scratch bank while evaluating a finite sequence of output fields. -/
def emitFields (c : Code) (cap : ℕ) : List (Fin 6) → RegCode (14+cap)
  | [] => .ret
  | i::is => .seq (c.fieldCode (inReg cap) (outReg cap i) (workReg cap) i) (emitFields c cap is)

private theorem emitFields_correct (c : Code) (cap p : ℕ) (is : List (Fin 6)) (rs : Regs (14+cap) w)
    (env : Fin 8 → ℕ) (hcap : c.scratch ≤ cap) (hw : (p+1)*c.wordFactor ≤ w)
    (he : ∀ i, env i < 2^p) (hr : ∀ i, (rs (inReg cap i)).val = env i) :
    let fin := (c.emitFields cap is).exec rs
    (∀ i, fin (inReg cap i) = rs (inReg cap i)) ∧
      ∀ i, (fin (outReg cap i)).val = if i ∈ is then c.eval env i else (rs (outReg cap i)).val := by
  induction is generalizing rs with
  | nil => simp [emitFields, RegCode.exec]
  | cons j js ih =>
    let body := c.fieldCode (inReg cap) (outReg cap j) (workReg cap) j
    let middle := body.exec rs
    have hneed : c.need j ≤ cap := (Finset.single_le_sum (f := c.need) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hcap
    have hbits := Finset.single_le_sum (f := c.bits) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hinput (i : Fin 8) : middle (inReg cap i) = rs (inReg cap i) :=
      c.fieldCode_preserves _ _ _ _ _ _ (in_ne_out cap i j) (fun _ hi => input_separate (hi.trans_le hneed) i)
    have hval : (middle (outReg cap j)).val = c.eval env j :=
      c.fieldCode_correct _ _ _ _ p cap _ _ he hr hneed ((Nat.mul_le_mul_left _ hbits).trans hw)
        (fun i hi j hj h => Nat.add_left_cancel (by simpa only [workReg_val hi,workReg_val hj] using congrArg Fin.val h))
        (fun _ hi j => input_separate hi j)
    obtain ⟨hinputs, houtputs⟩ := ih middle (fun i => (congrArg Fin.val (hinput i)).trans (hr i))
    refine ⟨fun i => (hinputs i).trans (hinput i), fun i => ?_⟩
    change (((c.emitFields cap js).exec middle) (outReg cap i)).val = _
    rw [houtputs]
    by_cases heq : i = j
    · subst i
      simp [hval]
    · have hkeep : middle (outReg cap i) = rs (outReg cap i) :=
        c.fieldCode_preserves _ _ _ _ _ _ ((out_inj cap).ne heq) (fun _ hi => output_separate (hi.trans_le hneed) i)
      simp [heq, hkeep]

/-- Compile the dispatch tree to a physical machine that emits all six output fields. -/
def physical (c : Code) (cap : ℕ) : Machine (14+cap) := (c.emitFields cap (List.finRange 6)).compile

/-- The fixed compiled bit-stack program returns all six output words, while
preserving its eight input words. Its finite control and scratch count depend
only on the syntax of the decision tree. -/
theorem physical_runs (c : Code) (cap p : ℕ) (hcap : c.scratch ≤ cap)
    (env : Fin 8 → ℕ) (rs : Regs (14+cap) w) (hw : (p+1)*c.wordFactor ≤ w)
    (he : ∀ i, env i < 2^p) (hr : ∀ i, (rs (inReg cap i)).val = env i)
    (pub : Fin 0 → Word w) (persistent : Word w) :
    ∃ t ≤ (c.emitFields cap (List.finRange 6)).length * (100*(w+1)^2), ∃ out,
      (c.physical cap).Runs t (ISA.bank pub persistent rs []) (ISA.bank pub persistent out []) ∧
        (∀ i, out (inReg cap i) = rs (inReg cap i)) ∧ ∀ i, (out (outReg cap i)).val = c.eval env i := by
  obtain ⟨t,ht,hrun⟩ := (c.emitFields cap (List.finRange 6)).compile_runs pub persistent rs
  obtain ⟨hinputs,houtputs⟩ := c.emitFields_correct cap p (List.finRange 6) rs env hcap hw he hr
  refine ⟨t,ht,_,hrun,hinputs,fun i => ?_⟩
  simpa using houtputs i

end Code

end RankQuery.Stack.Dispatch

end VPVNP
end Computability
end OAI
