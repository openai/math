import OAI.Optimization.LinearProgramming.Compression.CircuitMachine
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

/-- Compile a layer left to right. Each result survives later temporaries because the
next output starts one register higher. -/
def compileLayer {ι : Type*} (addr : ι → ℕ) (out : ℕ) : List (ArithExpr ι) → Program
  | [] => []
  | e :: es => e.compile addr out ++ compileLayer addr (out + 1) es

theorem compileLayer_length_le {ι : Type*} (addr : ι → ℕ) (out : ℕ) (es : List (ArithExpr ι)) :
    (compileLayer addr out es).length ≤ 2 * (es.map ArithExpr.size).sum := by
  induction es generalizing out with
  | nil => simp [compileLayer]
  | cons e es ih =>
    simp only [compileLayer, List.length_append, List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (e.compile_length_le addr out) (ih (out + 1))

/-- At the end of a layer, every output is the corresponding expression evaluated in the
*initial* register file. Input scalars, live status and the complete address bank survive. -/
theorem compileLayer_spec {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (addr : ι → ℕ) (out : ℕ) (es : List (ArithExpr ι)) (s : State K)
    (hlive : s.output = none) (hfresh : ∀ i, addr i < out) :
    ∃ t, BlockExec (compileLayer addr out es) s t ∧
      (∀ (j : Fin es.length), t.data (out + j.val) = es[j.val].eval (fun i => s.data (addr i))) ∧
      (∀ j < out, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  induction es generalizing s out with
  | nil =>
    refine ⟨s, ?_, (fun j => Fin.elim0 j), fun _ _ => rfl, rfl, hlive⟩
    exact .nil _
  | cons e es ih =>
    obtain ⟨u, hblock, hres, hlow, hidx, hu⟩ := e.compile_spec addr out s hlive hfresh
    obtain ⟨t, htail, hresults, hbefore, htidx, ht⟩ :=
      ih (out + 1) u hu (fun i => Nat.lt_succ_of_lt (hfresh i))
    refine ⟨t, hblock.append htail, ?_, ?_, htidx.trans hidx, ht⟩
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa using (hbefore out (Nat.lt_succ_self out)).trans hres
      · have hread : (fun i => u.data (addr i)) = fun i => s.data (addr i) :=
          funext (fun i => hlow (addr i) (hfresh i))
        have h := hresults k
        rw [hread] at h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · intro j hj
      exact (hbefore j (Nat.lt_succ_of_lt hj)).trans (hlow j hj)

/-- A finite layer's outputs occupy the contiguous registers starting at `out`. -/
def compileFinLayer {ι : Type*} {k : ℕ} (addr : ι → ℕ) (out : ℕ)
    (es : Fin k → ArithExpr ι) : Program := compileLayer addr out (List.ofFn es)

theorem compileFinLayer_length_le {ι : Type*} {k : ℕ} (addr : ι → ℕ) (out : ℕ)
    (es : Fin k → ArithExpr ι) :
    (compileFinLayer addr out es).length ≤ 2 * ∑ i, (es i).size := by
  simpa [compileFinLayer, List.map_ofFn, List.sum_ofFn, Function.comp_def] using
    compileLayer_length_le addr out (List.ofFn es)

theorem compileFinLayer_spec {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {k : ℕ} (addr : ι → ℕ) (out : ℕ) (es : Fin k → ArithExpr ι) (s : State K)
    (hlive : s.output = none) (hfresh : ∀ i, addr i < out) :
    ∃ t, BlockExec (compileFinLayer addr out es) s t ∧
      (∀ j, t.data (out + j.val) = (es j).eval (fun i => s.data (addr i))) ∧
      (∀ j < out, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  obtain ⟨t, hcode, hres, hlow, hidx, ht⟩ := compileLayer_spec addr out (List.ofFn es) s hlive hfresh
  refine ⟨t, hcode, fun j => ?_, hlow, hidx, ht⟩
  simpa using hres ⟨j.val, by simp⟩

/-- A fixed input and a table from the preceding stage are the two sources of a layer. -/
def evalLayer {ι σ K : Type*} [Ring K] {k : ℕ} (loc : σ → Fin k)
    (es : Fin k → ArithExpr (ι ⊕ σ)) (fixed : ι → K) (v : Fin k → K) : Fin k → K :=
  fun j => (es j).eval (Sum.elim fixed (v ∘ loc))

/-- The initial table need not be contiguous. Subsequent tables are laid out back to back. -/
def layerResultAddr {k : ℕ} (initial : Fin k → ℕ) (fresh : ℕ) : ℕ → Fin k → ℕ
  | 0 => initial
  | r + 1 => fun i => fresh + r * k + i.val

def compileIterLayer {ι σ : Type*} {k : ℕ} (fixed : ι → ℕ) (loc : σ → Fin k)
    (es : Fin k → ArithExpr (ι ⊕ σ)) : ℕ → (Fin k → ℕ) → ℕ → Program
  | 0, _, _ => []
  | t + 1, initial, fresh =>
    compileFinLayer (Sum.elim fixed (initial ∘ loc)) fresh es ++
      compileIterLayer fixed loc es t (fun i => fresh + i.val) (fresh + k)

theorem compileIterLayer_length_le {ι σ : Type*} {k : ℕ} (fixed : ι → ℕ) (loc : σ → Fin k)
    (es : Fin k → ArithExpr (ι ⊕ σ)) (rounds : ℕ) (initial : Fin k → ℕ) (fresh : ℕ) :
    (compileIterLayer fixed loc es rounds initial fresh).length ≤ rounds * (2 * ∑ i, (es i).size) := by
  induction rounds generalizing initial fresh with
  | zero => simp [compileIterLayer]
  | succ rounds ih =>
    rw [compileIterLayer, List.length_append, Nat.succ_mul, Nat.add_comm (rounds * _)]
    exact Nat.add_le_add (compileFinLayer_length_le _ _ _) (ih _ _)

private theorem resultAddr_succ {k : ℕ} (initial : Fin k → ℕ) (fresh rounds : ℕ) (j : Fin k) :
    layerResultAddr initial fresh (rounds+1) j =
      layerResultAddr (fun i => fresh + i.val) (fresh+k) rounds j := by
  cases rounds with
  | zero => simp [layerResultAddr]
  | succ t => simp [layerResultAddr, Nat.succ_mul]; omega

/-- Each stage sees the complete previous table. The finite RAM execution computes the exact
iterate and preserves the fixed input even when the table layout is empty or has one entry. -/
theorem compileIterLayer_spec {ι σ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {k : ℕ} (fixed : ι → ℕ) (loc : σ → Fin k) (es : Fin k → ArithExpr (ι ⊕ σ))
    (rounds : ℕ) (initial : Fin k → ℕ) (fresh : ℕ) (s : State K)
    (hlive : s.output = none) (hfixed : ∀ i, fixed i < fresh) (hinit : ∀ j, initial j < fresh) :
    ∃ t, BlockExec (compileIterLayer fixed loc es rounds initial fresh) s t ∧
      (∀ j, t.data (layerResultAddr initial fresh rounds j) =
        ((evalLayer loc es (fun i => s.data (fixed i)))^[rounds] (fun i => s.data (initial i))) j) ∧
      (∀ j < fresh, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  induction rounds generalizing initial fresh s with
  | zero => exact ⟨s, .nil s, fun _ => rfl, fun _ _ => rfl, rfl, hlive⟩
  | succ r ih =>
    let addr := Sum.elim fixed (initial ∘ loc)
    have hadd : ∀ i, addr i < fresh := by
      rintro (i | j)
      · exact hfixed i
      · exact hinit (loc j)
    obtain ⟨u, hu, hr, hp, hi, hl⟩ := compileFinLayer_spec addr fresh es s hlive hadd
    obtain ⟨t, ht, hv, hp', hi', hl'⟩ := ih (fun j => fresh + j.val) (fresh + k) u hl
      (fun i => (hfixed i).trans_le (Nat.le_add_right ..))
      (fun j => Nat.add_lt_add_left j.isLt fresh)
    refine ⟨t, hu.append ht, ?_, ?_, hi'.trans hi, hl'⟩
    · have hfixed' : (fun i => u.data (fixed i)) = fun i => s.data (fixed i) :=
        funext fun i => hp (fixed i) (hfixed i)
      have hval : (fun j : Fin k => u.data (fresh + j.val)) =
          evalLayer loc es (fun i => s.data (fixed i)) (fun i => s.data (initial i)) := by
        funext j
        rw [hr j, evalLayer]
        apply congrArg (fun v => (es j).eval v)
        funext i
        cases i <;> rfl
      intro j
      rw [resultAddr_succ, Function.iterate_succ_apply]
      simpa only [hfixed', hval] using hv j
    · intro j hj
      exact (hp' j (hj.trans_le (Nat.le_add_right ..))).trans (hp j hj)

end Compression
end LinearProgramming
end Optimization
end OAI
