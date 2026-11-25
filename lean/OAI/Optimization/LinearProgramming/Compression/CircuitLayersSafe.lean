import OAI.Optimization.LinearProgramming.Compression.CircuitMachineSafe
import OAI.Optimization.LinearProgramming.Compression.CircuitLayers

/-! Intermediate-value invariants for repeated layers of the scalar machine. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

variable {K : Type*}

open RAM

variable {ι σ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Safe scalar evaluations compose when each expression reads only the original registers. -/
theorem compileLayer_safe (P : K → Prop) (addr : ι → ℕ) (out : ℕ) (es : List (ArithExpr ι))
    (s : State K) (hlive : s.output = none) (hfresh : ∀ i, addr i < out)
    (initial : ∀ j, P (s.data j)) (hzero : P 0)
    (hvals : ∀ e ∈ es, e.AllValues (fun i => s.data (addr i)) P) :
    ∃ t, SafeBlock P (compileLayer addr out es) s t := by
  induction es generalizing s out with
  | nil => exact ⟨s, .nil _ initial⟩
  | cons e es ih =>
    obtain ⟨u, hsafe⟩ := e.compile_safe addr out s hlive hfresh initial hzero
      (hvals e List.mem_cons_self)
    obtain ⟨u', hblock, _, hlow, _, hu⟩ := e.compile_spec addr out s hlive hfresh
    have hsame := hsafe.toBlockExec.deterministic hblock
    subst u'
    have hread : (fun i => u.data (addr i)) = fun i => s.data (addr i) :=
      funext fun i => hlow (addr i) (hfresh i)
    obtain ⟨t, htail⟩ := ih (out+1) u hu (fun i => Nat.lt_succ_of_lt (hfresh i))
      hsafe.last_ok (fun f hf => by rw [hread]; exact hvals f (List.mem_cons_of_mem _ hf))
    exact ⟨t, hsafe.append htail⟩

theorem compileFinLayer_safe {k : ℕ} (P : K → Prop) (addr : ι → ℕ) (out : ℕ)
    (es : Fin k → ArithExpr ι) (s : State K) (hlive : s.output = none)
    (hfresh : ∀ i, addr i < out) (initial : ∀ j, P (s.data j)) (hzero : P 0)
    (hvals : ∀ j, (es j).AllValues (fun i => s.data (addr i)) P) :
    ∃ t, SafeBlock P (compileFinLayer addr out es) s t := by
  apply compileLayer_safe P addr out (List.ofFn es) s hlive hfresh initial hzero
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact hvals i

/-- A stage-by-stage value bound holds throughout the RAM run, including scratch registers
written before the complete table is available. -/
theorem compileIterLayer_safe {k : ℕ} (P : K → Prop) (fixed : ι → ℕ) (loc : σ → Fin k)
    (es : Fin k → ArithExpr (ι ⊕ σ)) (rounds : ℕ) (initial : Fin k → ℕ) (fresh : ℕ)
    (s : State K) (hlive : s.output = none) (hfixed : ∀ i, fixed i < fresh)
    (hinit : ∀ j, initial j < fresh) (start : ∀ j, P (s.data j)) (hzero : P 0)
    (hvals : ∀ r < rounds, ∀ j, (es j).AllValues (Sum.elim (fun i => s.data (fixed i))
      (((evalLayer loc es (fun i => s.data (fixed i)))^[r] (fun i => s.data (initial i))) ∘ loc)) P) :
    ∃ t, SafeBlock P (compileIterLayer fixed loc es rounds initial fresh) s t := by
  induction rounds generalizing initial fresh s with
  | zero => exact ⟨s, .nil _ start⟩
  | succ r ih =>
    let addr := Sum.elim fixed (initial ∘ loc)
    have hadd : ∀ a, addr a < fresh := by
      rintro (i | j)
      · exact hfixed i
      · exact hinit (loc j)
    have fread : (fun i => s.data (addr i)) = Sum.elim (fun i => s.data (fixed i))
        ((fun i => s.data (initial i)) ∘ loc) := by
      funext i
      cases i <;> rfl
    have hfirst (j) : (es j).AllValues (fun i => s.data (addr i)) P := by
      rw [fread]
      exact hvals 0 (Nat.zero_lt_succ r) j
    obtain ⟨u, hu⟩ := compileFinLayer_safe P addr fresh es s hlive hadd start hzero hfirst
    obtain ⟨u', hblock, hr, hp, _, hl⟩ := compileFinLayer_spec addr fresh es s hlive hadd
    have hsame := hu.toBlockExec.deterministic hblock
    subst u'
    have hfixed' : (fun i => u.data (fixed i)) = fun i => s.data (fixed i) :=
      funext fun i => hp (fixed i) (hfixed i)
    have hval : (fun j : Fin k => u.data (fresh + j.val)) =
        evalLayer loc es (fun i => s.data (fixed i)) (fun i => s.data (initial i)) := by
      funext j
      rw [hr j, fread]
      rfl
    obtain ⟨t, htail⟩ := ih (fun j => fresh + j.val) (fresh+k) u hl
      (fun i => (hfixed i).trans_le (Nat.le_add_right ..))
      (fun j => Nat.add_lt_add_left j.isLt fresh) hu.last_ok (fun b hb j => by
        rw [hfixed', hval]
        exact hvals (b+1) (Nat.succ_lt_succ hb) j)
    exact ⟨t, hu.append htail⟩

end Compression
end LinearProgramming
end Optimization
end OAI
