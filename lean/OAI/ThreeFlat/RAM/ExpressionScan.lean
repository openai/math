import OAI.ThreeFlat.RAM.DescriptorScan
import OAI.ThreeFlat.RAM.DescriptorExpr

namespace OAI
/-! # Scanning an interval with a compiled row-address expression -/

namespace ThreeFlat.RAM.DescriptorScan

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM DescriptorExpr

variable {w p r k : ℕ}

def agreesOutside (lo hi : ℕ) (m m₀ : Memory w) : Prop :=
  ∀ a, a < lo ∨ hi ≤ a → m a = m₀ a

def scanInvariant (R : Fin 4 ↪ Fin r) (lo hi : ℕ) (m₀ : Memory w)
    (c : Config w p r) (m : Memory w) : Prop :=
  c.reg (R 3) = 1 ∧ lo ≤ (c.reg (R 0)).val ∧ (c.reg (R 1)).val = hi ∧
    agreesOutside lo hi m m₀

/-- It suffices to verify the denotation of a one-input word expression on
the source memory outside the destination interval. The expression compiler
executes all arithmetic, comparisons, and memory reads in native code. -/
theorem describes_expression (M : Machine w p r k) (R : Fin 4 ↪ Fin r) (L : Labels p)
    (e : Term w k 1) (loc : Fin e.labels → Fin p) (tmp : Fin e.binds ↪ Fin r)
    (fresh : ∀ i j, R i ≠ tmp j) (entry : loc e.first = L.describe)
    (rom : ∀ i, M.code (loc i) =
      e.emit loc (fun _ => R 0) tmp (R 2) L.store i)
    (lo hi : ℕ) (m₀ : Memory w) (word : ℕ → Word w)
    (correct : ∀ (a : Word w) (m : Memory w), lo ≤ a.val → a.val < hi →
      agreesOutside lo hi m m₀ → e.eval M.publicData m (fun _ => a) = word a.val) :
    Describes M R L e.steps word (scanInvariant R lo hi m₀) := by
  intro c m _ inv lt
  obtain ⟨unit, hlow, upper, frame⟩ := inv
  let start := {c with pc := L.describe}
  let out := e.run M.publicData m (fun _ => R 0) tmp (R 2) L.store start
  have keep (i : Fin 4) (hne : i ≠ 2) : out.reg (R i) = c.reg (R i) :=
    (e.run_frame M.publicData m (fun _ => R 0) tmp (R 2) L.store start).2.2 (R i)
      (R.injective.ne hne) (fresh i)
  have hlt : (c.reg (R 0)).val < hi := by
    rw [← upper]
    exact lt
  have produced : out.reg (R 2) = word (c.reg (R 0)).val :=
    (e.run_result M.publicData m (fun _ => R 0) tmp (R 2) L.store start
      (fun _ => fresh 0) tmp.injective).trans (correct _ m hlow hlt frame)
  have one : out.reg (R 3) = 1 := (keep 3 (by decide)).trans unit
  refine ⟨e.steps, le_rfl, out, e.advance_emit M loc (fun _ => R 0) tmp (R 2) L.store rom
    start m entry.symm, e.run_pc .., keep 0 (by decide), keep 1 (by decide), one, produced, ?_⟩
  have unchanged (i : Fin 4) (h : i ≠ 0) : (next R L out).reg (R i) = out.reg (R i) :=
    Function.update_of_ne (R.injective.ne h) ..
  refine ⟨(unchanged 3 (by decide)).trans one, ?_, ?_, ?_⟩
  · simp only [next, Config.put_same, keep 0 (by decide), one]
    have h := (c.reg (R 1)).isLt
    rw [Fin.val_add_one_of_lt' (by omega)]
    omega
  · rw [unchanged 1 (by decide), keep 1 (by decide), upper]
  · intro a ha
    have ne : a ≠ (c.reg (R 0)).val := by omega
    simpa [writeMemory, ne] using frame a ha

end ThreeFlat.RAM.DescriptorScan

end OAI
