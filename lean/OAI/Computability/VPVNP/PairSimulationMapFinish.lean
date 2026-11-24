import OAI.Computability.VPVNP.PairSimulationMapTotalCheck
import OAI.Computability.VPVNP.PairSimulationPrivateLabels
import OAI.Computability.VPVNP.PairSimulationMapStream

/-!
# Finishing a grouped map in the native private workspace

The entry's complete payload vector is checked before any parameter counter
is incremented. A successful check processes the emitted ordinals in copy
order, preserving the multiplicity of repeated labels.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapFinish

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM MotifSelector
open scoped Fin.CommRing

variable {J D E Q V : Type*} {w p r k t u bits : ℕ}

open private nameRun_value from OAI.Computability.VPVNP.MotifEntry

/-- Split the actual metered entry into the selector stage, the full-vector
test and the list of exact local parameter names. -/
theorem entry_value [DecidableEq J] [Fintype D] [Fintype E]
    (src dst : D → J) (a b : D → ℕ) (G : Supply J E) (width : Q → E → ℕ)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e ↦ MotifSelector.Word (width s e)) j → V)
    (table : List Q) (code : Q ↪ MotifSelector.Word bits) (v : E → ℕ) (j : J)
    (d : MotifEntry.DemandBits src dst b j) (x : Half G (fun e ↦ Fin (v e + u * bits) → Bool) j) :
    (MotifEntry.run src dst a b G width lookup table code v j d x).1 =
      (MotifEntry.selectorRun G table code v j x).1.bind fun θ ↦
        if ∀ e, v e = totalWidth width θ e then some (List.ofFn fun i ↦
          MapStream.readRow src dst a b G width lookup v j d x i (θ i)
            (fun e ↦ MotifEntry.offset (fun l ↦ width (θ l) e) i)) else none := by
  unfold MotifEntry.run
  dsimp only
  cases h : (MotifEntry.selectorRun G table code v j x).1 with
  | none => rfl
  | some θ =>
    dsimp only
    rw [MotifEntry.totalRun_spec]
    simp only [decide_eq_true_eq, Option.bind_some]
    split
    · simp only [(MotifEntry.scanCopies_spec _).1, nameRun_value, MapStream.readRow]
    · rfl

/-- The fixed registers used by the counter loop are initialized before
checking the width vector. The width comparisons do not change them. -/
structure HistogramReady (reg : Fin 6 ↪ Fin r) (src base : ℕ) (c : Config w p r) : Prop where
  cursor : c.reg (reg 0) = (src : BurstRAM.Word w)
  stop : c.reg (reg 1) = ((src + u : ℕ) : BurstRAM.Word w)
  base : c.reg (reg 2) = (base : BurstRAM.Word w)
  one : c.reg (reg 3) = 1

open scoped Classical in
/-- Follow the actual width guards and the native private label scan in one
machine. Every syntactic width mismatch exits before its first counter write. -/
theorem native (width : Q → E → ℕ) (θ : Fin u → Q) (v : E → ℕ) (es : List E)
    (cover : ∀ e, e ∈ es) (lhs rhs : E → Fin r) (tmp : Fin r) (M : Machine w p r k)
    (guardPC : (MapWidths.checkCode lhs rhs tmp es : Flow r k).Label → Fin p)
    (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done bad : Fin p)
    (guards : Flow.Linked M (MapWidths.checkCode lhs rhs tmp es) guardPC (pc 0) bad)
    (counts : PrivateLabels.Linked M pc reg done) (src base : ℕ)
    (names : Fin u → Fin t) (c : Config w p r)
    (hc : c.pc = guardPC (MapWidths.checkCode lhs rhs tmp es : Flow r k).entry)
    (hx : ∀ e, (c.reg (lhs e)).val = totalWidth width θ e) (hy : ∀ e, (c.reg (rhs e)).val = v e)
    (ready : HistogramReady (u := u) reg src base c) (hfit : base + t ≤ 2 ^ w)
    (apart : src + u ≤ base ∨ base + t ≤ src) (endFit : src + u < 2 ^ w)
    (data : ∀ i : Fin u, c.privateMem ((src + i.val : ℕ) : BurstRAM.Word w) =
      ((names i).val : BurstRAM.Word w)) :
    ∃ n out, n ≤ (es.length + 1) + (7 * u + 1) ∧ Prefix M c (List.replicate n .tick) out ∧
      out.persistent = c.persistent ∧
      if ∀ e, v e = totalWidth width θ e then out.pc = done ∧
        out.privateMem = PrivateLabels.accumulate base (List.ofFn names) c.privateMem
      else out.pc = bad ∧ out.privateMem = c.privateMem := by
  classical
  obtain ⟨g, hg, pre⟩ := MapWidths.totalCheck_native width θ v es cover lhs rhs tmp M guardPC
    (pc 0) bad guards c hc hx hy
  by_cases valid : ∀ e, v e = totalWidth width θ e
  · rw [ite_eq_left valid] at pre
    let mid := {c with pc := pc 0}
    let ns := List.ofFn names
    have hlen : ns.length = u := List.length_ofFn
    have stored (i : Fin ns.length) : mid.privateMem ((src + i.val : ℕ) : BurstRAM.Word w) =
        (ns[i.val].val : BurstRAM.Word w) := by
      have hi : i.val < u := hlen ▸ i.isLt
      simpa [ns, mid] using data ⟨i.val, hi⟩
    obtain ⟨out, run, hpc, mem, per⟩ := PrivateLabels.run_separated counts ns src base mid rfl
      ready.cursor
      (by rw [hlen]; exact ready.stop) ready.base ready.one hfit (by simpa only [hlen] using apart)
      (by simpa only [hlen] using endFit) stored
    refine ⟨g + (7 * u + 1), out, Nat.add_le_add_right hg _, ?_, per, ?_⟩
    · rw [List.replicate_add, ← hlen]
      exact pre.append run
    · rw [ite_eq_left valid]
      exact ⟨hpc, mem⟩
  · rw [ite_eq_right valid] at pre
    exact ⟨g, {c with pc := bad}, hg.trans (Nat.le_add_right ..), pre, rfl,
      by rw [ite_eq_right valid]; exact ⟨rfl, rfl⟩⟩

end PairSimulation.MapFinish

end VPVNP
end Computability
end OAI
