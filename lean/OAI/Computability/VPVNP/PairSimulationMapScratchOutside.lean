import OAI.Computability.VPVNP.PairSimulationMapScratch
import OAI.Computability.VPVNP.PairSimulationHistogramFrame
import OAI.Computability.VPVNP.PairPendingArguments

/-!
# Exterior words of the grouped map's deterministic scratch update

The descriptor and directory writes affect their indexed words. The selector
and label writes affect fitted consecutive intervals. Histogram increments
affect their selected bins. This calculation applies to any incoming scratch
in the pure map interpreter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapScratch

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifEntry MapCallSetup MapEntryTable
open scoped Fin.CommRing

private theorem write_other {w n : ℕ} (base : BurstRAM.Word w)
    (value : Fin n → BurstRAM.Word w) (old : PrivateScratch.Memory w) (q : BurstRAM.Word w)
    (apart : ∀ i : Fin n, q ≠ base + (i.val : BurstRAM.Word w)) :
    PrivateScratch.write base value old q = old q := by
  unfold PrivateScratch.write
  apply dite_eq_right
  rintro ⟨i, hi⟩
  exact apart i hi.symm

private theorem apart_of_interval {w n base : ℕ} (q : BurstRAM.Word w)
    (room : base + n ≤ 2 ^ w) (outside : q.val < base ∨ base + n ≤ q.val) (i : Fin n) :
    q ≠ (base : BurstRAM.Word w) + (i.val : BurstRAM.Word w) := by
  intro eqn
  have val := congrArg Fin.val eqn
  rw [← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans_le
    room)] at val
  have := i.isLt
  omega

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {r k p w t u : ℕ}
  (A : Allocation B z j r k) (args : Arg D E ≃ Fin (Fintype.card (Arg D E)))
  (loc : A.Address → Fin p) {demand : D → ℕ} {v : E → ℕ}
  {d : DemandBits src dst demand j} {x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j}
  (X : MapEntry.Program.Workspace (A.program loc) demand v d x t w)
  (addr : BurstRAM.Word w) (sel : Selector B ↪ BurstRAM.Word w)
  (ord : (parameterData B).Entry → Fin t)

/-- Exterior cells agree with the input memory after evaluating the pure map update. -/
theorem successMemory_outside (old : PrivateScratch.Memory w) (q : BurstRAM.Word w)
    (fit : addr.val + Fintype.card (Arg D E) ≤ 2 ^ w)
    (descriptor : q.val < addr.val ∨ addr.val + Fintype.card (Arg D E) ≤ q.val)
    (other : MapCallSetup.Outside A loc X q) :
    successMemory A args loc X addr sel ord old q = old q := by
  have ptr (i : Fin (Fintype.card (Arg D E))) : q ≠ addr + (i.val : BurstRAM.Word w) := by
    simpa only [Fin.cast_val_eq_self] using apart_of_interval q fit descriptor i
  have desc : published A args loc X addr old q = old q := write_other _ _ _ _ ptr
  let first := directoryMemory A loc X (published A args loc X addr old)
  have directory : first q = old q := (write_other _ _ _ _ other.2).trans desc
  cases code : (selectorRun G (selectorTable B) (selectorCode B) v j x).1 with
  | none => simpa only [successMemory, code, Option.elim_none] using directory
  | some θ =>
    have hs := apart_of_interval q X.ordinalFit.le other.1.1
    have ht := apart_of_interval q X.labelFit.le other.1.2.1
    simp only [successMemory, code, Option.elim_some, MapEntry.Program.successMemory]
    rw [PrivateLabels.accumulate_outside _ _ _ q other.1.2.2, write_other _ _ _ _ ht,
      write_other _ _ _ _ hs]
    exact directory

/-- Project the same exterior identity through the scratch boundary. -/
theorem upper_outside (endAddr : ℕ) (saved : DFS.Scratch w endAddr) (q : BurstRAM.Word w)
    (fit : addr.val + Fintype.card (Arg D E) ≤ 2 ^ w)
    (descriptor : q.val < addr.val ∨ addr.val + Fintype.card (Arg D E) ≤ q.val)
    (other : MapCallSetup.Outside A loc X q) :
    NodeArguments.rawScratch (upper A args loc X addr sel ord endAddr saved) q =
      NodeArguments.rawScratch saved q := by
  by_cases live : endAddr ≤ q.val
  · simp only [NodeArguments.rawScratch, dite_eq_left live, upper, DFS.scratch]
    exact (successMemory_outside A args loc X addr sel ord _ q fit descriptor other).trans
      (dite_eq_left live)
  · simp only [NodeArguments.rawScratch, dite_eq_right live]

end PairSimulation.MapScratch

end VPVNP
end Computability
end OAI
