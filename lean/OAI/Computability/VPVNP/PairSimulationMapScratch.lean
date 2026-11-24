import OAI.Computability.VPVNP.PairSimulationMapCallRun
import OAI.Computability.VPVNP.PairSimulationDFSHooks

/-!
# Exact upper scratch of a successful grouped-map visit

The descriptor publisher writes its argument words, the initializer writes
the pointer directory, and the evaluator writes the decoded selector ordinals
and parameter labels before incrementing the histogram. At an individual
address this result depends only on the incoming contents of that address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapScratch

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifEntry MapCallSetup MapEntryTable
open scoped Fin.CommRing

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

/-- The descriptor's address and field order come from the fixed argument writer. -/
noncomputable def published (old : PrivateScratch.Memory w) : PrivateScratch.Memory w :=
  PrivateScratch.write addr (fun i ↦ values A loc X (args.symm i)) old

/-- Complete private memory update used when the selector and total-width checks succeed. -/
noncomputable def successMemory (old : PrivateScratch.Memory w) : PrivateScratch.Memory w :=
  let init := directoryMemory A loc X (published A args loc X addr old)
  (selectorRun G (selectorTable B) (selectorCode B) v j x).1.elim init
    (fun θ ↦ (A.program loc).successMemory X sel ord θ init)

/-- The semantic entry succeeds only at a decoded sequence with its full width vector. -/
theorem sequence_of_success
    (good : (MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
      (selectorTable B) (selectorCode B) v j d x).1.isSome = true) :
    ∃ θ, (selectorRun G (selectorTable B) (selectorCode B) v j x).1 = some θ ∧
      ∀ e, v e = totalWidth (basePayload B) θ e := by
  rw [MapFinish.entry_value] at good
  cases hs : (selectorRun G (selectorTable B) (selectorCode B) v j x).1 with
  | none => simp [hs] at good
  | some θ =>
    rw [hs, Option.bind_some] at good
    split at good
    · exact ⟨θ, rfl, by assumption⟩
    · simp at good

/-- On a successful native visit every private address has the prescribed value. -/
theorem exact_memory {old new : PrivateScratch.Memory w}
    (good : (MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
      (selectorTable B) (selectorCode B) v j d x).1.isSome = true)
    (post : Success A loc X sel ord (published A args loc X addr old) new) :
    new = successMemory A args loc X addr sel ord old := by
  obtain ⟨θ, tags, valid⟩ := sequence_of_success good
  simpa only [successMemory, tags, Option.elim_some] using post θ tags valid

theorem successMemory_congr_at {old old' : PrivateScratch.Memory w} (q : BurstRAM.Word w)
    (h : old q = old' q) :
    successMemory A args loc X addr sel ord old q =
      successMemory A args loc X addr sel ord old' q := by
  have init : directoryMemory A loc X (published A args loc X addr old) q =
      directoryMemory A loc X (published A args loc X addr old') q :=
    PrivateScratch.write_congr_at _ _ q (PrivateScratch.write_congr_at _ _ q h)
  cases hs : (selectorRun G (selectorTable B) (selectorCode B) v j x).1 with
  | none => simpa only [successMemory, hs, Option.elim_none] using init
  | some θ => simpa only [successMemory, hs, Option.elim_some] using
      (A.program loc).successMemory_congr_at X sel ord θ q init

/-- The canonical outgoing upper scratch is defined on the upper scratch alone. -/
noncomputable def upper (endAddr : ℕ) (saved : DFS.Scratch w endAddr) : DFS.Scratch w endAddr :=
  DFS.scratch endAddr (successMemory A args loc X addr sel ord
    (fun a ↦ if h : endAddr ≤ a.val then saved ⟨a, h⟩ else 0))

theorem exact_upper (endAddr : ℕ) (saved : DFS.Scratch w endAddr)
    {old new : PrivateScratch.Memory w}
    (incoming : DFS.scratch endAddr old = saved)
    (good : (MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
      (selectorTable B) (selectorCode B) v j d x).1.isSome = true)
    (post : Success A loc X sel ord (published A args loc X addr old) new) :
    DFS.scratch endAddr new = upper A args loc X addr sel ord endAddr saved := by
  rw [exact_memory A args loc X addr sel ord good post]
  funext a
  apply successMemory_congr_at
  rw [dite_eq_left a.property]
  exact congrFun incoming a

/-- Two successful visits with the same incoming upper scratch agree at every upper word. -/
theorem success_upper_eq (endAddr : ℕ) {old old' new new' : PrivateScratch.Memory w}
    (incoming : DFS.scratch endAddr old = DFS.scratch endAddr old')
    (good : (MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
      (selectorTable B) (selectorCode B) v j d x).1.isSome = true)
    (post : Success A loc X sel ord (published A args loc X addr old) new)
    (post' : Success A loc X sel ord (published A args loc X addr old') new') :
    DFS.scratch endAddr new = DFS.scratch endAddr new' := by
  exact (exact_upper A args loc X addr sel ord endAddr _ incoming good post).trans
    (exact_upper A args loc X addr sel ord endAddr _ rfl good post').symm

end PairSimulation.MapScratch

end VPVNP
end Computability
end OAI
