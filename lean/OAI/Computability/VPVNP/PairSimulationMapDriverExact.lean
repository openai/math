import OAI.Computability.VPVNP.PairSimulationMapRowLoop

/-!
# Exact ticks of the successful row driver

The number of comparisons for a copy is the position of its selector in the
fixed dispatch table. The selected row supplies its own input-dependent tick
count. The same path stores every label and carries the offset and register
invariants to the width check.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapDriver.Program

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

open private MapDriver.val_word MapDriver.Program.step_at from
  OAI.Computability.VPVNP.PairSimulationMapDriver
open private MapDriver.Program.stable_saved from OAI.Computability.VPVNP.PairSimulationMapDriverFrame

variable {S : Type*} {w p r k u : ℕ} (P : MapDriver.Program S p r k)
  (θ : Fin u → S) (rowSteps : Fin u → ℕ)

/-- Test, selector load, dispatch, selected row, label store and two increments. -/
noncomputable def visitSteps (i : Fin u) : ℕ :=
  5 + dispatchSteps P.selectors (θ i) + rowSteps i

/-- The final exit test follows the last copy. -/
noncomputable def exactSteps : ℕ := (∑ i, P.visitSteps θ rowSteps i) + 1

variable {P} {M : Machine w p r k}
  (link : P.Linked M) (inj : Function.Injective (M.publicData ∘ P.port))
  (member : ∀ i, θ i ∈ P.selectors) (labelWord : Fin u → Word w)
  (inv : ℕ → Config w p r → Prop) (src dest cap : ℕ) (stable : P.Stable inv dest u)

include link inj member stable in
private theorem visits_exact
    (row : P.RowRunsWith M θ labelWord inv cap (fun i n ↦ n = rowSteps i))
    (hs : src + u < 2 ^ w) (hd : dest + u < 2 ^ w) (sep : src + u ≤ dest ∨ dest + u ≤ src)
    (c : Config w p r) (ready : P.Ready M θ labelWord src dest 0 c) (h0 : inv 0 c)
    (n : ℕ) (hn : n ≤ u) :
    let ticks := MapRowLoop.prefixWidth (P.visitSteps θ rowSteps) n
    ∃ d, ticks ≤ P.visitCap cap * n ∧ Prefix M c (List.replicate ticks .tick) d ∧
      P.Ready M θ labelWord src dest n d ∧ inv n d ∧
      (∀ a : Word w, a.val < dest ∨ dest + n ≤ a.val → d.privateMem a = c.privateMem a) ∧
      d.persistent = c.persistent := by
  dsimp only
  induction n with
  | zero =>
    rw [MapRowLoop.prefix_zero]
    exact ⟨c, by simp, .nil _, ready, h0, fun _ _ ↦ rfl, rfl⟩
  | succ n ih =>
    obtain ⟨m, bound, pre, hr, hi, mem, per⟩ := ih (by omega)
    let i : Fin u := ⟨n, hn⟩
    obtain ⟨s, d, hbound, ⟨ticks, he, h⟩, tail, hr', hi', hm, hp⟩ :=
      visitWith link inj θ member labelWord inv src dest cap stable _ row hs hd sep i m hr hi
    have eq : s = P.visitSteps θ rowSteps i := h.trans (congrArg _ he)
    rw [eq] at hbound tail
    rw [show n + 1 = i.val + 1 from rfl, MapRowLoop.prefix_next, Nat.mul_succ]
    refine ⟨d, Nat.add_le_add bound hbound, ?_, hr', hi', ?_, hp.trans per⟩
    · rw [List.replicate_add]
      exact pre.append tail
    · intro a ha
      change a.val < dest ∨ dest + (n + 1) ≤ a.val at ha
      apply (hm a ?_).trans (mem a (by omega))
      intro same
      have hv := congrArg Fin.val same
      rw [MapDriver.val_word (by change dest + n < 2 ^ w; omega)] at hv
      change a.val = dest + n at hv
      omega

include link inj member stable in
/-- The complete exact path preserves the exterior registers, delivers each label at
its private array position, and leaves all other private cells unchanged. -/
theorem native_exact_framed (save : Fin r → Prop) (keep : P.OutsideWrites save)
    (rows : P.FramedRowsWith θ rowSteps M labelWord inv cap save)
    (hs : src + u < 2 ^ w) (hd : dest + u < 2 ^ w) (sep : src + u ≤ dest ∨ dest + u ≤ src)
    (c : Config w p r) (ready : P.Ready M θ labelWord src dest 0 c) (h0 : inv 0 c) :
    ∃ d, P.exactSteps θ rowSteps ≤ P.visitCap cap * u + 1 ∧
      Prefix M c (List.replicate (P.exactSteps θ rowSteps) .tick) d ∧
      d.pc = P.checkWidths ∧ inv u d ∧ Saved save c d ∧
      (∀ i : Fin u, d.privateMem ((dest + i.val : ℕ) : Word w) = labelWord i) ∧
      (∀ a : Word w, a.val < dest ∨ dest + u ≤ a.val → d.privateMem a = c.privateMem a) ∧
      d.persistent = c.persistent := by
  let framed n d := inv n d ∧ Saved save c d
  have stable' : P.Stable framed dest u := MapDriver.Program.stable_saved P stable keep c
  obtain ⟨m, bound, pre, hr, hi, hm, hp⟩ :=
    visits_exact θ rowSteps link inj member labelWord framed src dest cap stable'
      (rows c) hs hd sep c ready ⟨h0, fun _ _ ↦ rfl⟩ u le_rfl
  rw [MapRowLoop.prefix_last] at bound pre
  let d := {m with pc := P.checkWidths}
  have eq : m.reg (P.reg 0) = m.reg (P.reg 1) := hr.source.trans hr.stop.symm
  have stop : M.program.step m = .localStep d := by
    rw [MapDriver.Program.step_at link 0 hr.pc]
    simp [instruction, Instr.run, eq, d]
  have final := stable' u m d hi (fun _ _ _ _ _ ↦ rfl) (fun _ _ ↦ rfl) rfl
  refine ⟨d, Nat.add_le_add_right bound _, ?_, rfl, final.1, final.2,
    fun i ↦ hr.labels i i.isLt, hm, hp⟩
  rw [exactSteps, List.replicate_add]
  exact pre.append (.tick stop (.nil _))

end PairSimulation.MapDriver.Program

end VPVNP
end Computability
end OAI
