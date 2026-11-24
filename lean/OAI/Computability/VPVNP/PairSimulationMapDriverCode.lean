import OAI.Computability.VPVNP.PairSimulationMapDriver

/-!
# Relocatable instruction text for the streamed row driver

The successor of a failed ordinal test is fixed by the selector's position
in the table. The row entry points, full-width check, and bad exit can all
belong to a surrounding map program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapDriver.Program

open BurstRAM BurstRAM.PrivateRAM

variable {S : Type*} {w p r k : ℕ} (P : MapDriver.Program S p r k)

/-- Labels of the driver's five outer instructions and its two dispatch instructions per
selector. -/
abbrev Location (S : Type*) := Fin 5 ⊕ (S × Bool)

/-- Select an outer label, public-word load, or equality jump. -/
def address : Location S → Fin p := Sum.elim P.pc (fun x ↦ P.comparePC x.1 x.2)

/-- The residual fixed table after comparing the named selector. -/
noncomputable def remaining (s : S) : List S → List S
  | [] => []
  | x :: xs => by
    classical
    exact if s = x then xs else remaining s xs

/-- Bounded targets are already relocated into the enclosing instruction table. -/
noncomputable def code : Location S → Instr 1 p r k
  | .inl i => P.instruction i
  | .inr (s, false) => .publicWord (P.reg 5) (P.port s) (P.comparePC s true)
  | .inr (s, true) =>
    .jumpEq (P.reg 4) (P.reg 5) (P.rowPC s) (P.first (remaining s P.selectors))

private theorem dispatch_of_code {M : Machine w p r k}
    (rows : ∀ loc, M.code (P.address loc) = (P.code loc).resize w)
    (xs : List S) (hn : xs.Nodup)
    (tail : ∀ s ∈ xs, remaining s P.selectors = remaining s xs) : P.dispatch M xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    have hd := List.nodup_cons.mp hn
    refine ⟨rows (.inr (x, false)), ?_, ih hd.2 ?_⟩
    · have hx := tail x (List.mem_cons_self ..)
      have he : remaining x P.selectors = xs := hx.trans (by simp [remaining])
      change M.code (P.address (.inr (x, true))) = _
      rw [rows]
      change Instr.jumpEq _ _ _ (P.first (remaining x P.selectors)) = _
      rw [he]
    · intro s hs
      have ne : s ≠ x := fun he ↦ hd.1 (he ▸ hs)
      exact (tail s (List.mem_cons_of_mem _ hs)).trans (by simp [remaining, ne])

/-- Installing each emitted opcode links the driver, including the dispatch
of the final selector and the empty-table case. -/
theorem linked_of_code {M : Machine w p r k} (hn : P.selectors.Nodup)
    (rows : ∀ loc, M.code (P.address loc) = (P.code loc).resize w) : P.Linked M := by
  constructor
  · intro i
    exact (rows (.inl i)).trans (P.resize_instruction i)
  · exact dispatch_of_code P rows _ hn fun _ _ ↦ rfl

end PairSimulation.MapDriver.Program

end VPVNP
end Computability
end OAI
