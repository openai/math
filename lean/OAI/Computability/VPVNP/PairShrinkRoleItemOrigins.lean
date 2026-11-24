import OAI.Computability.VPVNP.PairSimulationResidentMapLoopExact

/-!
# Resident map invariants with an arbitrary prepared origin

The packet and operand proofs can be established for a fixed map-loop entry
configuration. Any later configuration may retain that origin as a witness.
The same selected actions still execute on its current scratch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentMapLoop.Exact

open BurstRAM BurstRAM.PrivateRAM

variable {w n p r k : ℕ} {Ω : Type*} {P : Program p r} {M : Machine w p r k} {m : Memory w}
  {dfs : Fin 9 ↪ Fin r} {inv : Ω → Word w → Config w p r → Prop}
  {eligible : Ω → Word w → Prop}

/-- Origin-dependent data that can be retained through the whole row. -/
def OriginInvariant (eligible : Ω → Word w → Prop)
    (inv : Ω → Word w → Config w p r → Prop) (node : Word w) (c : Config w p r) : Prop :=
  ∃ origin, eligible origin node ∧ inv origin node c

theorem OriginInvariant.stable (each : ∀ origin node, P.Stable (inv origin node)) (node : Word w) :
    P.Stable (OriginInvariant eligible inv node) := by
  rintro c d ⟨origin, good, live⟩ regs mem persistent
  exact ⟨origin, good, each origin node c d live regs mem persistent⟩

/-- The actions and their guard addresses are identical across origins. The
actual native item takes the origin belonging to the input configuration. -/
theorem Items.existsInvariant {src : ℕ} {actions : List (Action w n)}
    (quiet : ∀ a ∈ actions, NoChoices a)
    (each : ∀ origin, Items P M m dfs (inv origin) src actions) :
    Items P M m dfs (OriginInvariant eligible inv) src actions := by
  induction actions generalizing src with
  | nil => trivial
  | cons a rest ih =>
    refine ⟨⟨quiet a List.mem_cons_self, ?_, ?_⟩,
      ih (fun b hb => quiet b (List.mem_cons_of_mem _ hb)) (fun o => (each o).2)⟩
    · rintro node c es out atItem cursor ⟨o, good, live⟩ hit
      obtain ⟨d, done, keep, frame⟩ := (each o).1.success node c es out atItem cursor live hit
      exact ⟨d, done, ⟨o, good, keep⟩, frame⟩
    · rintro node c atItem cursor ⟨o, _, live⟩ bad
      exact (each o).1.reject node c atItem cursor live bad

end PairSimulation.ResidentMapLoop.Exact

end VPVNP
end Computability
end OAI
