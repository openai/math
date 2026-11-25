import OAI.Computability.NearSquareRoot.PhysicalWalshGrid

/-! # The four normalized-plan leaves on encoded fixed-point rows

Mix and scale run the concrete guarded arithmetic commands. The two address
operations are supplied by the routing and recursive entry points. Each guard
is checked on the rows reaching that point in the program.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshGrid

open IntegerMultiplication Code KernelPass PhysicalWalsh

variable {a : ℕ} {U X F : Type} (L : KernelScaleBank.Layout a U F) (w : U → ℕ)

abbrev Row (u : U) := (layout L w).Row u

variable (xor : Fin (a+1) × Fin (a+1) → ∀ u, Row L w u → Row L w u)
  (child : Fin (a+1) → ∀ u, Row L w u → Row L w u)

def ops : Ops (a+1) (layout L w) where
  mix := mix L w
  xor := xor
  scale := fun _ test table => scale L w test table
  child := child

variable (xorReady : Fin (a+1) × Fin (a+1) → ∀ u, Row L w u → Prop)
  (childReady : Fin (a+1) → ∀ u, Row L w u → Prop)

def guards : Guards (a+1) (layout L w)
  | _, _, .mix c, u, x => mixFits L w c u x
  | _, _, .scale _ test table, u, x => scaleFits L w test table u (x 0)
  | _, _, .xor g, u, x => xorReady g u (x 0)
  | _, _, .child axis, u, x => childReady axis u (x 0)
  | _, _, _, _, _ => True

/-- Given the two address commands, this discharges every physical leaf of the
rounded-plan compiler, retaining the exact child-recursion count. -/
theorem gridLeaves {m : Meter U} (hb : ∀ u, budget L w u ≤ m.arena u) (u : X → U)
    (xrun : ∀ g (x : ∀ t, Rows (layout L w) (u t) 1), (∀ t, xorReady g (u t) (x t 0)) →
      OpenRun m 0 u (fun t => send (packet (layout L w) (u t) (x t)))
        (fun t => send (packet (layout L w) (u t) (fun _ : Fin 1 => xor g (u t) (x t 0)))))
    (crun : ∀ axis (x : ∀ t, Rows (layout L w) (u t) 1), (∀ t, childReady axis (u t) (x t 0)) →
      OpenRun m 1 u (fun t => send (packet (layout L w) (u t) (x t)))
        (fun t => send (packet (layout L w) (u t) (fun _ : Fin 1 => child axis (u t) (x t 0))))) :
    LeafRuns m (ops L w xor child) (guards L w xorReady childReady) X u := by
  intro i o p leaf x ready
  cases p with
  | mix c => exact mix_open L w hb c u x ready
  | xor g => exact xrun g x ready
  | child axis => exact crun axis x ready
  | scale q test table => exact scale_open L w hb test table u x ready
  | seq p q => cases leaf
  | parallel p q => cases leaf

end PhysicalWalshGrid

end NearSquareRoot
end Computability
end OAI
