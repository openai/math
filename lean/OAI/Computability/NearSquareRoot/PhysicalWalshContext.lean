import OAI.Computability.NearSquareRoot.PhysicalWalshGridLeaves

/-! # Retaining the recursion descriptor across the fixed-grid plan

The header on the tape consists of the arithmetic shape rulers and the current
node's descriptor. An arithmetic instruction consumes the same rulers as before
and restores the descriptor. Address instructions receive the entire header so
that a child entry point can construct its new shape from physical data.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshContext

open IntegerMultiplication Code KernelPass Space PhysicalWalsh
open PhysicalWalshGrid (Header Row mix scale)

variable {a i o : ℕ} {U F X D : Type} (L : KernelScaleBank.Layout a U F) (w : U → ℕ) (desc : U → D)

/-- The machine carries a compact description of its current recursive node. -/
def routeLayout : Layout U (Header × D) (List Dusk.Pair) where
  Row := Row L w
  header u := (PhysicalWalshGrid.header L w u, desc u)
  store := (PhysicalWalshGrid.layout L w).store

variable (xor : Fin (a+1) × Fin (a+1) → ∀ u, Row L w u → Row L w u)
  (child : Fin (a+1) → ∀ u, Row L w u → Row L w u)
  (xorReady : Fin (a+1) × Fin (a+1) → ∀ u, Row L w u → Prop)
  (childReady : Fin (a+1) → ∀ u, Row L w u → Prop)

def routeOps : Ops (a+1) (routeLayout L w desc) where
  mix := mix L w
  xor := xor
  scale := fun _ test table => scale L w test table
  child := child

def routeGuards : Guards (a+1) (routeLayout L w desc) := PhysicalWalshGrid.guards L w xorReady childReady

/-- Both headers implement identical operations on the mathematical records. -/
theorem routeApply_eq (p : Plan (a+1) i o) (u : U) (x : Rows (PhysicalWalshGrid.layout L w) u i) :
    (routeOps L w desc xor child).applyPlan p u x = (PhysicalWalshGrid.ops L w xor child).applyPlan p u x := by
  induction p with
  | mix _ | xor _ | scale _ _ _ | child _ => rfl
  | seq p q hp hq => simp only [Ops.applyPlan, hq, hp]; rfl
  | parallel p q hp hq => simp only [Ops.applyPlan, hp, hq]; rfl

theorem routeReady_iff (p : Plan (a+1) i o) (u : U) (x : Rows (PhysicalWalshGrid.layout L w) u i) :
    Ready (routeOps L w desc xor child) (routeGuards L w desc xorReady childReady) p u x ↔
      Ready (PhysicalWalshGrid.ops L w xor child) (PhysicalWalshGrid.guards L w xorReady childReady) p u x := by
  induction p with
  | mix _ | xor _ | scale _ _ _ | child _ => rfl
  | seq p q hp hq => simp only [Ready,routeApply_eq, hp,hq]
  | parallel p q hp hq => simp only [Ready,hp,hq]

variable [Codec D]

/-- The ordinary header and rows fit the grid area. The second header field is
charged once, in addition to the marker joining the two fields. -/
def routeArena (u : U) := 20*(PhysicalWalshGrid.budget L w u+1) + size (desc u) + 1

variable {m : Meter U} (hm : ∀ u, routeArena L w desc u ≤ m.arena u)
include hm

theorem fitsLayout : FitsLayout m (routeLayout L w desc) := by
  let base : Meter U := {
    scan := fun u => 20*(PhysicalWalshGrid.budget L w u+1)
    arena := fun u => 20*(PhysicalWalshGrid.budget L w u+1)
    arena_le := fun _ => le_rfl
    permit := m.permit }
  have sizes : FitsLayout base (PhysicalWalshGrid.layout L w) := PhysicalWalshGrid.fitsLayout L w (fun _ => le_rfl)
  constructor
  · intro u
    apply le_trans _ (hm u)
    have hh := sizes.header u
    change size (PhysicalWalshGrid.header L w u) ≤ 20*(PhysicalWalshGrid.budget L w u+1) at hh
    change size (PhysicalWalshGrid.header L w u, desc u) ≤ _
    rw [size_prod]
    exact Nat.add_le_add_right (Nat.add_le_add_right hh _) _
  · intro u x
    apply (sizes.row u x).trans
    apply le_trans _ (hm u)
    dsimp only [base,routeArena]; omega

/-- Supply the first field to any arithmetic leaf, keeping the complete header
on the stack. The address-dependent I/O rows can be arbitrary reached states. -/
theorem liftArithmetic (u : X → U) (x : ∀ t, Rows (routeLayout L w desc) (u t) i)
    (y : ∀ t, Rows (routeLayout L w desc) (u t) o)
    (inner : BoundedTask (PhysicalWalshGrid.budget L w ∘ u) (PhysicalWalshGrid.budget L w ∘ u)
      (fun t => send (packet (PhysicalWalshGrid.layout L w) (u t) (x t)))
      (fun t => send (packet (PhysicalWalshGrid.layout L w) (u t) (y t)))) :
    OpenRun m 0 u (fun t => send (packet (routeLayout L w desc) (u t) (x t)))
      (fun t => send (packet (routeLayout L w desc) (u t) (y t))) := by
  have bound t : PhysicalWalshGrid.budget L w (u t) ≤ m.arena (u t) := by
    apply le_trans _ (hm _)
    unfold routeArena; omega
  have shape := fitsLayout L w desc hm
  have g := PhysicalWalshGrid.retain (m.arena ∘ u) Prod.fst Easy.fst
    (fun t => (routeLayout L w desc).header (u t))
    (fun t => (packet (routeLayout L w desc) (u t) (x t)).2)
    (fun t => (packet (routeLayout L w desc) (u t) (y t)).2)
    (i+3) (o+3) (fun t => shape.packet (u t) (x t)) (fun t => shape.packet (u t) (y t))
    (inner.mono bound bound)
  exact OpenRun.closed (g.mono (fun t => m.arena_le (u t)) (fun _ => le_rfl))

variable (u : X → U)
  (xrun : ∀ g (x : ∀ t, Rows (routeLayout L w desc) (u t) 1), (∀ t, xorReady g (u t) (x t 0)) →
    OpenRun m 0 u (fun t => send (packet (routeLayout L w desc) (u t) (x t)))
      (fun t => send (packet (routeLayout L w desc) (u t) (fun _ : Fin 1 => xor g (u t) (x t 0)))))
  (crun : ∀ axis (x : ∀ t, Rows (routeLayout L w desc) (u t) 1), (∀ t, childReady axis (u t) (x t 0)) →
    OpenRun m 1 u (fun t => send (packet (routeLayout L w desc) (u t) (x t)))
      (fun t => send (packet (routeLayout L w desc) (u t) (fun _ : Fin 1 => child axis (u t) (x t 0)))))

include hm xrun crun

theorem routeLeaves :
    LeafRuns m (routeOps L w desc xor child) (routeGuards L w desc xorReady childReady) X u := by
  intro i o p leaf x ready
  cases p with
  | mix c => exact liftArithmetic L w desc hm u x _ (PhysicalWalshGrid.mix_bounded L w c u x ready)
  | scale q t c => exact liftArithmetic L w desc hm u x _ (PhysicalWalshGrid.scale_bounded L w t c u x ready)
  | xor g => exact xrun g x ready
  | child a => exact crun a x ready
  | seq _ _ => cases leaf
  | parallel _ _ => cases leaf

/-- Compile the whole program on enriched packets. Both the answer and the
numerical readiness hypothesis refer to the original grid semantics. -/
theorem runOn (p : Plan (a+1) i o) (x : ∀ t, Rows (routeLayout L w desc) (u t) i)
    (ready : ∀ t, Ready (PhysicalWalshGrid.ops L w xor child) (PhysicalWalshGrid.guards L w xorReady childReady)
      p (u t) (x t)) :
    OpenRun m p.calls u (fun t => send (packet (routeLayout L w desc) (u t) (x t)))
      (fun t => send (packet (routeLayout L w desc) (u t) ((PhysicalWalshGrid.ops L w xor child).applyPlan p (u t) (x t)))) := by
  have r := compileOn (routeOps L w desc xor child) (routeGuards L w desc xorReady childReady)
    (fitsLayout L w desc hm) u (routeLeaves L w desc xor child xorReady childReady hm u xrun crun) p x
    (fun t => (routeReady_iff L w desc xor child xorReady childReady p (u t) (x t)).mpr (ready t))
  have eq : (fun t => send (packet (routeLayout L w desc) (u t) ((routeOps L w desc xor child).applyPlan p (u t) (x t)))) =
      (fun t => send (packet (routeLayout L w desc) (u t) ((PhysicalWalshGrid.ops L w xor child).applyPlan p (u t) (x t)))) := by
    funext t
    exact congrArg (fun rows => send (packet (routeLayout L w desc) (u t) rows)) (routeApply_eq L w desc xor child p _ _)
  rw [← eq]; exact r

end PhysicalWalshContext

end NearSquareRoot
end Computability
end OAI
