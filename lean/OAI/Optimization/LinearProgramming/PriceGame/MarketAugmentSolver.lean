import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentRoutes
import OAI.Optimization.LinearProgramming.PriceGame.MarketOptimumDual

/-! Executable bit-scaling integral transshipment on the expert–good–dummy network. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment

open Quiver OAI.Optimization.LinearProgramming.PriceGame.Market.Graph

/-- The implementation stores every row and both potential vectors in dense arrays. -/
structure State (m g : ℕ) where
  mass : Vector (Vector ℕ (g + 1)) m
  expert : Vector ℚ m
  option : Vector ℚ (g + 1)

variable {m g : ℕ}

namespace State

def flow (s : State m g) (i : Fin m) (o : Option (Fin g)) : ℕ :=
  s.mass[i.val][((finSuccEquiv g).symm o).val]

def pe (s : State m g) (i : Fin m) : ℚ := s.expert[i.val]

def po (s : State m g) (o : Option (Fin g)) : ℚ := s.option[((finSuccEquiv g).symm o).val]

def pack (f : Fin m → Option (Fin g) → ℕ) (p : Fin m → ℚ) (q : Option (Fin g) → ℚ) : State m g :=
  ⟨Vector.ofFn fun e => Vector.ofFn fun o => f e (finSuccEquiv g o),
    Vector.ofFn p, Vector.ofFn fun o => q (finSuccEquiv g o)⟩

@[simp] theorem flow_pack (f : Fin m → Option (Fin g) → ℕ) (p : Fin m → ℚ)
    (q : Option (Fin g) → ℚ) : (pack f p q).flow = f := by
  funext e o
  simp [pack, flow]

@[simp] theorem pe_pack (f : Fin m → Option (Fin g) → ℕ) (p : Fin m → ℚ)
    (q : Option (Fin g) → ℚ) : (pack f p q).pe = p := by
  funext e
  simp [pack, pe]

@[simp] theorem po_pack (f : Fin m → Option (Fin g) → ℕ) (p : Fin m → ℚ)
    (q : Option (Fin g) → ℚ) : (pack f p q).po = q := by
  funext o
  simp [pack, po]

end State

/-- Finite indexed expert markets carry a decidable good list and rational arc weights. -/
structure Input (m g : ℕ) where
  positive : Fin m → Bool
  available : Fin m → Fin g → Bool
  intercept : Fin m → Fin g → ℚ

namespace Input

variable (I : Input m g)

def accepts (e : Fin m) (i : Fin g) : Prop := I.available e i = true

instance (e : Fin m) (i : Fin g) : Decidable (I.accepts e i) :=
  inferInstanceAs (Decidable (I.available e i = true))

def network (s : State m g) : Network (Fin m) (Fin g) :=
  ⟨I.positive, I.accepts, I.intercept, s.flow⟩

def decideAcceptance (s : State m g) (e : Fin m) (j : Fin g) :
    Decidable ((I.network s).accepts e j) := inferInstanceAs (Decidable (I.accepts e j))

def initial : State m g :=
  let M := OptimumDual.costBound I.intercept
  State.pack (fun _ _ => 0) (fun e => side I.positive e * M) (fun _ => 0)

def double (s : State m g) : State m g := State.pack (fun e o => 2 * s.flow e o) s.pe s.po

/-- Use the selected simple path to update the integer flow and retain all the Bellman potentials. -/
def unit (s : State m g) (i : Fin m) : State m g :=
  let n := I.network s
  let z := route n (I.decideAcceptance s) (combine n s.pe s.po) i
  State.pack (applyPath n z.path) (fun e => z.dual (.expert e)) (fun o => z.dual (.opt o))

structure Invariant (s : State m g) (qty : Fin m → ℕ) : Prop where
  feasible : Optimum.Feasible I.positive qty I.accepts s.flow
  residual : ResidualPotentials I.positive I.accepts I.intercept s.flow s.pe s.po

theorem initial_spec : I.Invariant I.initial (fun _ => 0) := by
  constructor <;> simp only [initial, State.flow_pack, State.pe_pack, State.po_pack]
  · exact OptimumDual.zero_feasible _ _
  · exact OptimumDual.zero_residual _ _ _

theorem double_spec {s : State m g} {qty : Fin m → ℕ} (hs : I.Invariant s qty) :
    I.Invariant (double s) (fun e => 2 * qty e) := by
  constructor <;> simp only [double, State.flow_pack, State.pe_pack, State.po_pack]
  · exact OptimumDual.double_feasible hs.feasible
  · exact OptimumDual.double_residual hs.residual

theorem unit_spec {s : State m g} {qty : Fin m → ℕ} (hs : I.Invariant s qty) (i : Fin m) :
    I.Invariant (I.unit s i) (raiseAt qty i) := by
  let n := I.network s
  let dec := I.decideAcceptance s
  let π := combine n s.pe s.po
  let z := route n dec π i
  have hpot : ResidualPotentials n.pos n.accepts n.c n.f s.pe s.po := hs.residual
  have hf : Optimum.Feasible n.pos qty n.accepts n.f := hs.feasible
  obtain ⟨ended, simple, bounds, tight⟩ := route_spec n dec π (residual_arc n hpot) i
  change z.last = finish n i at ended
  change z.path.vertices.Nodup at simple
  have fnew : Optimum.Feasible n.pos (raiseAt qty i) n.accepts (applyPath n z.path) := by
    have step {u : Vertex n} (p : Path (start n i) u) (endpt : u = finish n i) (hp : p.vertices.Nodup) :
        Optimum.Feasible n.pos (raiseAt qty i) n.accepts (applyPath n p) := by
      subst u
      exact feasible_applyPath n hf i p hp
    exact step z.path ended simple
  have eqLast : z.path.addWeight n.weight = z.dual (start n i) - z.dual z.last := by
    rw [congrArg z.dual ended]; exact tight
  have dnew := residual_applyPath n hf z.dual bounds z.path simple eqLast
  constructor
  · simpa only [unit, State.flow_pack, z, π, dec, n, network] using fnew
  · simpa only [unit, State.flow_pack, State.pe_pack, State.po_pack, z, π, dec, n, network] using dnew

/-- Most-significant-first bit scaling, with one Bellman pass per nonzero expert digit. -/
def solveWithWidth (k : ℕ) (qty : Fin m → ℕ) : State m g :=
  (schedule k qty).foldl (operation double I.unit) I.initial

theorem solveWithWidth_spec (k : ℕ) (qty : Fin m → ℕ) (hb : ∀ i, qty i < 2 ^ k) :
    I.Invariant (I.solveWithWidth k qty) qty :=
  run_schedule double I.unit I.Invariant I.initial I.initial_spec
    (fun _ _ h => I.double_spec h) (fun _ _ h => I.unit_spec h) k qty hb

def bits (qty : Fin m → ℕ) : ℕ := Finset.univ.sup fun e => (qty e).size

def solve (qty : Fin m → ℕ) : State m g := I.solveWithWidth (bits qty) qty

theorem solve_spec (qty : Fin m → ℕ) : I.Invariant (I.solve qty) qty := by
  apply I.solveWithWidth_spec
  intro e
  apply Nat.size_le.mp
  exact Finset.le_sup (s := Finset.univ) (f := fun j : Fin m => (qty j).size) (Finset.mem_univ e)

theorem solve_optimal (qty : Fin m → ℕ) (f : Fin m → Option (Fin g) → ℕ)
    (hf : Optimum.Feasible I.positive qty I.accepts f) :
    Optimum.value I.intercept f ≤ Optimum.value I.intercept (I.solve qty).flow :=
  OptimumDual.optimal_of_residual (I.solve_spec qty).feasible (I.solve_spec qty).residual f hf

end Input
end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
