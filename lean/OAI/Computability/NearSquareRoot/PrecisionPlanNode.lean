import OAI.Computability.NearSquareRoot.PrecisionPlan
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeGuard
import OAI.Computability.NearSquareRoot.PhysicalWalshGridMixNorm
import OAI.Computability.NearSquareRoot.KernelScaleNorm

/-! # The ideal row operations corresponding to the recursive evaluator

Each row is a physical ordinal function. Only its finite initial range belongs
to a packet. The numerical norm below reads exactly that range.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace PhysicalWalshNode

open IntegerMultiplication Code KernelPass PhysicalWalsh PhysicalWalshGrid

abbrev IdealRow := ℕ → ℂ

def atWidth (n : ℕ) (y : IdealRow) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun j => y j.val)

def meaningRow (p : ℕ) {s : Shape} (x : Data s) : IdealRow := fun n => Grid.meaning p s.w (x n)

def laneCount (a W : ℕ) (s : Shape) := groups W s * inner (a+1) s

/-- The physical storage enumerates every finite ordinal of a lane exactly once. -/
theorem coords_rows {a W : ℕ} (s : Shape) (hl : 0 < s.level) :
    (coords a W).rows s = List.range (laneCount a W s) := by
  have he : (a+1)*(2*((a+1)^(s.level-1))) = grow (a+1) s.level := by
    rw [grow,Nat.mul_left_comm,← pow_succ',Nat.sub_add_cancel hl]
  change List.range (groups W s * (2^_ * s.suff)) = _
  rw [he]
  rfl

def idealLayout : Layout Shape Unit Unit where
  Row := fun _ => IdealRow
  header := fun _ => ()
  store := fun _ _ => ()

def idealOps (a W : ℕ) (child : Fin (a+1) → Shape → IdealRow → IdealRow) : Ops (a+1) idealLayout where
  mix c _ x b n := ∑ j, (value (c b j) : ℂ) * x j n
  xor g s y := y ∘ xorIndex a g s
  scale _ test table s y n :=
    (value (table (KernelScaleBank.signature (coords a W) test s n)) : ℂ) * y n
  child := child

def idealLane (A W : ℕ) (s : Shape) (y : IdealRow) (b : Fin W) (n : ℕ) : ℂ :=
  y ((n / inner A s * W + b.val) * inner A s + n % inner A s)

def idealUnlane {W : ℕ} (A : ℕ) (hW : 0 < W) (s : Shape) (y : Fin W → IdealRow) (n : ℕ) : ℂ :=
  y ⟨n / inner A s % W, Nat.mod_lt _ hW⟩ (n / inner A s / W * inner A s + n % inner A s)

def laneSize (a W : ℕ) (s : Shape) (y : IdealRow) : ℝ := ‖atWidth (laneCount a W s) y‖

def laneGap (a W p : ℕ) (s : Shape) (x : Data s) (y : IdealRow) : ℝ :=
  ‖atWidth (laneCount a W s) (meaningRow p x) - atWidth (laneCount a W s) y‖

theorem atWidth_idealMix (a W : ℕ) (s : Shape) {i o}
    (child : Fin (a+1) → Shape → IdealRow → IdealRow)
    (c : Fin o → Fin i → Coefficient) (x : Rows idealLayout s i) (b : Fin o) :
    atWidth (laneCount a W s) ((idealOps a W child).mix c s x b) =
      idealMixRow c (fun j => atWidth (laneCount a W s) (x j)) b := by
  ext t
  simp [idealOps,atWidth,idealMixRow,smul_eq_mul]

theorem atWidth_idealScale (a W : ℕ) (s : Shape) {q}
    (child : Fin (a+1) → Shape → IdealRow → IdealRow)
    (test : Column (a+1) → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → Coefficient)
    (x : IdealRow) :
    atWidth (laneCount a W s) ((idealOps a W child).scale q test table s x) =
      KernelScaleNorm.action table (fun j => KernelScaleBank.signature (coords a W) test s j.val)
        (atWidth (laneCount a W s) x) := rfl

end PhysicalWalshNode

end

end NearSquareRoot
end Computability
end OAI
