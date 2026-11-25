import OAI.Computability.NearSquareRoot.InterchangeROMDriver
import OAI.Computability.NearSquareRoot.InterchangeBQuestMixedResolve
import OAI.Computability.NearSquareRoot.InterchangeProgram

/-!
# Closing a selected recursive interchange controller

The open contract refers to the literal recursive parent. Its call clock sums
each occurrence in the child ledger once. A small child may retain a whole
parent row, while a full-volume child retains only its logarithmic header.
The fixed-point theorem certifies the very command whose code is generated.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRecursion

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom
  NearSquareRoot.Space NearSquareRoot.InterchangeSpace NearSquareRoot.InterchangeROMFrame

variable {I X : Type}

/-- Closed execution of the indicated command on all parked decks. -/
def Certified (cmd : Cmd) (time space : X → ℕ) (input output : X → Tree) : Prop :=
  ∃ K : ℕ, ∀ x env deck base, DeckCap base deck →
    BoundedFits env cmd (pile 0 (input x) deck) (pile 0 (output x) deck)
      (K*(time x+1)) (base+K*(space x+1)) (K*(space x+1))

theorem Certified.task {cmd : Cmd} {t v : X → ℕ} {p q : X → Tree} (h : Certified cmd t v p q) :
    BoundedTask t v p q := ⟨cmd,h⟩

theorem Certified.on {cmd : Cmd} {t v : X → ℕ} {p q : X → Tree} (h : Certified cmd t v p q)
    (a : I → X) : Certified cmd (t ∘ a) (v ∘ a) (p ∘ a) (q ∘ a) := by
  obtain ⟨K,run⟩ := h
  exact ⟨K,fun i => run (a i)⟩

/-- The program counter used by recursive calls is the exact open parent.
Selecting the executed command per row permits an already decoded leaf
branch and internal branch to share the same contract. -/
def Sharp (parent : Cmd) (selected : I → Cmd) (job : Job X) (small full : I → List X)
    (V : I → ℕ) (C H : ℕ) (input output : I → Tree) : Prop :=
  ∀ (i : I) (env : Env) (time data depth : X → ℕ),
    (∀ y ∈ small i ++ full i, ∀ deck base, DeckCap base deck →
      BoundedFits (parent::env) parent (pile 0 (job.issue y) deck) (pile 0 (job.reply y) deck)
        (time y) (base + data y) (depth y)) →
    ∀ deck base, DeckCap base deck →
      BoundedFits (parent::env) (selected i) (pile 0 (input i) deck) (pile 0 (output i) deck)
        (C*V i + ((small i ++ full i).map time).sum)
        (base + max (C*V i + childPeak data (small i))
          (H*(Nat.log 2 (V i)+1) + childPeak data (full i)))
        (max (C*V i + childPeak depth (small i))
          (H*(Nat.log 2 (V i)+1) + childPeak depth (full i)))

/-- The prelude returns before the selected stage begins. Increasing the
local volume charge does not increase the header parked on full-volume calls. -/
theorem Sharp.node {prelude stage : Cmd} {b n : ℕ} {job : Job X} {small full : I → List X}
    {V frontTime : I → ℕ} {C H A : ℕ} {input middle output : I → Tree} {select : I → Bool}
    (chosen : Sharp (node prelude stage b n) (fun i => bif select i then stage else .pass) job
      small full V C H middle output)
    (front : ∀ i env deck, Fits (node prelude stage b n::env) prelude
      (pile 0 (.fork (literal b n) (input i)) deck)
      (pile 0 (.fork (.atom (select i)) (middle i)) deck) (frontTime i))
    (localBound : ∀ i, 5*(literal b n).count + frontTime i + (input i).count + (middle i).count + 20 ≤ A*V i) :
    Sharp (node prelude stage b n) (fun _ => node prelude stage b n) job small full V (A+C) H input output := by
  intro i env t d r invoke deck base cap
  have step := node_run b n prelude stage _ deck base cap (input i) (middle i) (output i)
    (select i) _ _ _ _ (front i env deck) (chosen i env t d r invoke deck base cap)
  have paid := localBound i
  apply step.mono
  · simp only [Nat.add_mul]; omega
  · simp only [Nat.add_mul]; omega
  · simp only [Nat.add_mul]; omega

/-- An externally supplied fare can include other polynomial factors. The
same fixed tied command has a single volume coefficient on both its stacks. -/
theorem resolve_controller {job : Job X} {small full : X → List X} {V : X → ℕ}
    {C H : ℕ} (b n : ℕ) (prelude stage : Cmd)
    (step : Sharp (node prelude stage b n) (fun _ => node prelude stage b n) job small full V C H job.issue job.reply)
    (height : X → ℕ) (fare : X → ℝ) (ε : ℝ) (hε : 0 < ε)
    (power : ∀ x, 2^height x ≤ V x) (localCost : ∀ x, (V x : ℝ) ≤ fare x)
    (slack : ∀ x, ((small x ++ full x).map fare).sum + ε*fare x ≤ fare x)
    (order : ∀ x y, y ∈ small x ++ full x → height y < height x)
    (shrink : ∀ x y, y ∈ small x → 3*V y ≤ 2*V x)
    (contract : ∀ x y, y ∈ full x → V y ≤ V x) :
    Certified (controller prelude stage b n) (fun x => ⌈fare x⌉₊) V job.issue job.reply := by
  have pos (x : X) : 1 ≤ V x := (Nat.pow_pos (by decide : 0 < 2)).trans_le (power x)
  have one (x : X) : (1:ℝ) ≤ fare x := (by exact_mod_cast pos x : (1:ℝ) ≤ V x).trans (localCost x)
  have nonneg x := zero_le_one.trans (one x)
  have scaled (x : X) : ((C*V x : ℕ):ℝ)+1 ≤ ((C:ℝ)+1)*fare x := by
    rw [Nat.cast_mul,add_mul,one_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (localCost x) (Nat.cast_nonneg _)) (one x)
  obtain ⟨D,clock⟩ := exists_floor_clock (fun x => C*V x) (fun x => small x ++ full x)
    fare nonneg ((C:ℝ)+1) ε hε scaled slack
  let time (x : X) := ⌊(D:ℝ)*fare x⌋₊
  let space (x : X) := interchangeSpacePotential C H (height x) (V x)
  have tied := resolve_tie_exact (node prelude stage b n) job.issue job.reply time space space height
    (fun x => small x ++ full x) order (fun x env ih deck base hc => ?_)
  · let K := max (D+1) (3*C+4*H)
    refine ⟨K,fun x env deck base hc => ?_⟩
    have tm : time x + 1 ≤ (D+1)*(⌈fare x⌉₊+1) := by
      have bound := floor_clock_le_mul_ceil D (nonneg x)
      simp only [time,Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
      omega
    have sp : space x ≤ K*(V x+1) := (interchange_space_potential_linear C H _ _ (power x)).trans
      (Nat.mul_le_mul (le_max_right ..) (Nat.le_succ _))
    exact (tied x env deck base hc).mono (tm.trans (Nat.mul_le_mul_right _ (le_max_left ..)))
      (Nat.add_le_add_left sp _) sp
  · have body := step x env time space space ih deck base hc
    have budget := clock x
    have peak := mixed_space_bound C H height order shrink contract x
    exact body.mono (by dsimp only [time]; omega) (Nat.add_le_add_left peak _) peak

/-- Specialize the selected controller to the manuscript's width fare by
using its actual two ledgers, including repeated calls. -/
theorem resolve_controller_width {job : Job X} {small full : X → List X} {V : X → ℕ}
    {C H : ℕ} (b n : ℕ) (prelude stage : Cmd)
    (step : Sharp (node prelude stage b n) (fun _ => node prelude stage b n) job small full V C H job.issue job.reply)
    (width : X → ℕ) (m : ℕ) (α θ : ℝ) (hm : 1 < m) (hα : 0 ≤ α) (hc : θ < (m:ℝ)^α)
    (wpos : ∀ x, 0 < width x) (power : ∀ x, 2^width x ≤ V x)
    (child : ∀ x y, y ∈ small x ++ full x → width y*m ≤ width x)
    (mass : ∀ x, ((small x ++ full x).map (fun y => (V y:ℝ))).sum ≤ θ*V x)
    (shrink : ∀ x y, y ∈ small x → 3*V y ≤ 2*V x)
    (contract : ∀ x y, y ∈ full x → V y ≤ V x) :
    Certified (controller prelude stage b n) (fun x => ⌈(V x:ℝ)*(width x:ℝ)^α⌉₊) V job.issue job.reply := by
  obtain ⟨ε,pos,slack⟩ := interchange_fare_slack width V (fun x => small x ++ full x) m α θ hm hα hc child mass
  exact resolve_controller b n prelude stage step width _ ε pos power
    (fun x => le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow (by exact_mod_cast wpos x) hα))
    slack (fun x y hy => (by simpa using Nat.mul_lt_mul_of_pos_left hm (wpos y) :
      width y < width y * m).trans_le (child x y hy)) shrink contract

end InterchangeROMRecursion

end NearSquareRoot
end Computability
end OAI
