import OAI.Computability.BorderVNP.CubeTeamNativeMinimum
import OAI.Computability.BorderVNP.CubeTeamNativeModel

/-! # Memory intervals of the sparse group assignment pass -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamNative

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Public counts and the three array base addresses. There are `r+1` teams. -/
structure Layout where
  /-- Team count minus one. -/
  r : ℕ
  /-- Number of symbol groups in the selected coordinate. -/
  groups : ℕ
  /-- Input joint weight of each group. -/
  weights : ℕ
  /-- Writable total for each team. -/
  totals : ℕ
  /-- Writable selected team for each group. -/
  owners : ℕ

/-- Register values kept throughout the two counted loops. -/
structure Layout.Ready (l : Layout) (z : NatState) : Prop where
  zeroReg : z.reg 0 = 0
  oneReg : z.reg 1 = 1
  teamCount : z.reg 3 = l.r+1
  groupCount : z.reg 4 = l.groups
  weightBase : z.reg 5 = l.weights
  totalBase : z.reg 6 = l.totals
  ownerBase : z.reg 7 = l.owners

/-- Equalities on the fixed low registers preserve the public layout. -/
theorem Layout.Ready.congr {l : Layout} {a b : NatState} (h : l.Ready a)
    (he : ∀ j : Reg, j.val < 8 → b.reg j = a.reg j) : l.Ready b :=
  ⟨(he 0 (by decide)).trans h.zeroReg,(he 1 (by decide)).trans h.oneReg,
    (he 3 (by decide)).trans h.teamCount,(he 4 (by decide)).trans h.groupCount,
    (he 5 (by decide)).trans h.weightBase,(he 6 (by decide)).trans h.totalBase,
    (he 7 (by decide)).trans h.ownerBase⟩

/-- Actual word bounds and separation of the input and output intervals. -/
structure Layout.Allocated (l : Layout) (w : ℕ) : Prop where
  weightsFit : ∀ i < l.groups, l.weights+i < 2^w
  totalsFit : ∀ j : Fin (l.r+1), l.totals+j.val < 2^w
  ownersFit : ∀ i < l.groups, l.owners+i < 2^w
  weightsTotals : ∀ i < l.groups, ∀ j : Fin (l.r+1), l.weights+i ≠ l.totals+j.val
  weightsOwners : ∀ i < l.groups, ∀ k < l.groups, l.weights+i ≠ l.owners+k
  ownersTotals : ∀ i < l.groups, ∀ j : Fin (l.r+1), l.owners+i ≠ l.totals+j.val

/-- Memory outside the two writable intervals retains every original word. -/
def Layout.Preserves (l : Layout) (orig mem : ℕ → ℕ) : Prop :=
  ∀ a, (∀ j : Fin (l.r+1), a ≠ l.totals+j.val) → (∀ i < l.groups, a ≠ l.owners+i) →
    mem a = orig a

/-- Prefix semantics of the native group pass. -/
structure Tables (l : Layout) (ws orig : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℕ) : Prop where
  totals : ∀ j : Fin (l.r+1), mem (l.totals+j.val) = loads l.r ws k j
  owners : ∀ i < k, mem (l.owners+i) = (owner l.r ws i).val
  other : l.Preserves orig mem

/-- Two writes of the native commit step, to the owner cell and then the total. -/
def commitWords (l : Layout) (ws : ℕ → ℕ) (k : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let j := owner l.r ws k
  Function.update (Function.update mem (l.owners+k) j.val)
    (l.totals+j.val) (loads l.r ws k j + ws k)

/-- The native two-store commit realizes the next prefix of the greedy assignment. -/
theorem Tables.commit {l : Layout} {ws orig mem : ℕ → ℕ} {w k : ℕ}
    (t : Tables l ws orig k mem) (al : l.Allocated w) (hk : k < l.groups) :
    Tables l ws orig (k+1) (commitWords l ws k mem) := by
  let j := owner l.r ws k
  constructor
  · intro i
    by_cases h : i = j
    · subst i
      simp [commitWords, loads, owner, j]
    · have ht : l.totals+i.val ≠ l.totals+j.val := by
        intro he
        exact h (Fin.ext (Nat.add_left_cancel he))
      have hw := (al.ownersTotals k hk i).symm
      change Function.update (Function.update mem (l.owners+k) j.val)
        (l.totals+j.val) (loads l.r ws k j + ws k) (l.totals+i.val) =
        Function.update (loads l.r ws k) j (loads l.r ws k j + ws k) i
      rw [Function.update_of_ne ht, Function.update_of_ne hw, Function.update_of_ne h]
      exact t.totals i
  · intro i hi
    have ht := al.ownersTotals i (by omega) j
    rw [commitWords,Function.update_of_ne ht]
    by_cases he : i = k
    · subst i
      simp
    · rw [Function.update_of_ne (show l.owners+i ≠ l.owners+k by omega)]
      exact t.owners i (by omega)
  · intro a ht ho
    rw [commitWords,Function.update_of_ne (ht j),Function.update_of_ne (ho k hk)]
    exact t.other a ht ho

end Cube.TeamNative

end BorderVNP
end Computability
end OAI
