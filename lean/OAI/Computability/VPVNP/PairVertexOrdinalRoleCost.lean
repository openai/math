import OAI.Computability.VPVNP.PairVertexSelectedReport
import OAI.Computability.VPVNP.CompressorSourceTransport

/-! # A common cost bound for the installed terminal roles -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM DFS LocalHistory NetworkKernel NodeArguments TreeDecode

variable {geometry rootFields leaf shrink refresh : Segment} {p regs w endAddr : ℕ}
  {A : Placement (segments geometry rootFields leaf shrink refresh) p regs} {M : Machine w p regs
    11}
  {m : Memory w} {allow : ℕ → Prop} {cost bound : VisitPath w endAddr → Prop}

/-- Transfer a local role estimate without losing the actual machine link,
external memory update or read footprint. -/
theorem JobGuard.withCost (le : ∀ j, cost j → bound j) {j : VisitPath w endAddr}
    (guard : JobGuard A M m allow cost j) : JobGuard A M m allow bound j :=
  ⟨guard.1,guard.2.1,guard.2.2.1,le j guard.2.2.2⟩

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {κ : L → R} {N : Network}
  {valid : List Packet → Scratch w endAddr → Prop} {hist : Scratch w endAddr → L → ℕ}

/-- The same native leaf jobs and semantic exponent increments satisfy
any common upper bound on their observed costs. -/
theorem emits_withCost {P : SiteParsers κ N} {input : Packets N} {jobs : JobsFor P}
    (native : Emits valid hist (JobGuard A M m allow cost) P input jobs)
    (le : ∀ j, cost j → bound j) :
    Emits valid hist (JobGuard A M m allow bound) P input jobs := by
  intro v z x pending s ready
  obtain ⟨js,run⟩ := native v z x pending s ready
  exact ⟨js,run.realized,run.ready,fun j hj => (run.framed j hj).withCost le,run.remaining⟩

/-- Use a shared role allowance on each selected shrink or refresh pass. -/
theorem emitsNode_withCost {t : Term R N} {r : TermParsers κ t} {ptr : t.output.Site → ℕ × ℕ}
    {before : Packets N} {next : Packets t.output}
    (native : EmitsNode valid hist (JobGuard A M m allow cost) r ptr before next)
    (le : ∀ j, cost j → bound j) :
    EmitsNode valid hist (JobGuard A M m allow bound) r ptr before next := by
  intro v z a k pending s ready
  obtain ⟨j,job,enabled,guard,later⟩ := native v z a k pending s ready
  exact ⟨j,job,enabled,guard.withCost le,later⟩

/-- Bound used on an individual role report in the selected vertex call. -/
def ordinalJobCost (n power scan : ℕ) (j : VisitPath w endAddr) : Prop :=
  countProbes j.trace ≤ scan * (n.log2 + 1) ^ power ∧ j.trace.length ≤ n ^ 43

/-- In the installed cursor leaf, the dispatch and optional virtual-header
read together make at most two probes. The private role already includes
its reload and auxiliary computation. -/
theorem leaf_ordinal_cost {n power scan : ℕ} (hn : 1 ≤ n) (hs : 2 ≤ scan)
    {j : VisitPath w endAddr}
    (localCost : countProbes j.trace ≤ 2 ∧ j.trace.length + 17 ≤ n ^ 40) :
    ordinalJobCost n power scan j := by
  have hL : 1 ≤ (n.log2 + 1) ^ power := Nat.one_le_pow _ _ (by omega)
  exact ⟨localCost.1.trans (hs.trans (Nat.le_mul_of_pos_right _ hL)),
    (Nat.le_add_right j.trace.length 17).trans
      (localCost.2.trans (Nat.pow_le_pow_right hn (by decide)))⟩

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
