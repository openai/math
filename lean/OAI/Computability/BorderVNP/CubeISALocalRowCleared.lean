import OAI.Computability.BorderVNP.CubeISALocalRowSetup

/-! # Preserving the actual descriptor while clearing a local declaration row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical.Owned BorderVNP.Cube.Tally OwnedRowSetup

/-- Register and memory facts supplied to the full local tally after its zero fill. -/
structure Cleared (l : Layout) {n : ℕ} (b h K s actual claim vertex : ℕ) (i : Fin (n+1))
    (lo hi : Fin l.d) (z : NatState) : Prop where
  cfg : SingleTally.Config i lo hi actual (l.blocks*l.bc) z
  packet : ∀ eqn : lo < hi, Owned.packetReady (blocks := l.blocks) i ⟨(lo,hi),eqn⟩ (bankWidth n b h K s) l.bank 0 z
  descriptor : z.reg 8 = head l n b h K s
  header : PacketTally.Header z.mem (head l n b h K s) n K h actual (head l n b h K s+8) s
  declared : z.reg 59 = claim
  saved : z.reg 61 = vertex
  zeros : ∀ j : Fin (n+1), z.mem (actual+j.val) = 0

/-- Clearing from the addressed setup zeros this role's own subtotal and leaves
the eight-word descriptor, all packet selectors and the true declaration intact. -/
theorem clearReady_run {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (l : Layout) (i : Fin (n+1)) (lo hi : Fin l.d)
    (b h K s actual claim vertex : ℕ)
    (ready : Ready l b h K s actual claim vertex i lo hi (.ofWords r m))
    (before : actual+(n+1) ≤ head l n b h K s) (endRoom : actual+(n+1) ≤ 2^w) :
    BoundedRun pub mac clear r m (4*(n+1)+1) (fun z =>
      Cleared l b h K s actual claim vertex i lo hi z ∧
      ∀ x, x < actual ∨ actual+(n+1) ≤ x → z.mem x = readings m x) := by
  apply (withKeptRegs (clear_run pub mac r m actual (n+1) ready.cfg.zero ready.cfg.one ready.zero
    ready.dim ready.base endRoom)).mono le_rfl
  rintro z ⟨mem,reg⟩
  have old (x : ℕ) (hx : x < actual ∨ actual+(n+1) ≤ x) : z.mem x = readings m x := by
    rw [mem]
    simp [zeroPrefix,show ¬(actual ≤ x ∧ x < actual+(n+1)) by omega]
  have retain (k : ℕ) : z.mem (head l n b h K s+k) = readings m (head l n b h K s+k) := old _ (.inr (by omega))
  refine ⟨⟨?_,?_,(reg 8 (by decide)).trans ready.descriptor,?_,
    (reg 59 (by decide)).trans ready.declared,(reg 61 (by decide)).trans ready.saved,?_⟩,old⟩
  · apply ready.cfg.transfer
    intro k hk _ _
    exact reg k ((by decide : ∀ k : Reg, k.val < 24 → clear.keeps k = true) k hk)
  · intro good
    obtain ⟨e0,e1,e2,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19⟩ := ready.packet good
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals apply (reg _ (by decide)).trans
    all_goals assumption
  · obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7⟩ := ready.header
    exact ⟨(retain 0).trans e0,(retain 1).trans e1,(retain 2).trans e2,(retain 3).trans e3,
      (retain 4).trans e4,(retain 5).trans e5,(retain 6).trans e6,(retain 7).trans e7⟩
  · intro j
    rw [mem]
    simp [zeroPrefix,j.isLt]

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
