import OAI.Computability.BorderVNP.CellProfileCost
import Mathlib.Tactic.GCongr

/-! # A fixed polynomial private clock for a bounded profile record -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Profile

open Prefix CellMacro

/-- All three integer fields in a port are bounded by the cell's expanded size. -/
def PortBound (M : ℕ) (p : CellSparse.Port) := p.base ≤ M ∧ p.copyStride ≤ M ∧ p.laneStride ≤ M

private theorem port_le {M off i k : ℕ} {p : CellSparse.Port} (hp : PortBound M p)
    (ho : off ≤ (M+1)^3) (hi : i ≤ M) (hk : k ≤ M) :
    off+p.atBit i k ≤ 4*(M+1)^3 := by
  calc
    _ ≤ (M+1)^3+(M+M*M+M*M) := by obtain ⟨_,_,_⟩ := hp; unfold Port.atBit; gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (M^3)]

private theorem flags_le {M base copies t i k : ℕ} (hb : base ≤ (M+1)^3) (hc : copies ≤ M) (ht : t ≤ M)
    (hi : i ≤ M) (hk : k ≤ M) : address (termBase base copies t) copies i k ≤ 4*(M+1)^3 := by
  calc
    _ ≤ (M+1)^3+M*((M+1)*(M+1))+M*(M+1)+M := by unfold termBase address; gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (M^3)]

/-- At scale `M` the complete profile check, including all decoded unary offsets, has
a fixed degree-nine private clock. No cost assumption about compiled tests is needed. -/
theorem budget_polynomial {base off copies w M : ℕ} {s : CellSparse.Port} {hist : List ℕ}
    {routes : List Route} (e : List ℕ) (hbase : base ≤ (M+1)^3) (hoff : off ≤ (M+1)^3)
    (hc : copies ≤ M) (hw : w ≤ M) (hh : hist.length ≤ M) (hr : routes.length ≤ M)
    (hs : PortBound M s)
    (hroute : ∀ r ∈ routes, r.term ≤ M ∧ r.lanes ≤ M ∧ PortBound M r.original ∧ PortBound M r.compact) :
    budget ((profileGen base off copies s w hist routes).expand e) ≤ 15000*(M+2)^9 := by
  let A := 4*(M+1)^3
  have ha : ReadBound base off copies s w hist.length routes A := by
    constructor
    · intro i hi k hk; exact port_le hs hoff (hi.le.trans hc) (hk.le.trans hw)
    · intro t ht i hi k hk
      exact flags_le hbase hc (ht.le.trans hh) (hi.trans hc) (hk.trans hc)
    · intro r hm i hi k hk j hj
      obtain ⟨ht,hl,hp,hp'⟩ := hroute r hm
      exact ⟨port_le hp hoff (hi.le.trans hc) (hj.le.trans hl), port_le hp' hoff (hk.trans hc) (hj.le.trans hl),
        flags_le hbase hc ht (hi.le.trans hc) (hk.trans hc)⟩
  apply (profileGen_budget_le _ _ _ _ _ _ _ e A M ha (fun r hm => (hroute _ hm).2.1)).trans
  let N := 40*(M+1)^2
  have hn : maxNodes w hist.length ≤ N := by
    change (40*w+40)*(hist.length+1) ≤ 40*(M+1)^2
    calc
      _ ≤ (40*M+40)*(M+1) := by gcongr
      _ = _ := by ring
  have htests : copies+hist.length*((copies+1)*(copies+1)+1)+routes.length*(1+copies*(copies+1)*M) ≤
      M+M*((M+1)*(M+1)+1)+M*(1+M*(M+1)*M) := by gcongr
  have hguard : guardCost A (maxNodes w hist.length) ≤ N*(A+N+20)+5 := by unfold guardCost; gcongr
  calc
    _ ≤ 5*(M+M*((M+1)*(M+1)+1)+M*(1+M*(M+1)*M))*(N*(A+N+20)+5)+2 := by gcongr
    _ ≤ _ := by
      dsimp [N,A]
      nlinarith only [Nat.zero_le M, Nat.zero_le (M^2), Nat.zero_le (M^3), Nat.zero_le (M^4),
        Nat.zero_le (M^5), Nat.zero_le (M^6), Nat.zero_le (M^7), Nat.zero_le (M^8), Nat.zero_le (M^9)]

end CellSparse.Profile

end BorderVNP
end Computability
end OAI
