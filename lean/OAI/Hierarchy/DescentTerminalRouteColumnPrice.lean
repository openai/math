import OAI.Hierarchy.DescentTerminalRouteSources
import OAI.Hierarchy.DescentTerminalBookWeights
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Price of each source column installed for the actual terminal route -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.RouteSources
open DescentTerminalEmitter.Compact DescentTerminalLocalPortBook DescentTerminalRowArena
open DescentTerminalRouteLedger DescentDyadicSpan

/-- All five computed row banks have zero literal length. The three book tables and
five route tables fit the same public price as the other compact source columns. -/
theorem columns_priced (V A W q K h : ℕ) (arena:Arena) (other:Columns)
    (prior:∀j,need (other j)≤2^(h/2)+4*(K*W)) (priced:Book.fixedWords V A W q≤2^(h/2))
    (j:Fin 43) :
    need ((Tables.mk 4 V (V*A) A (nameBits 4 (V*A)) W q K).columns arena other j)≤2^(h/2)+4*(K*W) := by
  let T:=Tables.mk 4 V (V*A) A (nameBits 4 (V*A)) W q K
  let bound:=2^(h/2)+4*(K*W)
  have both:Book.fixedWords V A W q≤bound:=priced.trans (Nat.le_add_right ..)
  have width:W≤bound:=by
    have one : span W ≤ 2 * span W := by
      rw [two_mul]
      exact Nat.le_add_right _ _
    have slots : 2 * span W ≤ Book.lookupWords V A W :=
      (Nat.le_add_left (2 * span W) _).trans (Nat.le_add_right _ _)
    exact (span_ge W).trans (one.trans (slots.trans ((Book.lookup_le_fixed V A W q).trans both)))
  have menu:T.menuSize≤bound:=(Book.route_domain V A W q).trans both
  have all_:2^T.line+T.extent+radix W T.line+3*T.extent+2^T.buffer≤bound:=
    (Book.emitter_domains V A W q (K*W)).trans (Nat.add_le_add_right priced _)
  have terms (a b c d e total : ℕ) (cover : a+b+c+d+e ≤ total) :
      a≤total ∧ b≤total ∧ c≤total ∧ d≤total ∧ e≤total := by omega
  obtain ⟨code,phase,updates,ends,decode⟩ := terms _ _ _ _ _ _ all_
  change need (T.columns arena other j)≤bound
  unfold Tables.columns
  split <;> first
    | exact Nat.zero_le _
    | exact width
    | exact menu
    | exact code
    | exact phase
    | exact updates
    | exact ends
    | exact decode
    | exact prior j

end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.RouteSources

end OAI
