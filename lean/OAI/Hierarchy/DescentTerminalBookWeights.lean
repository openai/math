import OAI.Hierarchy.DescentTerminalRouteInvoice
import OAI.Hierarchy.DescentTerminalWeightWords

namespace OAI
/-! # Sizes of the physical book dictionaries and values of every printed weight -/
namespace Hierarchy.DescentTerminalLocalPortBook.Book
open DescentDyadicSpan DescentTerminalPrintedFieldsRAM DescentTerminalRouteLedger
open scoped BigOperators
noncomputable section
variable (V A W q : ℕ)
local notation "M" => V*A
local notation "a" => tokenBits (V*A)
local notation "b" => Bytes 4 V (V*A) A a
local notation "size" => fixedWords V A W q

theorem token_fit (g : Fin 4) (j : Fin (V*A)) : g.val*M+j.val<2^a := by
  apply Nat.lt_of_lt_of_le _ (Nat.le_pow_clog (by decide : 1<2) (4*M+1))
  have same:=Nat.mul_le_mul_right M (show g.val+1≤4 from g.isLt)
  rw [Nat.succ_mul] at same
  omega

theorem book_domain : b≤ size := by
  apply (span_ge b).trans
  apply le_trans _ (lookup_le_fixed V A W q)
  dsimp only [lookupWords]
  omega

theorem route_domain : W*(W*b)≤ size := by
  apply (span_ge _).trans
  apply le_trans _ (lookup_le_fixed V A W q)
  dsimp only [lookupWords]
  omega

theorem weights_size (i : Fin 6) :
    (weights (capacities 4 V M A a i) (strides 4 V M A a i)).length≤ size := by
  rw [weights,List.length_ofFn]
  exact (capacity_fit 4 V M A a i).trans (book_domain V A W q)

theorem weights_value (i : Fin 6) (v : Fin (capacities 4 V M A a i)) :
    (weights (capacities 4 V M A a i) (strides 4 V M A a i))[v.val]'(by simp [weights]) < b := by
  simpa only [weights,List.getElem_ofFn] using weight_fit i v

theorem emitter_domains (pool : ℕ) : let c:=routeBits V A W q
    2^c+pool+radix W c+3*pool+2^(W*c) ≤ size+4*pool := by
  intro c
  have off:=span_ge (2^c)
  have step:=span_ge (radix W c)
  have last:=span_ge (2^(W*c))
  change _ ≤ (lookupWords V A W+span (2^c)+span (radix W c)+span (2^(W*c)))+4*pool
  omega

end
end Hierarchy.DescentTerminalLocalPortBook.Book

end OAI
