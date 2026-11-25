import OAI.Hierarchy.ProbePayloadStrip
import OAI.Hierarchy.ProbeColumnAccounts

namespace OAI
/-! # The payload tests use the global commodity inventory exactly once -/

namespace Hierarchy.AdaptiveProbe.PayloadStrip
open scoped BigOperators Classical
noncomputable section

variable {P : Type*} {N k : ℕ}

def rowAddress (p : P) : Quotes N k → Commodity P N k
  | .inl _ => .inl p
  | .inr (j,c) => .inr ((p,j),c)

/-- Both the ordinary payload and every signed counter of every tile occur in one
and only one initial test strip. -/
def allAddresses : P × Quotes N k ≃ Commodity P N k where
  toFun i := rowAddress i.1 i.2
  invFun
    | .inl p => (p,.inl ())
    | .inr ((p,j),c) => (p,.inr (j,c))
  left_inv := by rintro ⟨p,⟨⟩|⟨j,c⟩⟩ <;> rfl
  right_inv := by rintro (p | ⟨⟨p,j⟩,c⟩) <;> rfl

theorem actual_payload_prices (p : P) (M : ℝ) (x : Commodity P N k → ℝ) :
    prices N k M (rowQuotes x p) =
    activePrice (ColumnWires.account (rowAddress p)) (ColumnWires.printed M (length N)) x := by
  have h : rowQuotes x p = x ∘ rowAddress p := by funext i; cases i <;> rfl
  rw [h]; funext e; exact ColumnWires.quote_active M (length N) _ x e

/-- The `some`-stock fibers of payload-strip physical wire roles are singletons,
prior to restriction to the selected native subset of records. -/
theorem paid_unique {p q : P}
    {r s : ColumnWires.Role (Columns N) (Fin (edgeCount N)) (Quotes N k ⊕ Empty) k}
    {i : Commodity P N k} (a : ColumnWires.account (rowAddress p) r=some i)
    (b : ColumnWires.account (rowAddress q) s=some i) : p=q ∧ r=s := by
  cases r <;> try contradiction
  case extra r =>
    cases r with
    | inr r => exact r.elim
    | inl u =>
      cases s <;> try contradiction
      case extra s =>
        cases s with
        | inr s => exact s.elim
        | inl v =>
          have e := Option.some.inj (a.trans b.symm)
          have ids : (p,u)=(q,v) := allAddresses.injective e
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj ids
          exact ⟨rfl,rfl⟩

end
end Hierarchy.AdaptiveProbe.PayloadStrip

end OAI
