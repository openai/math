import OAI.Computability.NearSquareRoot.ScheduleUniversal
import OAI.Computability.NearSquareRoot.ShortWordSpace

/-! # Data-head invariants of physical ROM scans -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal

open IntegerMultiplication

/-- A trace whose every prefix satisfies the stated physical invariant. -/
structure During {X : Type} (step : X → Option X) (P : X → Prop) (x : X) (n : ℕ)
    (y : X) : Prop where
  trace : Trace step x n y
  throughout : ∀ k ≤ n, ∀ z, Trace step x k z → P z

namespace During
variable {X : Type} {s : X → Option X} {P R : X → Prop} {x y z : X} {m n : ℕ}

theorem nil (x : X) (h : P x) : During s P x 0 x :=
  ⟨.nil _,fun k hk y tr => by
    obtain rfl : k = 0 := by omega
    simpa only [trace_endpoint_unique tr (.nil x)] using h⟩

theorem trans (a : During s P x m y) (b : During s P y n z) : During s P x (m+n) z := by
  refine ⟨a.trace.trans b.trace, fun k hk u hu => ?_⟩
  by_cases h : k ≤ m
  · exact a.throughout k h u hu
  obtain ⟨v,hv,tail⟩ := trace_split hu (k := m) (by omega)
  obtain rfl := trace_endpoint_unique hv a.trace
  exact b.throughout _ (by omega) _ tail

theorem single (transition : s x = some y) (hx : P x) (hy : P y) : During s P x 1 y := by
  refine ⟨.single transition, fun k hk z hz => ?_⟩
  rcases (show k=0 ∨ k=1 by omega) with rfl | rfl
  · exact trace_endpoint_unique hz (.nil x) ▸ hx
  · exact trace_endpoint_unique hz (.single transition) ▸ hy

theorem cons (transition : s x = some y) (hx : P x) (b : During s P y n z) :
    During s P x (1+n) z :=
  (single transition hx (b.throughout _ (Nat.zero_le _) _ (.nil _))).trans b

theorem imp (h : During s P x n y) (g : ∀ v, P v → R v) : During s R x n y :=
  ⟨h.trace, fun k hk v sub => g v (h.throughout k hk v sub)⟩

end During

/-- The physical data bank is unchanged while the two ROM heads navigate. -/
def HasBank {A I : Type} (d : I → TM.Tape A) (c : TM.Config (Letter A I) PC (Index I)) :=
  ∀ i, c.tape (.inl i) = dataCell (d i)

theorem bank_conf {A I : Type} (s : ℤ → Tag A I) (d : I → TM.Tape A) (b : Bool)
    (f : Phase) (p q : ℤ) : HasBank d (conf s d b f p q) := fun _ => rfl

end Universal

end NearSquareRoot
end Computability
end OAI
