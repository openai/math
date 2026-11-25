import OAI.LinearAlgebra.FiniteFourier.CircuitComposition

/-! # Combining two integral circuit outputs

The program first computes both circuits on their shared inputs. Each output then
uses at most one extra binary gate to combine the two available readouts. This
construction also works over arbitrary semirings.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R I O : Type*} [Semiring R]

private theorem combineReadouts {r : ℕ} (p : Program R I r) (t : Finset O)
    (f g : O → (I → R) → R) (hf : ∀ o, Available p (f o)) (hg : ∀ o, Available p (g o))
    (a b : R) :
    ∃ n ≤ r + t.card, ∃ q : Program R I n, (∀ h, Available p h → Available q h) ∧
      ∀ o ∈ t, Available q (fun x => a * f o x + b * g o x) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨r, by simp, p, fun _ h => h, by simp⟩
  | @insert o t ho ih =>
    obtain ⟨n, hn, q, hq, ht⟩ := ih
    obtain ⟨m, hm, q', hq', hnew⟩ := available_combine q a b (hq _ (hf o)) (hq _ (hg o))
    refine ⟨m, ?_, q', fun _ h => hq' _ (hq _ h), fun i hi => ?_⟩
    · rw [Finset.card_insert_of_notMem ho]
      omega
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hnew
      · exact hq' _ (ht i hi)

/-- Taking a pointwise linear combination requires at most one additional gate
per output. There are no constraints on the two scalars or on the inputs. -/
theorem circuit_sumPair (I O : Type*) [Fintype O] (a b : R) {s t : ℕ}
    (p : Circuit R I O s) (q : Circuit R I O t) :
    ∃ u ≤ s + t + Fintype.card O, ∃ z : Circuit R I O u, ∀ x o,
      z.eval x o = a * p.eval x o + b * q.eval x o := by
  obtain ⟨n, hn, r, hr⟩ := circuit_fanout p q
  have hp (o : O) : Available r.program (fun x => p.eval x o) :=
    ⟨r.output (.inl o), fun x => congrFun (hr x) (.inl o)⟩
  have hq (o : O) : Available r.program (fun x => q.eval x o) :=
    ⟨r.output (.inr o), fun x => congrFun (hr x) (.inr o)⟩
  obtain ⟨u, hu, z, _, hz⟩ := combineReadouts r.program Finset.univ _ _ hp hq a b
  choose out hout using fun o => hz o (Finset.mem_univ o)
  exact ⟨u, hu.trans (Nat.add_le_add_right hn _), ⟨z, out⟩, fun x o => hout o x⟩

end FiniteFourier
end LinearAlgebra
end OAI
