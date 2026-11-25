import OAI.Optimization.LinearProgramming.PriceGame.Computation

/-! Total oracle communication in a finite computation, including inconsistent transcripts. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Computation

universe u v

variable {N : ℕ} {α : Type u} {β : Type v}

/-- Uniform bound on every query at every node. -/
def AllQueries (P : Query N → Prop) : Computation N α → Prop
  | .pure _ => True
  | .ask q rest => P q ∧ ∀ reply, AllQueries P (rest reply)

theorem allQueries_bind (P : Query N → Prop) {p : Computation N α} {f : α → Computation N β}
    (hp : AllQueries P p) (hf : ∀ a, AllQueries P (f a)) : AllQueries P (p.bind f) := by
  induction p with
  | pure a => exact hf a
  | ask q rest ih => exact ⟨hp.1, fun b => ih b (hp.2 b)⟩

theorem allQueries_map (P : Query N → Prop) {p : Computation N α} (hp : AllQueries P p) (f : α → β) :
    AllQueries P (p.map f) := allQueries_bind P hp (fun _ => True.intro)

theorem allQueries_traverse (P : Query N → Prop) (f : α → Computation N β) {xs : List α}
    (hf : ∀ a ∈ xs, AllQueries P (f a)) : AllQueries P (traverse f xs) := by
  induction xs with
  | nil => exact True.intro
  | cons a as ih =>
    apply allQueries_bind P (hf a List.mem_cons_self)
    intro b
    exact allQueries_map P (ih (fun x hx => hf x (List.mem_cons_of_mem a hx))) (b :: ·)

theorem allQueries_iterate (P : Query N → Prop) (f : α → Computation N α)
    (hf : ∀ a, AllQueries P (f a)) (k : ℕ) (a : α) : AllQueries P (iterate f k a) := by
  induction k generalizing a with
  | zero => exact True.intro
  | succ k ih => exact allQueries_bind P (hf a) ih

/-- The worst-case charge over all reply branches. A charge can count serialized bits,
arithmetic cost per query, or a nonnegative sum of distinct resources. -/
def worstCharge (charge : Query N → ℕ) : Computation N α → ℕ
  | .pure _ => 0
  | .ask q next => charge q + max (worstCharge charge (next false)) (worstCharge charge (next true))

theorem worstCharge_bind_le (charge : Query N → ℕ) (p : Computation N α)
    (f : α → Computation N β) (K : ℕ) (hk : ∀ a, worstCharge charge (f a) ≤ K) :
    worstCharge charge (p.bind f) ≤ worstCharge charge p + K := by
  induction p with
  | pure a => simpa [worstCharge] using hk a
  | ask q next ih =>
    simp only [bind_ask, worstCharge]
    have hfalse := ih false
    have htrue := ih true
    omega

theorem worstCharge_le_height_mul (charge : Query N → ℕ) (K : ℕ) (p : Computation N α)
    (hbound : AllQueries (fun q => charge q ≤ K) p) : worstCharge charge p ≤ p.height * K := by
  induction p with
  | pure => simp [worstCharge, height]
  | ask q next ih =>
    have hfalse := ih false (hbound.2 false)
    have htrue := ih true (hbound.2 true)
    have both : max (worstCharge charge (next false)) (worstCharge charge (next true)) ≤
        max (next false).height (next true).height * K := by
      apply max_le
      · exact hfalse.trans (Nat.mul_le_mul_right K (le_max_left _ _))
      · exact htrue.trans (Nat.mul_le_mul_right K (le_max_right _ _))
    simp only [worstCharge, height, Nat.succ_mul]
    exact (Nat.add_le_add hbound.1 both).trans (by omega)

/-- Execute and meter precisely the visited branch with the complete adaptive history. -/
def runMetered (charge : Query N → ℕ) (reply : List (Query N × Bool) → Query N → Bool)
    (p : Computation N α) (history : List (Query N × Bool) := []) : α × ℕ :=
  match p with
  | .pure a => (a, 0)
  | .ask q next =>
    let b := reply history q
    let v := runMetered charge reply (next b) ((q,b) :: history)
    (v.1, charge q + v.2)

theorem runMetered_value (charge : Query N → ℕ) (reply : List (Query N × Bool) → Query N → Bool)
    (p : Computation N α) (history : List (Query N × Bool)) :
    (runMetered charge reply p history).1 = p.run reply history := by
  induction p generalizing history with
  | pure => rfl
  | ask q next ih => exact ih _ _

theorem runMetered_le (charge : Query N → ℕ) (reply : List (Query N × Bool) → Query N → Bool)
    (p : Computation N α) (history : List (Query N × Bool)) :
    (runMetered charge reply p history).2 ≤ worstCharge charge p := by
  induction p generalizing history with
  | pure => exact le_rfl
  | ask q next ih =>
    have ht := ih (reply history q) ((q, reply history q) :: history)
    change charge q + _ ≤ charge q + _
    apply Nat.add_le_add_left
    exact ht.trans (by cases reply history q <;> simp)

/-- Explicit charge for reading one answer bit and writing the supplied serialization. -/
def wireCost (serialize : Query N → List Bool) (q : Query N) : ℕ := (serialize q).length + 1

theorem communication_le (serialize : Query N → List Bool) (B : ℕ)
    (reply : List (Query N × Bool) → Query N → Bool) (p : Computation N α)
    (history : List (Query N × Bool))
    (bounded : AllQueries (fun q => (serialize q).length ≤ B) p) :
    (runMetered (wireCost serialize) reply p history).2 ≤ p.height * (B + 1) := by
  apply (runMetered_le _ _ _ _).trans
  apply worstCharge_le_height_mul
  clear reply history
  induction p with
  | pure => exact True.intro
  | ask q next ih => exact ⟨Nat.add_le_add_right bounded.1 1, fun b => ih b (bounded.2 b)⟩

end Computation
end PriceGame
end LinearProgramming
end Optimization
end OAI
