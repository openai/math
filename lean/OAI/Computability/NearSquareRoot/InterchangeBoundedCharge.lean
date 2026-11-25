import OAI.Computability.NearSquareRoot.InterchangeBoundedBeadCore
import OAI.Computability.NearSquareRoot.InterchangeBoundedBreeze

/-! # Constant-factor changes to rectangular row counts and payloads -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayload
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip

variable {I J : Type} {r : Regime I} {n n' l : I → ℕ} {p q : I → Tree} {f g : I → ℝ}

theorem BoundedBreeze.rescale (h : BoundedBreeze f r n' l p q)
    (rate : ∀ i, 1 ≤ g i) (C D : ℕ) (rows : ∀ i, n' i ≤ C*n i)
    (price : ∀ i, f i ≤ D*g i) : BoundedBreeze g r n l p q := by
  obtain ⟨hf,k,task⟩ := h
  have massBound (i : I) : mass r n' l k i ≤ C * mass r n l k i := by
    rw [mass,mass,← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast rows i
  refine ⟨rate,k,task.bound (C*D+1) (C+1) (fun i => ceil_charge ?_) (fun i => ceil_charge (massBound i))⟩
  calc
    runrate f r n' l k i ≤ (C*mass r n l k i) * (D*g i) := mul_le_mul (massBound i) (price i)
      (by linarith [hf i]) (by unfold mass; positivity)
    _ = ((C*D:ℕ):ℝ)*runrate g r n l k i := by unfold runrate; push_cast; ring

/-- Once the degree of a fixed command has been extracted, genuine payload
bits can absorb the per-record header expense in both time and peak space. -/
theorem BoundedBreeze.select_payload (h : BoundedBreeze f r n l p q) (select : ℕ → J → I)
    (fit : ∀ K j, (r.scale (select K j)+1)^K ≤ l (select K j)) :
    ∃ K : ℕ, let a := select K
      Space.BoundedTask (fun j => ⌈(n (a j):ℝ)*l (a j)*f (a j)⌉₊)
        (fun j => n (a j)*l (a j)) (p ∘ a) (q ∘ a) := by
  obtain ⟨hf,K,t⟩ := h
  let a := select K
  have hm (j : J) : mass r n l K (a j) ≤ 2 * ((n (a j) * l (a j) : ℕ) : ℝ) := by
    have z : (r.scale (a j) + 1 : ℝ)^K ≤ l (a j) := by exact_mod_cast fit K j
    unfold mass
    rw [Nat.cast_mul]
    calc
      _ ≤ (n (a j):ℝ)*(l (a j)+l (a j)) := by gcongr
      _ = _ := by ring
  refine ⟨K,(t.on a).bound 3 3 ?_ ?_⟩
  · intro j
    apply ceil_charge (C:=2)
    change mass r n l K (a j)*f (a j) ≤ _
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_right (hm j) (by linarith [hf (a j)])
      _ = _ := by push_cast; ring
  · intro j
    simpa only [Nat.cast_ofNat,Nat.ceil_natCast] using (ceil_charge (C:=2) (hm j))

end InterchangePayload

end NearSquareRoot
end Computability
end OAI
