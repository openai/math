import OAI.ThreeFlat.Diagonal.TraceRowPackets
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI
/-! # Elimination of Boolean validation factors in a weighted trace row -/

namespace ThreeFlat.Diagonal.TraceRowPackets

variable {F V : Type*} [Fintype F] [Fintype V] [CommSemiring F]

abbrev Guard := Unit ⊕ (Fin 2 × Fin 3)

def guardFactor (F : Type*) : Guard → Factor F
  | .inl u => .inl u
  | .inr (s,j) => .inr (s,.inl j)

private def factorEquiv (F : Type*) : Guard ⊕ (Fin 2 × Option F) ≃ Factor F where
  toFun
    | .inl a => guardFactor F a
    | .inr (s,i) => .inr (s,.inr i)
  invFun
    | .inl u => .inl (.inl u)
    | .inr (s,.inl j) => .inl (.inr (s,j))
    | .inr (s,.inr i) => .inr (s,i)
  left_inv := by rintro ((u|⟨s,j⟩)|⟨s,i⟩) <;> rfl
  right_inv := by rintro (u|⟨s,j|i⟩) <;> rfl

/-- Rearrange all physical factors into one global acceptance gate and the
product of the scalars returned by logical clock slots. -/
theorem factorProduct (b : V → Factor F → Bool) :
    (∏ v, ∏ a, scalar a (b v a)) =
      if ∀ v j, b v (guardFactor F j) = true then
        ∏ v, ∏ s : Fin 2, ∏ i : Option F, TraceTerminal.unary i (b v (.inr (s,.inr i)))
      else 0 := by
  classical
  have one (v : V) : (∏ a, scalar a (b v a)) =
      (if ∀ j, b v (guardFactor F j) = true then 1 else 0) *
        ∏ s : Fin 2, ∏ i : Option F, TraceTerminal.unary i (b v (.inr (s,.inr i))) := by
    rw [← (factorEquiv F).prod_comp (fun a => scalar a (b v a)), Fintype.prod_sum_type]
    congr 1
    · convert (Fintype.prod_boole (M₀:=F) (p:=fun j => b v (guardFactor F j) = true)) using 1
      apply Finset.prod_congr rfl
      rintro (u|⟨s,j⟩) _ <;> rfl
    · exact Fintype.prod_prod_type (f:=fun a : Fin 2 × Option F =>
        TraceTerminal.unary a.2 (b v (.inr (a.1,.inr a.2))))
  simp_rw [one]
  rw [Finset.prod_mul_distrib, Fintype.prod_boole]
  split <;> simp_all

omit [Fintype F] [Fintype V] [CommSemiring F] in
theorem guards_iff (b : V → Factor F → Bool) :
    (∀ v j, b v (guardFactor F j) = true) ↔
      (∀ v, b v (.inl ()) = true) ∧
      (∀ v s, b v (.inr (s,.inl 0)) = true) ∧
      (∀ v s, b v (.inr (s,.inl 1)) = true) ∧
      (∀ v s, b v (.inr (s,.inl 2)) = true) := by
  constructor
  · exact fun h => ⟨fun v => h v (.inl ()),fun v s => h v (.inr (s,0)),
      fun v s => h v (.inr (s,1)),fun v s => h v (.inr (s,2))⟩
  · rintro ⟨hm,hc,hp,hi⟩ v (u|⟨s,j⟩)
    · cases u; exact hm v
    · fin_cases j
      · exact hc v s
      · exact hp v s
      · exact hi v s

end ThreeFlat.Diagonal.TraceRowPackets

end OAI
