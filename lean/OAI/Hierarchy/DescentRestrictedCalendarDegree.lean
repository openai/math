import OAI.Hierarchy.DescentNextCoordinates

namespace OAI
/-! # The degree of the ten-hop calendar directory

A hop reads its incoming host and dyadic coordinate. Only the final hop's
slot contributes to the number of distinct reachable addresses.
-/

namespace Hierarchy.DescentHostDirectory

open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V]

private def zeroSlot (x : Key V) : Key V := (x.1, x.2.1, 0)

private theorem forget_slots (near : V → Finset V) (D slots h : ℕ) (x y : Key V)
    (walk : y ∈ directory near D slots h x) :
    zeroSlot y ∈ directory near D 1 h (zeroSlot x) := by
  induction h generalizing y with
  | zero =>
    have same : y = x := Finset.mem_singleton.mp walk
    subst y
    exact Finset.mem_singleton_self _
  | succ h ih =>
    obtain ⟨z, earlier, last⟩ := Finset.mem_biUnion.mp walk
    obtain ⟨host, tail⟩ := Finset.mem_product.mp last
    obtain ⟨coord, _⟩ := Finset.mem_product.mp tail
    exact extend (ih z earlier) (Finset.mem_product.mpr
      ⟨host, Finset.mem_product.mpr ⟨coord, Finset.mem_range.mpr (by decide : 0 < 1)⟩⟩)

theorem restricted_degree_calendar [Fintype V] (near : V → Finset V) (D k slots Δ : ℕ)
    (old : ∀ v, (near v).card ≤ Δ) (enough : 3 ≤ slots) (v : Host V k slots) :
    (restrictedNear near D k slots v).card ≤ ((Δ+1)*(D+1+2^D)*slots)^10 := by
  let encode (w : Host V k slots) : Key V × ℕ := (zeroSlot w.val, w.val.2.2)
  have injective : Function.Injective encode := by
    intro x y eqn
    apply Subtype.ext
    exact congrArg (fun p : Key V × ℕ => ((p.1.1, p.1.2.1, p.2) : Key V)) eqn
  let slim := directory near D 1 10 (zeroSlot v.val)
  have into (w : Host V k slots) (hw : w ∈ restrictedNear near D k slots v) :
      encode w ∈ slim ×ˢ Finset.range slots := by
    have walk := (Finset.mem_filter.mp hw).2.1
    have slot := (Finset.mem_product.mp (Finset.mem_product.mp w.property).2).2
    exact Finset.mem_product.mpr ⟨forget_slots near D slots 10 v.val w.val walk, slot⟩
  have count := Finset.card_le_card_of_injOn encode (fun _ hw => into _ hw) injective.injOn
  simp only [Finset.card_product, Finset.card_range] at count
  have reach : slim.card ≤ ((Δ+1)*(D+1+2*2^D))^10 := by
    simpa only [Nat.mul_one] using directory_card near D 1 Δ old 10 (zeroSlot v.val)
  let base := (Δ+1)*(D+1+2^D)
  have factor : (Δ+1)*(D+1+2*2^D) ≤ base*2 := by
    calc
      _ ≤ (Δ+1)*((D+1+2^D)*2) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := (Nat.mul_assoc ..).symm
  have pay : 2^10*slots ≤ slots^10 := by
    rw [pow_succ slots 9]
    exact Nat.mul_le_mul_right slots
      ((by decide : (2:ℕ)^10 ≤ 3^9).trans (Nat.pow_le_pow_left enough 9))
  calc
    _ ≤ slim.card*slots := count
    _ ≤ (base*2)^10*slots := Nat.mul_le_mul_right _ (reach.trans (Nat.pow_le_pow_left factor 10))
    _ = base^10*(2^10*slots) := by rw [mul_pow, Nat.mul_assoc]
    _ ≤ base^10*slots^10 := Nat.mul_le_mul_left _ pay
    _ = _ := (mul_pow base slots 10).symm


end
end Hierarchy.DescentHostDirectory

end OAI
