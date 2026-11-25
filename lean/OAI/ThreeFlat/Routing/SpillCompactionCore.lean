import OAI.ThreeFlat.Routing.SpillSlots
import OAI.ThreeFlat.BitNetwork.PinMap
import Mathlib.Tactic.Ring

namespace OAI
/-! # Dyadic composition and padding for sparse compaction -/

noncomputable section
open scoped Classical
namespace ThreeFlat.Routing.Spill

/-- A family of logarithmic-cost halvers compacts a dyadically enlarged bank
with the same asymptotic bound, independent of the depth. -/
theorem dyadic_of_halvings {F : Type*} [CommSemiring F] {last c w : ℕ}
    (banks : ∀ r, last ≤ r → ∃ s : Compactor F (2*r) r w,
      s.network.cells ≤ r*(Nat.log 2 (2*r)+w+3)*c) (k : ℕ) :
    ∃ s : Compactor F (2^(k+1)*last) last w, s.network.cells ≤
      2^(k+1)*last*(Nat.log 2 (2^(k+1)*last)+w+3)*c := by
  let cap := fun i : ℕ => 2^(k+1-i)*last
  let P := fun i : ℕ => RecordPins (cap i) w
  let legal := fun (i : ℕ) (x : P i → Bool) => 2*(occupied x).card ≤ last
  let data := fun (i : ℕ) (x : P i → Bool) => payloads x
  let canon := fun (i : ℕ) (x : P i → Bool) => ZeroBlanks x
  let perSlot := (Nat.log 2 (cap 0)+w+3)*c
  have steps (i : ℕ) (hi : i ≤ k) : ∃ s : Stage F (P i) (P (i+1)),
      s.network.cells ≤ 2^(k-i)*last*perSlot ∧
      (∀ x, legal i x → ∃ y, s.run x = some y ∧ legal (i+1) y) ∧
      ∀ x y, s.run x = some y → data (i+1) y = data i x ∧ canon (i+1) y := by
    let r := cap (i+1)
    have hr : last ≤ r := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    have he : cap i = 2*r := by
      have hj : k+1-i = (k-i)+1 := by omega
      simp only [r,cap,Nat.add_sub_add_right,hj,pow_succ',Nat.mul_assoc]
    have htop : 2*r ≤ cap 0 := by
      rw [← he]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
    obtain ⟨s,hs⟩ : ∃ s : Compactor F (cap i) r w,
        s.network.cells ≤ r*(Nat.log 2 (2*r)+w+3)*c := by
      rw [he]
      exact banks r hr
    dsimp only [P,legal,data,canon]
    change ∃ s : Stage F (RecordPins (cap i) w) (RecordPins r w), _
    refine ⟨s.toStage,?_,?_,fun x y h => ⟨s.preserves x y h,s.normalized x y h⟩⟩
    · calc
        _ ≤ r*(Nat.log 2 (2*r)+w+3)*c := hs
        _ ≤ r*(Nat.log 2 (cap 0)+w+3)*c := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_left
          exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.log_mono_right htop) _) _
        _ = _ := by simp [perSlot,r,cap,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
    · intro x hx
      obtain ⟨y,hy⟩ := s.complete x (by omega)
      have hc := congrArg Multiset.card (s.preserves x y hy)
      simp only [card_payloads] at hc
      exact ⟨y,hy,by omega⟩
  obtain ⟨s,hcost,ok,transport⟩ := Stage.exists_finite_chain P k last perSlot legal data canon steps
  have out : ∃ t : Compactor F (cap 0) (cap (k+1)) w,
      t.network.cells ≤ cap 0*perSlot := by
    refine ⟨⟨s,?_,fun x y hs => (transport x y hs).1,
      fun x y hs => (transport x y hs).2⟩,?_⟩
    · intro x hx
      obtain ⟨y,hy,_⟩ := ok x (by simpa [cap,legal] using hx)
      exact ⟨y,hy⟩
    · simpa only [cap,Nat.sub_zero] using (Nat.le_add_right _ _).trans hcost
  have finalCap : cap (k+1) = last := by simp [cap]
  have padded := Eq.mp (congrArg
    (fun r => ∃ t : Compactor F (cap 0) r w, t.network.cells ≤ cap 0*perSlot) finalCap) out
  simpa only [cap,perSlot,Nat.sub_zero,Nat.mul_assoc] using padded

private def inputIndex (n : ℕ) {m w : ℕ} (j : RecordPins m w) : Option (RecordPins n w) :=
  if h : j.1.val < n then some (⟨j.1.val,h⟩,j.2) else none

private def padInput {n w : ℕ} (m : ℕ) (x : RecordPins n w → Bool) (j : RecordPins m w) :=
  ((inputIndex n j).map x).getD false

private theorem payloads_pad {n m w : ℕ} (h : n ≤ m) (x : RecordPins n w → Bool) :
    payloads (padInput m x) = payloads x := by
  have active : occupied (padInput m x) = (occupied x).map (Fin.castLEEmb h) := by
    ext i
    simp only [occupied,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
    by_cases hi : i.val < n
    · constructor
      · intro active
        exact ⟨⟨i.val,hi⟩,by simpa [padInput,inputIndex,hi] using active,Fin.ext rfl⟩
      · rintro ⟨j,hj,rfl⟩
        simpa [padInput,inputIndex] using hj
    · constructor
      · intro hf
        simp [padInput,inputIndex,hi] at hf
      · rintro ⟨j,_,he⟩
        exact (hi ((congrArg Fin.val he) ▸ j.isLt)).elim
  unfold payloads
  rw [active]
  change (((occupied x).val.map (Fin.castLEEmb h)).map _) = _
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl (fun i _ => by funext j; simp [padInput,inputIndex])

private def restrictBoard {n m r w : ℕ} {F : Type*} [CommSemiring F]
    (s : Compactor F m r w) (h : n ≤ m) : Compactor F n r w := by
  let p (j : RecordPins m w ⊕ RecordPins r w) : Option (RecordPins n w ⊕ RecordPins r w) :=
    j.elim (fun t => (inputIndex n t).map Sum.inl) (fun t => some (.inr t))
  let wire := fun j => (p ((Fintype.equivFin _).symm j)).map (Fintype.equivFin _)
  refine ⟨⟨s.network.restrictPins wire,fun x => s.run (padInput m x),?_⟩,?_,?_,
    fun _ _ hs => s.normalized _ _ hs⟩
  · intro x y
    unfold TypedWiring.value
    rw [BitNetwork.restrictPins_eval]
    refine Eq.trans (congrArg s.network.eval ?_) (s.checked (padInput m x) y)
    funext i
    obtain ⟨i,rfl⟩ := (Fintype.equivFin (RecordPins m w ⊕ RecordPins r w)).surjective i
    cases i with
    | inl j => cases he : inputIndex n j <;> simp [wire,p,padInput,he]
    | inr j => simp [wire,p]
  · intro x hx
    apply s.complete
    simpa only [← card_payloads,payloads_pad h] using hx
  · intro x y hy
    exact (s.preserves (padInput m x) y hy).trans (payloads_pad h x)

/-- Zero-padding arbitrary initial capacities to a dyadic bank costs at
most a factor of two and one additional bit in the logarithm. -/
theorem compactor_of_dyadic {F : Type*} [CommSemiring F] {n r w c : ℕ}
    (hr : 0 < r) (hrn : r ≤ n)
    (dyadic : ∀ k, ∃ s : Compactor F (2^(k+1)*r) r w,
      s.network.cells ≤ 2^(k+1)*r*(Nat.log 2 (2^(k+1)*r)+w+3)*c) :
    ∃ s : Compactor F n r w, s.network.cells ≤ n*(Nat.log 2 n+w+4)*(2*c) := by
  have power : ∃ k : ℕ, n ≤ 2^(k+1)*r ∧ 2^(k+1)*r ≤ 2*n := by
    rcases hrn.eq_or_lt with h | h
    · subst n
      exact ⟨0,by simpa using Nat.le_mul_of_pos_left r (by decide : 0 < 2),by simp⟩
    · obtain ⟨j,hj,hj'⟩ := exists_dyadic_padding hr hrn
      cases j with
      | zero => simp at hj; omega
      | succ k => exact ⟨k,hj,hj'.le⟩
  obtain ⟨k,hlo,hhi⟩ := power
  obtain ⟨s,hs⟩ := dyadic k
  refine ⟨restrictBoard s hlo,?_⟩
  change s.network.cells ≤ _
  have hl : Nat.log 2 (2^(k+1)*r) ≤ Nat.log 2 n + 1 := by
    simpa [Nat.mul_comm 2 n,Nat.log_mul_base (by decide : 1 < 2) (by omega : n ≠ 0)] using
      Nat.log_mono_right (b := 2) hhi
  calc
    _ ≤ 2^(k+1)*r*(Nat.log 2 (2^(k+1)*r)+w+3)*c := hs
    _ ≤ (2*n)*(Nat.log 2 n+w+4)*c :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hhi (by omega))
    _ = _ := by ring

end ThreeFlat.Routing.Spill

end
end OAI
