import OAI.ThreeFlat.Diagonal.LaneCursorRelay

namespace OAI
/-! # Local bucket and relay factors on the lifted cursor -/

namespace ThreeFlat.Diagonal.LaneCursor

open scoped BigOperators Classical

variable {k r : ℕ} {O D : Type*}

/-- At a vertex, unused outgoing fields must be zero. On an intermediate
layer, compare the selected outgoing bit with the selected incoming bit.
Both arc fields in the comparison are incident to this vertex. -/
def LocalChecks (mask : O → Lane (k + 1)) (fields : Fields (k + 1) r O D)
    (i : Fin (k + 1)) (lane : Lane (k + 1)) : Prop :=
  (∀ arc tag, arc ≠ selected mask tag.1 i → fields i arc lane tag = false) ∧
  ∀ prev : Fin (k + 1), i.val = prev.val + 1 → ∀ tag,
    fields i (selected mask tag.1 i) lane tag =
      fields prev (selected mask tag.1 prev) (lane - axis prev (mask tag.1 prev)) tag

theorem relayChecks_iff_local (mask : O → Lane (k + 1)) (fields : Fields (k + 1) r O D) :
    RelayChecks mask (loaded mask fields) fields ↔ ∀ i lane, LocalChecks mask fields i lane := by
  constructor
  · intro checks i lane
    refine ⟨fun arc tag h => checks.unused i arc lane tag h, ?_⟩
    intro prev step tag
    simpa only [sub_add_cancel] using
      checks.forward prev i step (lane - axis prev (mask tag.1 prev)) tag
  · intro h
    constructor
    · intro i arc lane tag
      exact (h i lane).1 arc tag
    · intro i hi source tag
      have eq : i = 0 := Fin.ext hi
      subst i
      rfl
    · intro i j step lane tag
      simpa only [add_sub_cancel_right] using
        (h j (lane + axis i (mask tag.1 i))).2 i step tag

variable {F : Type*} [CommSemiring F]

/-- Local scalar for a vertex. Bucket tensors, with their open indices fixed,
occupy the base layer. Intermediate vertices carry only the relay constraints. -/
noncomputable def vertexFactor (mask : O → Lane (k + 1))
    (bucket : Lane (k + 1) → (O × D → Bool) → (O × D → Bool) → F)
    (fields : Fields (k + 1) r O D) (i : Fin (k + 1)) (lane : Lane (k + 1)) : F := by
  classical
  exact if LocalChecks mask fields i lane then
    if i = 0 then bucket lane (loaded mask fields lane) (delivered mask fields lane) else 1
    else 0

private theorem prod_vertexFactor (mask : O → Lane (k + 1))
    (bucket : Lane (k + 1) → (O × D → Bool) → (O × D → Bool) → F)
    (fields : Fields (k + 1) r O D) :
    (∏ i, ∏ lane, vertexFactor mask bucket fields i lane) =
      (if RelayChecks mask (loaded mask fields) fields then
        ∏ lane, bucket lane (loaded mask fields lane) (delivered mask fields lane) else 0) := by
  classical
  rw [relayChecks_iff_local]
  by_cases ok : ∀ i lane, LocalChecks mask fields i lane
  · rw [ite_eq_left ok]
    have per (i : Fin (k + 1)) : (∏ lane, vertexFactor mask bucket fields i lane) =
        if i = 0 then ∏ lane, bucket lane (loaded mask fields lane) (delivered mask fields lane)
        else 1 := by
      by_cases eq : i = 0 <;> simp [vertexFactor, ok, eq]
    simp_rw [per]
    simp
  · rw [ite_eq_right ok]
    push Not at ok
    obtain ⟨i, lane, fail⟩ := ok
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ lane)
    simp [vertexFactor, fail]

/-- Summing the physical arc labels and multiplying the local tensors computes
the original contraction among buckets with the public XOR offsets. -/
theorem contract_bucket_factors [Fintype O] [Fintype D] [DecidableEq O] [DecidableEq D] (mask : O → Lane (k + 1))
    (bucket : Lane (k + 1) → (O × D → Bool) → (O × D → Bool) → F) :
    (∑ fields : Fields (k + 1) r O D, ∏ i, ∏ lane, vertexFactor mask bucket fields i lane) =
      ∑ m : Lane (k + 1) → O × D → Bool,
        ∏ lane, bucket lane (m lane) (fun tag => m (lane - mask tag.1) tag) := by
  classical
  simp_rw [prod_vertexFactor]
  exact contract_cycle mask (fun send receive => ∏ lane, bucket lane (send lane) (receive lane))

end ThreeFlat.Diagonal.LaneCursor

end OAI
