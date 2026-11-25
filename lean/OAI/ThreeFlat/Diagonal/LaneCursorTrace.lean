import OAI.ThreeFlat.Diagonal.LaneCursorLayout
import OAI.ThreeFlat.Diagonal.LaneCursorContraction

namespace OAI
/-! # Contracting a row-addressed trace on the lane cursor

Each hidden bit is guessed at its own bucket. Each outgoing reservation
contains the requested bit or zero for an unused address. The receiving
bucket reads the corresponding slot to evaluate its local tensor entries.
The resulting network of bucket and relay factors has the same scalar as
the original bit network on all input pins.
-/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout

open scoped BigOperators Classical

variable {F : Type*} [CommSemiring F] {p k low offsets slots : ℕ}
variable {N : BitNetwork F p} (P : RowLayout N (k + 1) low offsets slots)

omit [CommSemiring F] in
/-- The outgoing field of a bucket depends only on its owned hidden bits
and pins. -/
theorem emitted_local (pin₁ pin₂ : Fin p → Bool) (h₁ h₂ : Fin N.internal → Bool) (lane : Lane (k + 1))
    (hp : ∀ j, (splitRow _ _ (P.pinRow j)).1 = lane → pin₁ j = pin₂ j)
    (hh : ∀ i, (splitRow _ _ (P.hiddenRow i)).1 = lane → h₁ i = h₂ i) :
    P.emitted pin₁ h₁ lane = P.emitted pin₂ h₂ lane := by
  funext tag
  by_cases used : ∃ e, P.key e = (lane, tag)
  · obtain ⟨e, eq⟩ := used
    have hl : P.ownerLane e = lane := congrArg
      (fun z : Lane (k + 1) × (Fin offsets × PayloadAddress low slots) => z.1) eq
    have ht : P.tag e = tag := congrArg
      (fun z : Lane (k + 1) × (Fin offsets × PayloadAddress low slots) => z.2) eq
    rw [← hl, ← ht, emitted_wire, emitted_wire]
    cases src : N.source e.val.1 e.val.2 with
    | hidden i => exact hh i (by simpa [ownerLane, owner, sourceRow, src] using hl)
    | pin j => exact hp j (by simpa [ownerLane, owner, sourceRow, src] using hl)
    | constant b => rfl
  · rw [P.emitted_unused pin₁ h₁ _ _ used, P.emitted_unused pin₂ h₂ _ _ used]

/-- The cells on a lane with outgoing bits fixed by a hidden assignment. -/
noncomputable def bucket (pin : Fin p → Bool) (h : Fin N.internal → Bool)
    (lane : Lane (k + 1)) (send receive : Fin offsets × PayloadAddress low slots → Bool) : F :=
  if send = P.emitted pin h lane then
    ∏ c : {c // P.cellLane c = lane}, N.table c.val (P.argument receive c.val)
  else 0

private theorem wire_sum (pin : Fin p → Bool) (h : Fin N.internal → Bool) :
    (∑ msgs : Lane (k + 1) → Fin offsets × PayloadAddress low slots → Bool,
      ∏ lane, P.bucket pin h lane (msgs lane)
      (fun tag => msgs (lane - P.mask tag.1) tag)) = N.weight pin h := by
  rw [Finset.sum_eq_single (P.emitted pin h)]
  · simp only [bucket]
    calc
      _ = ∏ lane, ∏ c : {c // P.cellLane c = lane}, N.factor pin h c.val := by
        apply Finset.prod_congr rfl
        intro lane _
        apply Finset.prod_congr rfl
        intro c _
        apply congrArg (N.table c.val)
        funext j
        simpa only [c.property] using P.argument_delivered pin h c.val j
      _ = N.weight pin h := Fintype.prod_fiberwise _ _
  · intro msgs _ unequal
    have hd : ¬ ∀ lane, msgs lane = P.emitted pin h lane := fun eq => unequal (funext eq)
    push Not at hd
    obtain ⟨lane, diff⟩ := hd
    apply Finset.prod_eq_zero (Finset.mem_univ lane)
    simp [bucket, diff]
  · simp

/-- Hidden variables partition by their unique owning lane. -/
abbrev LocalHidden (lane : Lane (k + 1)) :=
  {i : Fin N.internal // (splitRow _ _ (P.hiddenRow i)).1 = lane} → Bool

/-- Reindex global hidden assignments by independent local assignments. -/
def splitHidden : (Fin N.internal → Bool) ≃ ((lane : Lane (k + 1)) → P.LocalHidden lane) where
  toFun h _lane i := h i.val
  invFun f i := f _ ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv f := by
    funext lane i
    obtain ⟨i, hi⟩ := i
    subst lane
    rfl

/-- Extend a local hidden assignment with padding outside its lane. -/
def padHidden (lane : Lane (k + 1)) (bits : P.LocalHidden lane) (i : Fin N.internal) : Bool :=
  if eq : (splitRow _ _ (P.hiddenRow i)).1 = lane then bits ⟨i, eq⟩ else false

/-- The tensor at a bucket sums only over its owned hidden bits. -/
noncomputable def localTensor (pin : Fin p → Bool) (lane : Lane (k + 1))
    (send receive : Fin offsets × PayloadAddress low slots → Bool) : F :=
  ∑ bits : P.LocalHidden lane, P.bucket pin (P.padHidden lane bits) lane send receive

/-- The bucket has no dependence on external pins assigned to other lanes. -/
theorem localTensor_pins (pin₁ pin₂ : Fin p → Bool) (lane : Lane (k + 1))
    (hp : ∀ j, (splitRow _ _ (P.pinRow j)).1 = lane → pin₁ j = pin₂ j) :
    P.localTensor pin₁ lane = P.localTensor pin₂ lane := by
  funext send receive
  apply Finset.sum_congr rfl
  intro bits _
  have same := P.emitted_local pin₁ pin₂ (P.padHidden lane bits) (P.padHidden lane bits)
    lane hp (fun _ _ => rfl)
  simp only [bucket, same]

omit [CommSemiring F] in
/-- Paired row and column pins placed in one trace row have a unique common
bucket, including when that row is at a bucket boundary. -/
theorem paired_pin_bucket {rowPin colPin : Fin p} (same : P.pinRow rowPin = P.pinRow colPin) :
    ∃! lane : Lane (k + 1),
      (splitRow _ _ (P.pinRow rowPin)).1 = lane ∧ (splitRow _ _ (P.pinRow colPin)).1 = lane := by
  rw [same]
  exact ⟨_, ⟨rfl, rfl⟩, fun _ h => h.1.symm⟩

private theorem bucket_padded (pin : Fin p → Bool) (h : Fin N.internal → Bool)
    (lane : Lane (k + 1)) (send receive : Fin offsets × PayloadAddress low slots → Bool) :
    P.bucket pin (P.padHidden lane (P.splitHidden h lane)) lane send receive =
      P.bucket pin h lane send receive := by
  have same := P.emitted_local pin pin (P.padHidden lane (P.splitHidden h lane)) h lane
    (fun _ _ => rfl) (by intro i eq; simp [padHidden, eq, splitHidden])
  simp only [bucket, same]

/-- Each row-addressed bit network has an exact contraction on the cursor.
The independent external input pins are parameters of the local tensors. -/
theorem eval_cursor {r : ℕ} (pin : Fin p → Bool) :
    (∑ fields : Fields (k + 1) r (Fin offsets) (PayloadAddress low slots),
      ∏ i, ∏ lane, vertexFactor P.mask (P.localTensor pin) fields i lane) = N.eval pin := by
  rw [contract_bucket_factors]
  simp only [localTensor, Fintype.prod_sum]
  rw [Finset.sum_comm]
  rw [← P.splitHidden.sum_comp]
  simp only [bucket_padded]
  simp_rw [wire_sum]
  rfl

end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
