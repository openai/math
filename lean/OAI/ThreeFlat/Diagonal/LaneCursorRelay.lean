import OAI.ThreeFlat.Diagonal.LaneCursor
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Relaying the bits of a bucket message

One wire slot is reserved for each public offset and payload position.
For a given slot the first parallel arc of the selected branch carries the
source bit. Every unselected branch and every spare copy is fixed to zero.
The equations at the relays have a unique solution for fixed source bits.
-/

namespace ThreeFlat.Diagonal.LaneCursor

open scoped BigOperators Classical

variable {k r : ℕ} {O D : Type*}

/-- Physical slot number for the public offset, at the outgoing cursor position.
Copy zero carries its payload. -/
def selected (mask : O → Lane k) (o : O) (i : Fin k) : Fin ((r + 1) * 2) :=
  finProdFinEquiv ((0 : Fin (r + 1)), mask o i)

/-- Each physical arc carries one Boolean value per pair (offset, payload address). -/
abbrev Fields (k r : ℕ) (O D : Type*) :=
  Fin k → Fin ((r + 1) * 2) → Lane k → O × D → Bool

noncomputable instance fieldsFintype [Fintype O] [Fintype D] :
    Fintype (Fields k r O D) := by
  classical
  letI : Fintype (O × D → Bool) := Pi.instFintype
  letI : Fintype (Lane k → O × D → Bool) := Pi.instFintype
  letI : Fintype (Fin ((r + 1) * 2) → Lane k → O × D → Bool) := Pi.instFintype
  exact Pi.instFintype

/-- Fill a reserved arc slot from its unique source. -/
def arcFields (mask : O → Lane k) (messages : Lane k → O × D → Bool) : Fields k r O D :=
  fun i arc lane tag =>
    if arc = selected mask tag.1 i then messages ((stage (mask tag.1) i.val).symm lane) tag
    else false

theorem arcFields_on_route (mask : O → Lane k) (m : Lane k → O × D → Bool)
    (i : Fin k) (tag : O × D) (source : Lane k) :
    arcFields (r := r) mask m i (selected mask tag.1 i) (stage (mask tag.1) i.val source) tag =
      m source tag := by simp [arcFields]

/-- Zero checks on unused slots, loading at the first layer, and pairwise
equality between the incoming and outgoing fields at intermediate relays. -/
structure RelayChecks (mask : O → Lane k) (messages : Lane k → O × D → Bool)
    (fields : Fields k r O D) : Prop where
  unused : ∀ i arc lane tag, arc ≠ selected mask tag.1 i → fields i arc lane tag = false
  load : ∀ i : Fin k, i.val = 0 → ∀ source tag,
    fields i (selected mask tag.1 i) source tag = messages source tag
  forward : ∀ i j : Fin k, j.val = i.val + 1 → ∀ lane tag,
    fields j (selected mask tag.1 j) (lane + axis i (mask tag.1 i)) tag =
      fields i (selected mask tag.1 i) lane tag

private theorem canonical_checks (mask : O → Lane k) (m : Lane k → O × D → Bool) :
    RelayChecks mask m (arcFields (r := r) mask m) := by
  constructor
  · intro i arc lane tag unused
    simp [arcFields, unused]
  · intro i hi source tag
    simpa [hi] using arcFields_on_route (r := r) mask m i tag source
  · intro i j hj lane tag
    let source := (stage (mask tag.1) i.val).symm lane
    have h₁ : stage (mask tag.1) i.val source = lane :=
      (stage (mask tag.1) i.val).apply_symm_apply lane
    have h₂ : stage (mask tag.1) j.val source = lane + axis i (mask tag.1 i) := by
      rw [hj, stage_next, h₁]
    rw [← h₂, arcFields_on_route, ← h₁, arcFields_on_route]

/-- Fixed messages have exactly one extension to the physical arc fields.
The constraints involve only an arc or the two adjacent arcs at one vertex. -/
theorem relayChecks_iff (mask : O → Lane k) (m : Lane k → O × D → Bool)
    (fields : Fields k r O D) : RelayChecks mask m fields ↔ fields = arcFields mask m := by
  refine ⟨fun checks => ?_, fun eq => eq ▸ canonical_checks mask m⟩
  have along : ∀ t (ht : t < k) (source : Lane k) (tag : O × D),
      let i : Fin k := ⟨t, ht⟩
      fields i (selected mask tag.1 i) (stage (mask tag.1) i.val source) tag = m source tag := by
    intro t
    induction t with
    | zero =>
      intro ht source tag
      simpa using checks.load ⟨0, ht⟩ rfl source tag
    | succ t ih =>
      intro ht source tag
      let i : Fin k := ⟨t, by omega⟩
      let j : Fin k := ⟨t + 1, ht⟩
      change fields j _ (stage (mask tag.1) (i.val + 1) source) tag = _
      rw [stage_next, checks.forward i j rfl]
      exact ih i.isLt source tag
  funext i arc lane tag
  by_cases active : arc = selected mask tag.1 i
  · subst arc
    simpa [arcFields] using along i.val i.isLt ((stage (mask tag.1) i.val).symm lane) tag
  · rw [checks.unused i arc lane tag active]
    simp [arcFields, active]

/-- Contracting all accepted extensions gives precisely the value obtained
by putting the routed messages directly on their prescribed endpoints. -/
theorem sum_relay_checks {R : Type*} [AddCommMonoid R] [Fintype O] [Fintype D] [DecidableEq O] [DecidableEq D]
    (mask : O → Lane k) (m : Lane k → O × D → Bool) (f : Fields k r O D → R) :
    (∑ fields, if RelayChecks mask m fields then f fields else 0) =
      f (arcFields mask m) := by
  classical
  simp_rw [relayChecks_iff]
  simp

/-- Read the outgoing source bit at cursor zero. -/
def loaded (mask : O → Lane (k + 1)) (fields : Fields (k + 1) r O D)
    (source : Lane (k + 1)) (tag : O × D) : Bool :=
  fields 0 (selected mask tag.1 0) source tag

/-- The last selected arc enters cursor zero at the target lane. -/
def delivered (mask : O → Lane (k + 1)) (fields : Fields (k + 1) r O D)
    (target : Lane (k + 1)) (tag : O × D) : Bool :=
  let last := Fin.last k
  fields last (selected mask tag.1 last) (target - axis last (mask tag.1 last)) tag

@[simp] theorem loaded_arcFields (mask : O → Lane (k + 1))
    (m : Lane (k + 1) → O × D → Bool) : loaded mask (arcFields (r := r) mask m) = m := by
  funext source tag
  simpa [loaded] using arcFields_on_route (r := r) mask m 0 tag source

theorem delivered_arcFields (mask : O → Lane (k + 1)) (m : Lane (k + 1) → O × D → Bool)
    (target : Lane (k + 1)) (tag : O × D) :
    delivered mask (arcFields (r := r) mask m) target tag = m (target - mask tag.1) tag := by
  let source := target - mask tag.1
  let last := Fin.last k
  have final := stage_next (mask tag.1) source last
  change stage (mask tag.1) (k + 1) source = stage (mask tag.1) k source + _ at final
  rw [stage_end] at final
  have endpoint : source + mask tag.1 = target := sub_add_cancel ..
  rw [endpoint] at final
  change arcFields (r := r) mask m last _ (target - axis last (mask tag.1 last)) tag = _
  nth_rw 1 [final]
  rw [add_sub_cancel_right]
  exact arcFields_on_route mask m last tag source

private theorem checks_loaded (mask : O → Lane (k + 1)) (m : Lane (k + 1) → O × D → Bool)
    (fields : Fields (k + 1) r O D) :
    RelayChecks mask m fields ↔ loaded mask fields = m ∧ RelayChecks mask (loaded mask fields) fields := by
  refine ⟨fun check => ?_, ?_⟩
  · have eq : loaded mask fields = m := by
      funext s tag
      exact check.load 0 rfl s tag
    exact ⟨eq, eq.symm ▸ check⟩
  · rintro ⟨rfl, check⟩
    exact check

/-- Contract the actual arc variables of one entire cycle. The bucket
factors at position zero see exactly the sent bits and the bits received
from their XOR partners. All internal relays have weight one on a valid
assignment and zero on an invalid assignment. -/
theorem contract_cycle {R : Type*} [AddCommMonoid R] [Fintype O] [Fintype D] [DecidableEq O] [DecidableEq D]
    (mask : O → Lane (k + 1))
    (value : (Lane (k + 1) → O × D → Bool) → (Lane (k + 1) → O × D → Bool) → R) :
    (∑ fields : Fields (k + 1) r O D, if RelayChecks mask (loaded mask fields) fields then
      value (loaded mask fields) (delivered mask fields) else 0) =
      ∑ m, value m (fun target tag => m (target - mask tag.1) tag) := by
  classical
  let eval := fun fields : Fields (k + 1) r O D =>
    value (loaded mask fields) (delivered mask fields)
  calc
    _ = ∑ fields, ∑ m, if RelayChecks mask m fields then eval fields else 0 := by
      apply Finset.sum_congr rfl
      intro fields _
      by_cases h : RelayChecks mask (loaded mask fields) fields
      · have test (m) : RelayChecks mask m fields ↔ loaded mask fields = m := by
          simpa only [h, and_true] using checks_loaded mask m fields
        rw [ite_eq_left h]
        simp only [test, Finset.sum_ite_eq, Finset.mem_univ, ite_true, eval]
      · have test (m) : ¬RelayChecks mask m fields :=
          fun ok => h ((checks_loaded mask m fields).mp ok).2
        simp [h, test]
    _ = ∑ m, ∑ fields, if RelayChecks mask m fields then eval fields else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      rw [sum_relay_checks]
      simp only [eval, loaded_arcFields]
      exact congrArg (value m) (funext fun target => funext fun tag =>
        delivered_arcFields (r := r) mask m target tag)

/-- The per-arc address consists of one low row, a public offset, an
exchange kind and a bit position. -/
theorem arc_width (offsets rows kinds bits : ℕ) :
    Fintype.card (Fin offsets × (Fin rows × Fin kinds × Fin bits)) =
      rows * (offsets * kinds * bits) := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ac_rfl

theorem arc_width_polynomial {offsets rows kinds bits w u v z : ℕ}
    (ho : offsets ≤ w ^ u) (hc : kinds ≤ w ^ v) (hb : bits ≤ w ^ z) :
    Fintype.card (Fin offsets × (Fin rows × Fin kinds × Fin bits)) ≤ rows * w ^ (u + v + z) := by
  rw [arc_width, Nat.pow_add, Nat.pow_add]
  exact Nat.mul_le_mul_left rows (Nat.mul_le_mul (Nat.mul_le_mul ho hc) hb)

end ThreeFlat.Diagonal.LaneCursor

end OAI
