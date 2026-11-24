import OAI.Computability.VPVNP.RAMPathCount
import Mathlib.Data.LawfulXor.Equiv

/-!
# Routing the transcript fields on the cursor graph

In §12 of *VP and VNP differ over every field*, each site address traverses the cursor cycle
once per message system. It flips the current bit exactly when the system's mask specifies
that bit. At intermediate cursors every field comes from a unique sender. Unused arcs are
clamped, used arcs carry equal payloads at consecutive positions, and the returning arc
supplies the receiving validator. These local checks preserve the contraction exactly.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorRouting

/-- A binary word of width `D` used to address a site. -/
abbrev Site (D : ℕ) := Fin (2 ^ D)

variable {D : ℕ}

private def lowMask (mask : Site D) (k : ℕ) : Site D :=
  ⟨mask.val % 2 ^ k, lt_of_le_of_lt (Nat.mod_le _ _) mask.isLt⟩

private def bitMask (j : Fin D) : Site D :=
  ⟨2 ^ j.val, Nat.pow_lt_pow_right (by decide) j.isLt⟩

/-- Location at cursor `k` under the route that flips the bits set in `mask`. -/
def routePos (mask : Site D) (k : ℕ) : Equiv.Perm (Site D) :=
  Equiv.xor (lowMask mask k)

theorem routePos_val (mask : Site D) (k : ℕ) (x : Site D) :
    (routePos mask k x).val = x.val ^^^ (mask.val % 2 ^ k) := by
  rw [routePos, Equiv.xor_apply, Fin.xor_comm, Fin.xor_val,
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.isLt (lowMask mask k).isLt)]
  rfl

@[simp] theorem routePos_zero (mask : Site D) (x : Site D) : routePos mask 0 x = x := by
  apply Fin.ext
  simp [routePos_val, Nat.mod_one]

theorem routePos_full_val (mask x : Site D) : (routePos mask D x).val = x.val ^^^ mask.val := by
  rw [routePos_val, Nat.mod_eq_of_lt mask.isLt]

theorem routePos_symm_full_val (mask x : Site D) :
    ((routePos mask D).symm x).val = x.val ^^^ mask.val :=
  routePos_full_val mask x

/-- One arc of the cursor graph, either staying at `x` or flipping bit `j`. -/
def stepSite (j : Fin D) (flip : Bool) (x : Site D) : Site D :=
  if flip then x ^^^ bitMask j else x

@[simp] theorem stepSite_false (j : Fin D) (x : Site D) : stepSite j false x = x := rfl

theorem stepSite_true_val (j : Fin D) (x : Site D) :
    (stepSite j true x).val = x.val ^^^ 2 ^ j.val := by
  change (x ^^^ bitMask j).val = _
  rw [Fin.xor_val, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.isLt (bitMask j).isLt)]
  rfl

private theorem lowMask_succ_val (mask : Site D) (j : Fin D) :
    mask.val % 2 ^ (j.val + 1) =
      (mask.val % 2 ^ j.val) ^^^ (if mask.val.testBit j.val then 2 ^ j.val else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases lt_trichotomy i j.val with h | h | h
  · have hne := Ne.symm h.ne
    cases mask.val.testBit j.val <;> simp [h, Nat.lt_succ_of_lt h, hne]
  · subst i
    cases hb : mask.val.testBit j.val <;> simp [hb]
  · have hn : ¬ i < j.val + 1 := by omega
    have hn' : ¬ i < j.val := by omega
    cases mask.val.testBit j.val <;> simp [hn, hn', h.ne]

theorem routePos_step (mask : Site D) (j : Fin D) (x : Site D) :
    routePos mask (j.val + 1) x = stepSite j (mask.val.testBit j.val) (routePos mask j.val x) := by
  apply Fin.ext
  rw [routePos_val, lowMask_succ_val, ← Nat.xor_assoc]
  cases h : mask.val.testBit j.val with
  | false => simp [routePos_val]
  | true =>
    simp only [ite_true, stepSite_true_val, routePos_val]

/-- Incrementing a binary address changes exactly its trailing ones and the zero preceding them. -/
theorem successor_mask_eq {D x : ℕ} (hx : x + 1 < 2 ^ D) :
    ∃ k : Fin D, x ^^^ (x + 1) = 2 ^ (k.val + 1) - 1 := by
  induction D generalizing x with
  | zero => simp at hx
  | succ D ih =>
    let y := x / 2
    rcases Nat.mod_two_eq_zero_or_one x with heven | hodd
    · have hx₀ : x = Nat.bit false y := by simp only [Nat.bit_false, y]; omega
      have hx₁ : x + 1 = Nat.bit true y := by rw [hx₀, Nat.bit_false, Nat.bit_true]
      exact ⟨0, by rw [hx₁, hx₀, Nat.xor_bit, Nat.xor_self]; rfl⟩
    · have hx₀ : x = Nat.bit true y := by simp only [Nat.bit_true, y]; omega
      have hx₁ : x + 1 = Nat.bit false (y + 1) := by
        simp only [hx₀, Nat.bit_true, Nat.bit_false]
        omega
      have hy : y + 1 < 2 ^ D := by
        simp only [hx₁, Nat.bit_false, Nat.pow_succ] at hx
        omega
      obtain ⟨k, hk⟩ := ih hy
      refine ⟨k.succ, ?_⟩
      rw [hx₁, hx₀, Nat.xor_bit, hk]
      change 2 * (2 ^ (k.val + 1) - 1) + 1 = 2 ^ ((k.val + 1) + 1) - 1
      rw [Nat.pow_succ _ (k.val + 1)]
      have := Nat.two_pow_pos (k.val + 1)
      omega

/-- The masks of all nonwrapping successor messages in a graph with `D` address bits. -/
def successorMasks (D : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ D - 1)).image fun x => x ^^^ (x + 1)

/-- Section 12's partition of successor messages uses at most one mask per address bit. -/
theorem card_successorMasks_le (D : ℕ) : (successorMasks D).card ≤ D := by
  let possible := (Finset.range D).image fun k => 2 ^ (k + 1) - 1
  have hsub : successorMasks D ⊆ possible := by
    intro m hm
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
    have hx' := Finset.mem_range.mp hx
    obtain ⟨k, hk⟩ := successor_mask_eq (D := D) (x := x) (by omega)
    exact Finset.mem_image.mpr ⟨k.val, Finset.mem_range.mpr k.isLt, hk.symm⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (Finset.card_range D).le)

variable {D : ℕ} [NeZero D] {B : Type*}

/-- Fields on the two outgoing arc choices of every processor and cursor. Each
communication system gets its own instance of these fields. -/
abbrev ArcFields (D : ℕ) (B : Type*) := Fin D → Site D → Bool → B

/-- Both outgoing arcs advance the cursor cyclically. The flip arc additionally
changes the current cursor bit of the processor. -/
def arcTarget (x : Site D) (j : Fin D) (flip : Bool) : Site D × Fin D :=
  (stepSite j flip x, Fin.ofNat D (j.val + 1))

/-- The pointwise equalities checked at the routing vertices. Unselected arc choices
are clamped to `blank`. A message can itself be blank when its sender is inactive. -/
structure LocalTies (blank : B) (mask : Site D) (send receive : Site D → B)
    (fields : ArcFields D B) : Prop where
  clamp : ∀ j x side, side ≠ mask.val.testBit j.val → fields j x side = blank
  start : ∀ x, fields 0 x (mask.val.testBit 0) = send x
  transit : ∀ (j k : Fin D), k.val = j.val + 1 → ∀ x,
    fields k (stepSite j (mask.val.testBit j.val) x) (mask.val.testBit k.val) =
      fields j x (mask.val.testBit j.val)
  arrival : ∀ j : Fin D, j.val + 1 = D → ∀ x,
    receive (stepSite j (mask.val.testBit j.val) x) = fields j x (mask.val.testBit j.val)

/-- Pull each used field back along the prefix permutation to its unique sender. -/
def routedFields (blank : B) (mask : Site D) (send : Site D → B) : ArcFields D B :=
  fun j x side => if side = mask.val.testBit j.val then send ((routePos mask j.val).symm x)
    else blank

omit [NeZero D] in
private theorem routedFields_at (blank : B) (mask : Site D) (send : Site D → B)
    (j : Fin D) (x : Site D) :
    routedFields blank mask send j (routePos mask j.val x) (mask.val.testBit j.val) = send x := by
  simp [routedFields]

theorem routedFields_localTies (blank : B) (mask : Site D) (send receive : Site D → B)
    (h : ∀ x, receive (routePos mask D x) = send x) :
    LocalTies blank mask send receive (routedFields blank mask send) := by
  constructor
  · intro j x side hs
    simp [routedFields, hs]
  · intro x
    simpa [routePos_zero] using routedFields_at blank mask send (0 : Fin D) x
  · intro j k hstep y
    obtain ⟨x, rfl⟩ := (routePos mask j.val).surjective y
    rw [← routePos_step, ← hstep, routedFields_at, routedFields_at]
  · intro j hj y
    obtain ⟨x, rfl⟩ := (routePos mask j.val).surjective y
    rw [← routePos_step, hj, h, routedFields_at]

/-- Following the local equalities from the sender determines each used field. -/
theorem LocalTies.field_at {blank : B} {mask : Site D} {send receive : Site D → B}
    {fields : ArcFields D B} (h : LocalTies blank mask send receive fields)
    (j : Fin D) (x : Site D) :
    fields j (routePos mask j.val x) (mask.val.testBit j.val) = send x := by
  obtain ⟨k, hk⟩ := j
  induction k with
  | zero =>
    rw [routePos_zero]
    exact h.start x
  | succ k ih =>
    let i : Fin D := ⟨k, by omega⟩
    let j : Fin D := ⟨k + 1, hk⟩
    change fields j (routePos mask (i.val + 1) x) (mask.val.testBit j.val) = send x
    rw [routePos_step, h.transit i j rfl]
    exact ih i.isLt

theorem LocalTies.receive_at {blank : B} {mask : Site D} {send receive : Site D → B}
    {fields : ArcFields D B} (h : LocalTies blank mask send receive fields) (x : Site D) :
    receive (routePos mask D x) = send x := by
  have hd : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  let j : Fin D := ⟨D - 1, by omega⟩
  have hj : j.val + 1 = D := by dsimp [j]; omega
  calc
    receive (routePos mask D x) =
        receive (stepSite j (mask.val.testBit j.val) (routePos mask j.val x)) := by
      rw [← routePos_step, hj]
    _ = fields j (routePos mask j.val x) (mask.val.testBit j.val) := h.arrival j hj _
    _ = send x := h.field_at j x

theorem LocalTies.fields_eq {blank : B} {mask : Site D} {send receive : Site D → B}
    {fields : ArcFields D B} (h : LocalTies blank mask send receive fields) :
    fields = routedFields blank mask send := by
  funext j y side
  obtain ⟨x, rfl⟩ := (routePos mask j.val).surjective y
  by_cases hs : side = mask.val.testBit j.val
  · subst side
    rw [h.field_at, routedFields_at]
  · rw [h.clamp _ _ _ hs]
    simp [routedFields, hs]

/-- Prescribed sends and receives extend uniquely exactly when their endpoints match. -/
theorem existsUnique_fields_iff (blank : B) (mask : Site D) (send receive : Site D → B) :
    (∃! f : ArcFields D B, LocalTies blank mask send receive f) ↔
      ∀ x, receive (routePos mask D x) = send x := by
  constructor
  · rintro ⟨_, h, _⟩
    exact h.receive_at
  · intro h
    exact ⟨_, routedFields_localTies blank mask send receive h, fun _ hg => hg.fields_eq⟩

/-- After assigning a separate routed field to each mask system, summing over all
route bits and checking their ties leaves the original contraction unchanged. -/
theorem contraction_eq {A S R : Type*} [Fintype A] [Fintype S] [AddCommMonoid R]
    {P : S → Type*} [∀ s, Fintype (P s)] (blank : ∀ s, P s) (mask : S → Site D)
    (send receive : A → ∀ s, Site D → P s)
    (hcompat : ∀ a s x, receive a s (routePos (mask s) D x) = send a s x) (weight : A → R) :
    open scoped Classical in
    ∑ a : A, ∑ f : (s : S) → ArcFields D (P s),
      (if ∀ s, LocalTies (blank s) (mask s) (send a s) (receive a s) (f s) then weight a else 0) =
      ∑ a : A, weight a := by
  classical
  refine Finset.sum_congr rfl fun a _ => ?_
  let f : (s : S) → ArcFields D (P s) := fun s => routedFields (blank s) (mask s) (send a s)
  have hf (s : S) : LocalTies (blank s) (mask s) (send a s) (receive a s) (f s) :=
    routedFields_localTies _ _ _ _ (hcompat a s)
  rw [Finset.sum_eq_single f, ite_eq_left hf]
  · intro g _ hne
    apply ite_eq_right
    intro hg
    exact hne (funext fun s => (hg s).fields_eq)
  · simp

/-- Sum over the routed fields, giving zero to a setting that fails to carry
any consistent source assignment. -/
noncomputable def routedContraction {A S R : Type*} [Fintype S] [AddCommMonoid R]
    {P : S → Type*} [∀ s, Fintype (P s)] (blank : ∀ s, P s) (mask : S → Site D)
    (send receive : A → ∀ s, Site D → P s) (weight : A → R) : R := by
  classical
  exact ∑ f : (s : S) → ArcFields D (P s),
    if h : ∃ a, ∀ s, LocalTies (blank s) (mask s) (send a s) (receive a s) (f s)
    then weight h.choose else 0

/-- When the send fields recover the old assignment, the contraction can be indexed
solely by routed arc fields. The clamps and ties discard all invalid settings. -/
theorem routed_contraction_eq {A S R : Type*} [Fintype A] [Fintype S] [AddCommMonoid R]
    {P : S → Type*} [∀ s, Fintype (P s)] (blank : ∀ s, P s) (mask : S → Site D)
    (send receive : A → ∀ s, Site D → P s) (hinj : Function.Injective send)
    (hcompat : ∀ a s x, receive a s (routePos (mask s) D x) = send a s x) (weight : A → R) :
    routedContraction blank mask send receive weight = ∑ a : A, weight a := by
  classical
  unfold routedContraction
  rw [← contraction_eq blank mask send receive hcompat weight, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : ∃ a, ∀ s, LocalTies (blank s) (mask s) (send a s) (receive a s) (f s)
  · rw [dite_eq_left h, Finset.sum_eq_single h.choose, ite_eq_left h.choose_spec]
    · intro b _ hb
      apply ite_eq_right
      intro hties
      exact hb (hinj (funext fun s => funext fun x =>
        ((hties s).start x).symm.trans ((h.choose_spec s).start x)))
    · simp
  · rw [dite_eq_right h]
    symm
    exact Finset.sum_eq_zero fun a _ => ite_eq_right (fun ha => h ⟨a, ha⟩)

end CursorRouting

namespace CursorRouting

variable {D H w : ℕ}

/-- A successor mask class, or a cross-site layer of the sorting network. -/
abbrev RAMSystem (D : ℕ) := Fin D ⊕ RAMLayout.Layer D

/-- Every system uses its own field on both choices of arc at each cursor. -/
def ramFieldBits (H w : ℕ) : RAMSystem D → ℕ
  | .inl _ => 8 * w
  | .inr _ => RAMLayout.blockBits H w

/-- Exact number of processor-cursor positions before compression. -/
theorem cursorPositions_card (D : ℕ) : Fintype.card (Site D × Fin D) = 2 ^ D * D := by
  simp [Site]

/-- Width of one of the two cursor arcs when both reserve a field for every system. -/
theorem ramArcWidth (D H w : ℕ) : ∑ s : RAMSystem D, ramFieldBits H w s =
    D * (8 * w) + RAMLayout.layerCount D * RAMLayout.blockBits H w := by
  have hcard : Fintype.card (RAMLayout.Layer D) = RAMLayout.layerCount D := by
    simpa using Fintype.card_congr (RAMLayout.layerEquiv D)
  rw [Fintype.sum_sum_type]
  simp [ramFieldBits, hcard]

/-- A successor class flips a low-bit prefix. A sorting layer flips one site bit. -/
def systemMask : RAMSystem D → Site D
  | .inl k => ⟨2 ^ (k.val + 1) - 1, by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) k.isLt
      have := Nat.two_pow_pos (k.val + 1)
      omega⟩
  | .inr s => ⟨2 ^ s.siteBit, Nat.pow_lt_pow_right (by decide) s.siteBit_lt⟩

private theorem log_successorMask {x : ℕ} {k : Fin D}
    (h : x ^^^ (x + 1) = 2 ^ (k.val + 1) - 1) :
    ((x ^^^ (x + 1)) + 1).log2 - 1 = k.val := by
  have hp := Nat.two_pow_pos (k.val + 1)
  rw [h, Nat.sub_add_cancel hp, Nat.log2_two_pow]
  omega

/-- The unique mask class of a nonwrapping successor edge, computed from its sender. -/
def successorClass {x : ℕ} (h : x + 1 < 2 ^ D) : Fin D :=
  ⟨((x ^^^ (x + 1)) + 1).log2 - 1, by
    obtain ⟨k, hk⟩ := successor_mask_eq h
    exact (log_successorMask hk) ▸ k.isLt⟩

theorem successorClass_eq_iff {x : ℕ} (h : x + 1 < 2 ^ D) (k : Fin D) :
    successorClass h = k ↔ x ^^^ (x + 1) = (systemMask (.inl k)).val := by
  constructor
  · obtain ⟨i, hi⟩ := successor_mask_eq h
    intro hk
    have hi' : successorClass h = i := Fin.ext (log_successorMask hi)
    exact hk ▸ hi' ▸ hi
  · exact fun hk ↦ Fin.ext (log_successorMask hk)

/-- At an active successor source the route uses the corresponding physical
send. At the last site and in other classes its source is the all-zero field. -/
def ramSend (a : RAMLayout.SendArrays D H w) :
    (s : RAMSystem D) → Site D → Fin (ramFieldBits H w s) → Bool
  | .inl k, x, j =>
    if h : x.val + 1 < 2 ^ D ∧ x.val ^^^ (x.val + 1) = (systemMask (.inl k)).val
    then a.1 ⟨x.val, by omega⟩ j else false
  | .inr s, x, j => a.2 s x j

/-- An arrival reads the source identified by the inverse cursor permutation. -/
def ramReceive (a : RAMLayout.SendArrays D H w) (s : RAMSystem D) (y : Site D) :
    Fin (ramFieldBits H w s) → Bool := ramSend a s ((routePos (systemMask s) D).symm y)

@[simp] theorem ramReceive_at (a : RAMLayout.SendArrays D H w) (s : RAMSystem D) (x : Site D) :
    ramReceive a s (routePos (systemMask s) D x) = ramSend a s x := by simp [ramReceive]

theorem ramSend_sort (a : RAMLayout.SendArrays D H w) (s : RAMLayout.Layer D) (x : Site D)
    (j : Fin (RAMLayout.blockBits H w)) :
    ramSend a (.inr s) x j = (RAMLayout.incidentEquiv D H w a).val (x, .inr (s, 0, j)) :=
  (RAMLayout.incident_send a (.inr (s, x, j))).symm

theorem ramReceive_sort (a : RAMLayout.SendArrays D H w) (s : RAMLayout.Layer D) (y : Site D)
    (j : Fin (RAMLayout.blockBits H w)) :
    ramReceive a (.inr s) y j = (RAMLayout.incidentEquiv D H w a).val (y, .inr (s, 1, j)) := by
  have hp : (routePos (systemMask (.inr s)) D).symm y = s.partner y :=
    Fin.ext (routePos_symm_full_val _ _)
  rw [ramReceive, hp, RAMLayout.incident_receive_sort]
  rfl

theorem ramSend_successor (a : RAMLayout.SendArrays D H w) (x : Site D)
    (hx : x.val + 1 < 2 ^ D) (j : Fin (8 * w)) :
    ramSend a (.inl (successorClass hx)) x j =
      (RAMLayout.incidentEquiv D H w a).val (x, .inl (0, j)) := by
  have hm := (successorClass_eq_iff hx _).mp rfl
  simp only [ramSend, dite_eq_left (And.intro hx hm)]
  exact (RAMLayout.incident_send a (.inl (⟨x.val, by omega⟩, j))).symm

theorem ramSend_successor_unused (a : RAMLayout.SendArrays D H w) (k : Fin D) (x : Site D)
    (h : ¬ (x.val + 1 < 2 ^ D ∧ x.val ^^^ (x.val + 1) = (systemMask (.inl k)).val))
    (j : Fin (8 * w)) : ramSend a (.inl k) x j = false := by simp [ramSend, h]

theorem ramReceive_successor (a : RAMLayout.SendArrays D H w) (y : Site D) (hy : 0 < y.val)
    (j : Fin (8 * w)) :
    ramReceive a (.inl (successorClass (x := y.val - 1) (D := D) (by have := y.isLt; omega))) y j =
      (RAMLayout.incidentEquiv D H w a).val (y, .inl (1, j)) := by
  have hx : y.val - 1 + 1 < 2 ^ D := by have := y.isLt; omega
  let k := successorClass hx
  have hm : (y.val - 1) ^^^ y.val = (systemMask (.inl k)).val := by
    simpa [Nat.sub_add_cancel hy] using (successorClass_eq_iff hx k).mp rfl
  let x : Site D := ⟨y.val - 1, by have := y.isLt; omega⟩
  have he : routePos (systemMask (.inl k)) D x = y := by
    apply Fin.ext
    rw [routePos_full_val, ← hm]
    exact Nat.xor_xor_cancel_left _ _
  change ramReceive a (.inl k) y j = _
  rw [← he, ramReceive_at, he, RAMLayout.incident_receive_successor a y hy]
  simp [ramSend, x, Nat.sub_add_cancel hy, hm, y.isLt]

theorem ramReceive_successor_unused (a : RAMLayout.SendArrays D H w) (k : Fin D) (y : Site D)
    (h : ¬ (0 < y.val ∧ (y.val - 1) ^^^ y.val = (systemMask (.inl k)).val))
    (j : Fin (8 * w)) : ramReceive a (.inl k) y j = false := by
  let m := systemMask (.inl k)
  let x := (routePos m D).symm y
  apply ramSend_successor_unused
  intro ⟨_, hm⟩
  have he : y.val = x.val ^^^ m.val := by
    rw [← routePos_full_val]
    exact (congrArg Fin.val ((routePos m D).apply_symm_apply y)).symm
  have hv : y.val = x.val + 1 := by
    rw [he, ← hm, Nat.xor_xor_cancel_left]
  apply h
  rw [hv]
  exact ⟨Nat.succ_pos _, by simpa using hm⟩

/-- Restricting the source arrays to all routed systems preserves every physical send. -/
theorem ramSend_injective :
    Function.Injective (fun a : RAMLayout.SendArrays D H w ↦ ramSend a) := by
  intro a b hab
  apply Prod.ext
  · funext u j
    have h : u.val + 1 < 2 ^ D := by have := u.isLt; omega
    let k := successorClass h
    let x : Site D := ⟨u.val, by omega⟩
    have hm := (successorClass_eq_iff h k).mp rfl
    have he := congrFun (congrFun (congrFun hab (.inl k)) x) j
    simpa [ramSend, x, h, hm] using he
  · funext s x j
    exact congrFun (congrFun (congrFun hab (.inr s)) x) j

/-- Route-bit assignment, with separate payload bits for each system on every
cursor arc. These are the shared variables in the expanded contraction. -/
abbrev RAMFields (D H w : ℕ) :=
  (s : RAMSystem D) → ArcFields D (Fin (ramFieldBits H w s) → Bool)

/-- Recover each physical send directly from its outgoing field at cursor zero.
At a successor boundary only its own mask class is consulted. -/
def readSends [NeZero D] (f : RAMFields D H w) : RAMLayout.SendArrays D H w :=
  (fun u j =>
    let s : RAMSystem D := .inl (successorClass (x := u.val) (by have := u.isLt; omega))
    f s 0 ⟨u.val, by have := u.isLt; omega⟩ ((systemMask s).val.testBit 0) j,
   fun l x j => f (.inr l) 0 x ((systemMask (.inr l)).val.testBit 0) j)

theorem readSends_eq [NeZero D] (a : RAMLayout.SendArrays D H w) (f : RAMFields D H w)
    (h : ∀ s, LocalTies (fun _ => false) (systemMask s) (ramSend a s) (ramReceive a s) (f s)) :
    readSends f = a := by
  apply Prod.ext
  · funext u j
    have hx : u.val + 1 < 2 ^ D := by have := u.isLt; omega
    let k := successorClass hx
    let x : Site D := ⟨u.val, by have := u.isLt; omega⟩
    change f (.inl k) 0 x ((systemMask (.inl k)).val.testBit 0) j = a.1 u j
    rw [(h (.inl k)).start x]
    simp [ramSend, x, hx, (successorClass_eq_iff hx k).mp rfl]
  · funext l x j
    exact congrFun ((h (.inr l)).start x) j

/-- A routed field assignment can be checked using the directly addressed sends
read at cursor zero. No search over a compatible original assignment is required. -/
theorem carries_iff_readSends [NeZero D] (f : RAMFields D H w) :
    (∃ a, ∀ s, LocalTies (fun _ => false) (systemMask s) (ramSend a s) (ramReceive a s) (f s)) ↔
      ∀ s, LocalTies (fun _ => false) (systemMask s) (ramSend (readSends f) s)
        (ramReceive (readSends f) s) (f s) := by
  constructor
  · rintro ⟨a, ha⟩
    rw [readSends_eq a f ha]
    exact ha
  · exact fun h => ⟨readSends f, h⟩

/-- Unweighted contraction on the cursor graph, summing over its actual bit fields. -/
noncomputable def ramContraction [NeZero D] {R : Type*} [AddCommMonoid R]
    (weight : RAMLayout.SendArrays D H w → R) : R :=
  routedContraction (P := fun s : RAMSystem D => Fin (ramFieldBits H w s) → Bool)
    (fun _ _ => false) systemMask ramSend ramReceive weight

theorem ramContraction_eq [NeZero D] {R : Type*} [AddCommMonoid R]
    (weight : RAMLayout.SendArrays D H w → R) :
    ramContraction weight = ∑ a, weight a := by
  unfold ramContraction
  exact routed_contraction_eq _ _ _ _ ramSend_injective ramReceive_at weight

open BurstRAM RAMMemory RAMLayout in
/-- Applied to the local validators, the routed tensor network still counts precisely
the capped accepting RAM paths, including all their private branches. -/
theorem ramContraction_pathCount {C : Type*} {e : ℕ} [NeZero D]
    (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) :
    ramContraction (fun a : SendArrays D (2 ^ e) w => ∏ v : Site D,
      Nat.card (SitePaths P fuel initial header hw hc ((sendArraysEquiv D (2 ^ e) w).symm a) v)) =
      Nat.card (ActualPaths P fuel initial (initialMemory (2 ^ D) header)
        (withinCaps (2 ^ D) (2 ^ e))) := by
  rw [ramContraction_eq, parsimoniousRAMTranscripts P fuel initial header hw hc]
  exact (sendArraysEquiv D (2 ^ e) w).symm.sum_comp
    (fun bits => ∏ v : Site D, Nat.card (SitePaths P fuel initial header hw hc bits v))

end CursorRouting

end VPVNP
end Computability
end OAI
