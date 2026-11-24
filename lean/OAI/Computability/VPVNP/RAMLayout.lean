import OAI.Computability.VPVNP.RAMSortRouting
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# The communication fields of the RAM transcript

Lemma 10.1 of *VP and VNP differ over every field* uses two successor fields and
two fields for each cross-site sorting layer. We number the layers in phase order,
with decreasing stride within each phase. A field bit has a contiguous local
offset and either a unique matching bit at another site or a prescribed zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMLayout

/-- Number of cross-site layers for `2^d` sites. -/
def layerCount (d : ℕ) : ℕ := (d + 1).choose 2

private theorem layerCount_succ (d : ℕ) : layerCount (d + 1) = layerCount d + (d + 1) := by
  rw [layerCount, Nat.choose_succ_succ (d + 1) 1, Nat.choose_one_right, Nat.add_comm]
  rfl

/-- In phase `h + phase + 1` of an array with `2^h` positions per site,
the cross-site strides decrease from `2^(h+phase)` to `2^h`. -/
@[ext] structure Layer (d : ℕ) where
  /-- Zero-based phase of the cross-site sorting network, below the number of site-index bits. -/
  phase : ℕ
  /-- Zero-based step in a sorting phase, ranging from zero through the phase number in
  decreasing stride order. -/
  step : ℕ
  phase_lt : phase < d
  step_le : step ≤ phase
  deriving DecidableEq

variable {d : ℕ}

/-- Site-index bit flipped to find the partner at this layer, equal to the phase number minus
its step. -/
def Layer.siteBit (s : Layer d) : ℕ := s.phase - s.step

theorem Layer.siteBit_lt (s : Layer d) : s.siteBit < d :=
  lt_of_le_of_lt (Nat.sub_le _ _) s.phase_lt

/-- Translate a cross-site layer to its ordinal among all exchanges. -/
def Layer.ordinal (s : Layer d) : Fin (layerCount d) :=
  ⟨layerCount s.phase + s.step, by
    have h := Nat.choose_le_choose 2 (Nat.succ_le_succ s.phase_lt)
    change layerCount (s.phase + 1) ≤ layerCount d at h
    rw [layerCount_succ] at h
    have := s.step_le
    omega⟩

/-- Decode a layer ordinal by comparing against one triangular prefix per phase. -/
def layerAt : (d : ℕ) → Fin (layerCount d) → Layer d
  | 0, i => Fin.elim0 i
  | d + 1, i =>
    if h : i.val < layerCount d then
      let s := layerAt d ⟨i.val, h⟩
      ⟨s.phase, s.step, Nat.lt_succ_of_lt s.phase_lt, s.step_le⟩
    else
      ⟨d, i.val - layerCount d, Nat.lt_succ_self _, by
        have hbound := i.isLt
        have := layerCount_succ d
        omega⟩

private theorem ordinal_layerAt (i : Fin (layerCount d)) : (layerAt d i).ordinal = i := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    apply Fin.ext
    simp only [Layer.ordinal, layerAt]
    split
    · exact congrArg Fin.val (ih _)
    · change layerCount d + (i.val - layerCount d) = i.val
      omega

private theorem Layer.ordinal_injective : Function.Injective (Layer.ordinal (d := d)) := by
  intro a b hab
  have hn := congrArg Fin.val hab
  change layerCount a.phase + a.step = layerCount b.phase + b.step at hn
  have upper (s : Layer d) : layerCount s.phase + s.step < layerCount (s.phase + 1) := by
    rw [layerCount_succ]
    exact Nat.add_lt_add_left (Nat.lt_succ_of_le s.step_le) _
  have mono : Monotone layerCount := fun _ _ h ↦ Nat.choose_le_choose 2 (Nat.succ_le_succ h)
  have hp : a.phase = b.phase := by
    rcases lt_trichotomy a.phase b.phase with h | h | h
    · have : layerCount (a.phase + 1) ≤ layerCount b.phase := mono h
      have := upper a
      omega
    · exact h
    · have : layerCount (b.phase + 1) ≤ layerCount a.phase := mono h
      have := upper b
      omega
  exact Layer.ext hp (by rw [hp] at hn; omega)

/-- Bijection between physical sorting layers and their consecutive field numbers. -/
def layerEquiv (d : ℕ) : Layer d ≃ Fin (layerCount d) where
  toFun := Layer.ordinal
  invFun := layerAt d
  left_inv s := Layer.ordinal_injective (ordinal_layerAt s.ordinal)
  right_inv := ordinal_layerAt

/-- One block in a sorting direction contains five words per padded record. -/
def blockBits (H w : ℕ) : ℕ := 4 * H * 5 * w

/-- Successor fields carry status, cost, state, and one final five-word record.
The direction is zero for send and one for receive. -/
abbrev Slot (d H w : ℕ) :=
  (Fin 2 × Fin (8 * w)) ⊕ (Layer d × (Fin 2 × Fin (blockBits H w)))

/-- Number of incident bits at one site, counting both successor fields and a send and receive
block at every cross-site sorting layer. -/
def width (d H w : ℕ) : ℕ := 2 * (8 * w) + layerCount d * (2 * blockBits H w)

/-- Equation (10.1), with `d = log₂ S`. Both endpoints reserve both successor fields. -/
theorem width_eq (d H w : ℕ) :
    width d H w = 16 * w + 40 * H * w * (d + 1).choose 2 := by
  unfold width blockBits layerCount
  ring

/-- A uniform constant in the asymptotic estimate of (10.1), with `H = 2^e`
and `S = 2^d`. The sort has `log₂ (4HS)` phases. -/
theorem width_le (d e w : ℕ) :
    width d (2 ^ e) w ≤ 56 * (2 ^ e) * w * ((4 * 2 ^ e * 2 ^ d).log2) ^ 2 := by
  have hlog : (4 * 2 ^ e * 2 ^ d).log2 = 2 + e + d := by
    rw [show 4 * 2 ^ e * 2 ^ d = 2 ^ (2 + e + d) by rw [pow_add, pow_add]; rfl]
    exact Nat.log2_two_pow
  have hcount : (d + 1).choose 2 ≤ (2 + e + d) ^ 2 := by
    rw [Nat.choose_two_right, pow_two]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul (by omega) (by omega))
  have hpos := Nat.two_pow_pos e
  have hsquare : 1 ≤ (2 + e + d) ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [width_eq, hlog]
  calc
    16 * w + 40 * 2 ^ e * w * (d + 1).choose 2 ≤
        (16 * 2 ^ e * w + 40 * 2 ^ e * w) * (2 + e + d) ^ 2 := by
      rw [Nat.add_mul]
      apply Nat.add_le_add
      · exact (Nat.mul_le_mul_right w (Nat.le_mul_of_pos_right _ hpos)).trans
          (Nat.le_mul_of_pos_right _ hsquare)
      · exact Nat.mul_le_mul_left _ hcount
    _ = _ := by ring

/-- A contiguous, invertible bit address: the two successor fields precede the
send/receive field pair for each sorting layer in chronological order. -/
def offset (d H w : ℕ) : Slot d H w ≃ Fin (width d H w) :=
  (finProdFinEquiv.sumCongr
    (((layerEquiv d).prodCongr finProdFinEquiv).trans finProdFinEquiv)).trans finSumFinEquiv

variable {H w : ℕ}

theorem offset_successor (dir : Fin 2) (j : Fin (8 * w)) :
    (offset d H w (.inl (dir, j))).val = 8 * w * dir.val + j.val := by
  change j.val + 8 * w * dir.val = _
  omega

theorem offset_sort (s : Layer d) (dir : Fin 2) (j : Fin (blockBits H w)) :
    (offset d H w (.inr (s, dir, j))).val =
      16 * w + s.ordinal.val * (2 * blockBits H w) + dir.val * blockBits H w + j.val := by
  change 2 * (8 * w) + (j.val + blockBits H w * dir.val + 2 * blockBits H w * s.ordinal.val) = _
  ring

/-- The common partner of all records sent by a site at this layer. -/
def Layer.partner (s : Layer d) (v : Fin (2 ^ d)) : Fin (2 ^ d) :=
  ⟨RAMSort.partner s.siteBit v.val, RAMSort.partner_lt v.isLt s.siteBit_lt⟩

@[simp] theorem Layer.partner_partner (s : Layer d) (v : Fin (2 ^ d)) :
    s.partner (s.partner v) = v :=
  Fin.ext (RAMSort.partner_partner _ _)

theorem Layer.partner_ne (s : Layer d) (v : Fin (2 ^ d)) : s.partner v ≠ v :=
  fun h ↦ RAMSort.partner_ne _ _ (congrArg Fin.val h)

theorem Layer.record_partner (s : Layer d) (v : Fin (2 ^ d)) {h : ℕ} (j : Fin (2 ^ h)) :
    RAMSort.partner (h + s.siteBit) (v.val * 2 ^ h + j.val) =
      (s.partner v).val * 2 ^ h + j.val := by
  simpa [Layer.partner] using RAMSort.partner_cross v.val j.isLt (Nat.le_add_right h s.siteBit)

/-- The missing successor send at the last site and receive at the first site
are represented by `none`. All other bits have one peer with opposite direction. -/
def peer (v : Fin (2 ^ d)) : Slot d H w → Option (Fin (2 ^ d) × Slot d H w)
  | .inl (dir, j) =>
    if dir = 0 then
      if h : v.val + 1 < 2 ^ d then some (⟨v.val + 1, h⟩, .inl (1, j)) else none
    else
      if h : 0 < v.val then some (⟨v.val - 1, by omega⟩, .inl (0, j)) else none
  | .inr (s, dir, j) => some (s.partner v, .inr (s, dir.rev, j))

theorem peer_send_end (v : Fin (2 ^ d)) (h : v.val + 1 = 2 ^ d) (j : Fin (8 * w)) :
    peer (H := H) v (.inl (0, j)) = none := by simp [peer, h]

theorem peer_receive_start (v : Fin (2 ^ d)) (h : v.val = 0) (j : Fin (8 * w)) :
    peer (H := H) v (.inl (1, j)) = none := by simp [peer, h]

/-- Direction of an incident bit, in both parts of the layout. -/
def direction : Slot d H w → Fin 2
  | .inl (dir, _) | .inr (_, dir, _) => dir

private theorem peer_pair {v u : Fin (2 ^ d)} {p q : Slot d H w} (hp : peer v p = some (u, q)) :
    peer u q = some (v, p) ∧ direction q = (direction p).rev := by
  rcases p with ⟨dir, j⟩ | ⟨s, dir, j⟩
  · by_cases hd : dir = 0
    · subst dir
      by_cases h : v.val + 1 < 2 ^ d
      · simp [peer, h] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨by simp [peer], rfl⟩
      · simp [peer, h] at hp
    · have hdir : dir = 1 := by
        apply Fin.ext
        have := dir.isLt
        have : dir.val ≠ 0 := fun he ↦ hd (Fin.ext he)
        omega
      subst dir
      by_cases h : 0 < v.val
      · simp [peer, h] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have he : v.val - 1 + 1 = v.val := by omega
        exact ⟨by simp [peer, he, v.isLt], rfl⟩
      · simp [peer, h] at hp
  · cases hp
    exact ⟨by simp [peer], rfl⟩

/-- Each actual connection pairs two ports and can be traced from either end. -/
theorem peer_reverse {v u : Fin (2 ^ d)} {p q : Slot d H w} (hp : peer v p = some (u, q)) :
    peer u q = some (v, p) := (peer_pair hp).1

theorem peer_direction {v u : Fin (2 ^ d)} {p q : Slot d H w}
    (hp : peer v p = some (u, q)) : direction q = (direction p).rev := (peer_pair hp).2

private theorem rev_eq_zero_iff (i : Fin 2) : i.rev = 0 ↔ i ≠ 0 := by
  simp only [ne_eq, Fin.ext_iff, Fin.val_rev]
  have := i.isLt
  change 2 - (i.val + 1) = 0 ↔ i.val ≠ 0
  omega

/-- One incident bit position specified by its site and its local communication slot. -/
abbrev Endpoint (d H w : ℕ) := Fin (2 ^ d) × Slot d H w

/-- Shared assignments carry one bit per existing send. There is no independent
assignment to a clamped field or to the receiving copy of a shared bit. -/
def IsSend (x : Endpoint d H w) : Prop :=
  direction x.2 = 0 ∧ (peer x.1 x.2).isSome

instance (x : Endpoint d H w) : Decidable (IsSend x) := by
  unfold IsSend
  infer_instance

/-- A sending endpoint of an existing link, indexing the one Boolean shared with its matching
receiving endpoint. -/
abbrev SharedBit (d H w : ℕ) := {x : Endpoint d H w // IsSend x}

/-- Locate a port's bit in the array of sends. A missing endpoint is zero. -/
def source (x : Endpoint d H w) : Option (Endpoint d H w) :=
  (peer x.1 x.2).map fun y ↦ if direction x.2 = 0 then x else y

theorem source_shared {x s : Endpoint d H w} (hs : source x = some s) : IsSend s := by
  cases h : peer x.1 x.2 with
  | none => simp [source, h] at hs
  | some y =>
    by_cases hx : direction x.2 = 0
    · simp [source, h, hx] at hs
      subst s
      simp [IsSend, hx, h]
    · simp [source, h, hx] at hs
      subst s
      exact ⟨(peer_direction h).trans ((rev_eq_zero_iff _).2 hx), by simp [peer_reverse h]⟩

private theorem source_send (s : SharedBit d H w) : source s.val = some s.val := by
  have hh := s.property.2
  cases h : peer s.val.1 s.val.2 with
  | none => simp [h] at hh
  | some y => simp [source, h, s.property.1]

theorem source_peer {x y : Endpoint d H w} (h : peer x.1 x.2 = some y) :
    source x = source y := by
  have hr := peer_reverse h
  have hd := peer_direction h
  by_cases hx : direction x.2 = 0
  · have hy : direction y.2 ≠ 0 := by simpa [hd, rev_eq_zero_iff] using hx
    simp [source, h, hr, hx, hy]
  · have hy : direction y.2 = 0 := hd.trans ((rev_eq_zero_iff _).2 hx)
    simp [source, h, hr, hx, hy]

/-- Clamps and pairwise equality are exactly the constraints on incident bit values. -/
def Compatible (b : Endpoint d H w → Bool) : Prop :=
  (∀ x, peer x.1 x.2 = none → b x = false) ∧
  (∀ x y, peer x.1 x.2 = some y → b x = b y)

private def sentValue (b : SharedBit d H w → Bool) (s : Endpoint d H w) : Bool :=
  if h : IsSend s then b ⟨s, h⟩ else false

/-- Shared assignments and compatible incident assignments have equal multiplicities,
including the one-site case where both successor fields are clamped. -/
def assignmentEquiv (d H w : ℕ) :
    (SharedBit d H w → Bool) ≃ {b : Endpoint d H w → Bool // Compatible b} where
  toFun b := ⟨fun x ↦ ((source x).map (sentValue b)).getD false, by
    constructor
    · intro x hx
      simp [source, hx]
    · intro x y hxy
      exact congrArg (fun z ↦ (z.map (sentValue b)).getD false) (source_peer hxy)⟩
  invFun b := fun s ↦ b.val s.val
  left_inv b := funext fun s ↦ by simp [source_send, sentValue, s.property]
  right_inv b := by
    apply Subtype.ext
    funext x
    cases h : peer x.1 x.2 with
    | none => simp [source, h, b.property.1 x h]
    | some y =>
      by_cases hx : direction x.2 = 0
      · have hs : source x = some x := by simp [source, h, hx]
        simp [hs, sentValue, source_shared hs]
      · have hs : source x = some y := by simp [source, h, hx]
        simp [hs, sentValue, source_shared hs, b.property.2 x y h]

end RAMLayout

end VPVNP
end Computability
end OAI
