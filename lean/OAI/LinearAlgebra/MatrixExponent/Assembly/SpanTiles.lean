import OAI.LinearAlgebra.MatrixExponent.Assembly.PayloadProgram
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Assembly.Fragments
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.BoardPush
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Keys

/-! The cost of packing host records is linear in the transported width. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Payload.Script
open Coloring Transcript

def cost (m k m' k' p w v c c' : ℕ) :=
  50000 * (k + k' + 2) * (c + c' + (2 ^ m + 2 ^ m') * (v + (101 + m + m' + w + k') ^ 60) + 2 ^ (m + p) * (m' + p))

variable {m V k m' V' k' p w n v c c' : ℕ}

private theorem bound (ha : (item w p n).width ≤ v) :
    rawCost m V k m' V' k' p w n v c c' ≤ cost m k m' k' p w v c c' := by
  let K := k + k' + 2
  let N := 2 ^ m + 2 ^ m'
  let B := (101 + m + m' + w + k') ^ 60
  let X := c + c' + N * (v + B) + 2 ^ (m + p) * (m' + p)
  let I := (item w p n).width
  let C := Fintype.card (Slot (2 ^ m) V k)
  let C' := Fintype.card (Slot (2 ^ m') V' k')
  let a := (Fragments.Input w p n).width
  let P := (PeerLayout.input m m' p w).width
  have hi : I = a + w := by simp only [I, a, Format.width_pair, Format.width_addr]
  have hv : N * I ≤ N * (v + B) := Nat.mul_le_mul_left _ (ha.trans (Nat.le_add_right _ _))
  have hs : (Script m m' p w n).width ≤ X := by
    have e : (Script m m' p w n).width = N * I + 2 ^ (m + p) * (m' + p) := by
      simp only [Script, PeerLayout.input, PeerLayout.lengths, I, Fragments.Input,
        Format.width_pair, Format.width_vec, Format.width_addr, N]
      ring
    rw [e]
    unfold X
    omega
  have hP : P ≤ X := by
    rw [Format.width_pair] at hs
    exact (Nat.le_add_right _ _).trans hs
  have hf : (first m m' p w n).width ≤ 3 * X := by
    have e : (first m m' p w n).width = N * (w + I) + P := by
      simp only [first, Redistribute.input, Format.width_pair, Format.width_vec, Format.width_addr, N, I, P]
      ring
    rw [e]
    have hb : N * (w + I) ≤ 2 * X := calc
      _ ≤ N * (2 * I) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := by rw [mul_left_comm]; exact Nat.mul_le_mul_left _ (hv.trans (by unfold X; omega))
    omega
  have hb : C + C' ≤ K * N := by
    unfold C C' N
    rw [mul_add]
    exact Nat.add_le_add ((Transcript.card_slots ..).trans (Nat.mul_le_mul_right _ (by omega)))
      ((Transcript.card_slots ..).trans (Nat.mul_le_mul_right _ (by omega)))
  have hh : (C + C') * (I + B) ≤ K * X := calc
    _ ≤ (K * N) * (v + B) := Nat.mul_le_mul hb (Nat.add_le_add_right ha _)
    _ ≤ _ := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ (by unfold X; omega)
  have hrec : ((payloadBank m V k m' V' k').records w p n).width = (C + C') * a := by
    simp only [Bank.records, Fmt.width_pi, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    change Fintype.card (Slot (2 ^ m) V k ⊕ Slot (2 ^ m') V' k') * a = _
    rw [Fintype.card_sum]
  have hmove : (moved m V k m' V' k' p w n).width = (C + C') * I + P := by
    simp only [I, C, C', P, moved, Format.width_pair, Redistribute.output, Fmt.width_pi, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, add_mul]
  have hstage : (staged m V k m' V' k' p w n).width = (C + C') * a + (P + C' * w) := by
    unfold staged
    rw [Format.width_pair, hrec, Format.width_pair, Fmt.width_pi]
    simp only [Format.width_addr, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rfl
  have hpow : (100 + (w + k' + 1)) ^ 2 ≤ B :=
    (Nat.pow_le_pow_left (by omega : 100 + (w + k' + 1) ≤ 101 + m + m' + w + k') _).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hr (l b c₀ : ℕ) (hl : l ≤ m + m') (hn : 2 ^ l ≤ N) (hb : b + 1 ≤ K) (hc : c₀ ≤ c + c') :
      Redistribute.cost l b w v c₀ ≤ 10000 * (K * X) := by
    have hp : (101 + l + w) ^ 60 ≤ B := Nat.pow_le_pow_left (by omega) _
    have hle : Redistribute.budget l w v ≤ N * (v + B) := Nat.mul_le_mul hn (Nat.add_le_add_left hp v)
    unfold Redistribute.cost
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hb ((Nat.add_le_add hc hle).trans (Nat.le_add_right _ _)))
  have hr₁ := hr m k c (by omega) (Nat.le_add_right _ _) (by omega) (by omega)
  have hr₂ := hr m' k' c' (by omega) (Nat.le_add_left _ _) (by omega) (by omega)
  have hX : X ≤ K * X := Nat.le_mul_of_pos_left _ (by omega)
  have hsize : cost m k m' k' p w v c c' = 50000 * (K * X) := mul_assoc ..
  unfold rawCost
  rw [hsize, hrec, hstage, hmove]
  have he := Nat.mul_le_mul_left C' hpow
  rw [hi] at hh ⊢
  linarith only [he, hh, hr₁, hr₂, hX, hP, hf, hs, Nat.zero_le (C * w), Nat.zero_le (C' * w),
    Nat.zero_le (C * B), Nat.zero_le (C' * B), Nat.zero_le ((C + C') * a), Nat.zero_le (K * X)]

theorem realize {F : Type} [Field F] {u : ℕ} {L : Set (Table F)}
    (hu : 3 ≤ u) (ht : Radix.Tag F m v c) (ht' : Radix.Tag F m' v c')
    (ha : (item w p n).width ≤ v) :
    Map F u L (Script m m' p w n) (Out m V k m' V' k' p w n) pack (cost m k m' k' p w v c c') :=
  (build hu ht ht' ha).mono (bound ha)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Payload.Script
end

/-! # Correctness criteria on logical host records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Payload.Script

open Coloring
open scoped Classical
variable {m V k m' V' k' d p w n : ℕ} {x : Payload m V k} {y : Payload m' V' k'}
  {M : Traffic x y d} {hd : d ≤ 2 ^ p} {q : (Script m m' p w n).obj}

structure Bounds (z : (Fragments.Input w p n).obj) : Prop where
  inside : ∀ i, let a := z.2 i
    a.2.1.val + a.2.2.1.val ≤ (z.1 a.1).val
  apart : ∀ i j t, (z.2 i).1 = (z.2 j).1 →
    Intervals.covers (z.2 i).2 t → Intervals.covers (z.2 j).2 t → j = i

def At (z : B n → (Fragments.Entry w p).obj) (port : B p) (pos value : ℕ) : Prop :=
  ∃ i, (z i).1 = port ∧ Intervals.covers (z i).2 pos ∧
    (z i).2.2.2.val + (pos - (z i).2.1.val) = value

structure Valid (M : Traffic x y d) (hd : d ≤ 2 ^ p) (q : (Script m m' p w n).obj) : Prop where
  peer : PeerLayout.Fits M hd q.1
  left : ∀ s, Bounds (q.1.1.1.2 s, q.2.1 s)
  right : ∀ s, Bounds (q.1.1.2.2 s, q.2.2 s)
  send : ∀ e j, At (q.2.1 (M.src e).1) ((M.src e).2.castLE hd) j.val (M.send e j).val
  get : ∀ e j, At (q.2.2 (M.dst e).1) ((M.dst e).2.castLE hd) j.val (M.get e j).val

theorem Valid.pieces (h : Valid M hd q) : M.links.Pieces hd (pack q).1 := by
  let t := pack (V := V) (k := k) (V' := V') (k' := k') q
  have hempty : Bounds (empty w p n) := by
    constructor
    · simp [empty]
    · simp [Intervals.covers, empty]
  have hs (s) : Bounds (t.1 s) := by
    unfold t
    rcases s with s | s
    · cases he : x.seat.read s with
      | none => rw [empty_source h.peer s he]; exact hempty
      | some a => rw [(x.seat.valid _ _).mp he, source h.peer a]; exact h.left a
    · cases he : y.seat.read s with
      | none => rw [empty_destination h.peer s he]; exact hempty
      | some a => rw [(y.seat.valid _ _).mp he, destination h.peer a]; exact h.right a
  refine ⟨fits h.peer, fun s => (hs s).inside, fun s => (hs s).apart, ?_⟩
  rintro ⟨e, _|_⟩ j
  · change At (t.1 (.inl (x.seat.write (M.src e).1))).2 ((M.src e).2.castLE hd) j.val (M.send e j).val
    unfold t
    rw [source h.peer]
    exact h.send _ _
  · change At (t.1 (.inr (y.seat.write (M.dst e).1))).2 ((M.dst e).2.castLE hd) j.val (M.get e j).val
    unfold t
    rw [destination h.peer]
    exact h.get _ _

def decode (hd : d ≤ 2 ^ p) : (Script m m' p w n).obj →
    (PeerLayout.S m V k m' V' k' d).control.obj := command hd ∘ pack

theorem Valid.represents (h : Valid M hd q) : M.links.Represents (decode hd q) :=
  Script.represents hd M h.peer h.pieces

theorem Valid.carries (h : Valid M hd q) (a : (Fmt.payload m V k).obj) (b : (Fmt.payload m' V' k').obj) :
    (PeerLayout.S m V k m' V' k' d).Carries (decode hd q) a b ↔ M.links.Matches a b :=
  Bank.Links.Represents.carries M.links h.represents a b

theorem decode_net {F : Type} [Field F] {u : ℕ} {L : Set (Table F)} {v c c' : ℕ}
    (hu : 3 ≤ u) (hd : d ≤ 2 ^ p) (ht : Radix.Tag F m v c) (ht' : Radix.Tag F m' v c')
    (ha : (item w p n).width ≤ v) :
    Map F u L (Script m m' p w n) (PeerLayout.S m V k m' V' k' d).control
      (decode hd) (cost m k m' k' p w v c c' + commandCost m V k m' V' k' d p w n) := by
  have h := realize (V := V) (V' := V') (k := k) (k' := k') (L := L) hu ht ht' ha
  have hc := command_net (m := m) (m' := m') (V := V) (V' := V') (k := k) (k' := k')
    (w := w) (n := n) hd (F := F) (L := L) hu
  unfold decode
  exact h.comp hc

end OAI.LinearAlgebra.MatrixExponent.Assembly.Payload.Script
end

/-! The positive spans of each contact partition its channel positions. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring Finset

variable {w p n : ℕ} (x : (Input w p n).obj)

abbrev port (i : B n) := (x i).1
abbrev len (i : B n) := (x i).2.1.val
abbrev pos (i : B n) := (x i).2.2.1
abbrev offset (i : B n) := (x i).2.2.2.val
def extent (c : B p) := ((pack x).1 c).val
def start (i : B n) := ((pack x).2 i).2.1.val

def Unique : Prop := ∀ i j, 0 < len x i → 0 < len x j →
  port x i = port x j → pos x i = pos x j → i = j

theorem inside (hx : Fits x) (i : B n) : start x i + len x i ≤ extent x (port x i) := by
  rw [start, starts _ hx, extent, lengths _ hx]
  let f := univ.filter fun j => port x j = port x i ∧ pos x j < pos x i
  change (∑ j ∈ f, len x j) + len x i ≤ _
  rw [add_comm, ← sum_insert (by simp [f] : i ∉ f)]
  exact sum_le_sum_of_subset (insert_subset (by simp) (by
    intro j hj
    simpa using (mem_filter.mp hj).2.1))

theorem earlier_le (hx : Fits x) {i j : B n} (hc : port x i = port x j)
    (ho : pos x i < pos x j) : start x i + len x i ≤ start x j := by
  rw [start, start, starts _ hx, starts _ hx]
  let f := univ.filter fun u => port x u = port x i ∧ pos x u < pos x i
  change (∑ u ∈ f, len x u) + len x i ≤ _
  rw [add_comm, ← sum_insert (by simp [f] : i ∉ f)]
  refine sum_le_sum_of_subset (insert_subset (mem_filter.mpr ⟨mem_univ _, hc, ho⟩) ?_)
  intro u hu
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hu).2.1.trans hc, (mem_filter.mp hu).2.2.trans ho⟩

theorem bounds (hx : Fits x) (hu : Unique x) : Payload.Script.Bounds (pack x) := by
  refine ⟨inside _ hx, fun i j t h hi hj => ?_⟩
  change port x i = port x j at h
  change start x i ≤ t ∧ t < start x i + len x i at hi
  change start x j ≤ t ∧ t < start x j + len x j at hj
  rcases lt_trichotomy (pos x i) (pos x j) with hlt|he|hgt
  · have := earlier_le x hx h hlt
    omega
  · exact (hu _ _ (by omega) (by omega) h he).symm
  · have := earlier_le x hx h.symm hgt
    omega

abbrev Block (c : B p) := Σ i : {i // port x i = c}, Fin (len x i.val)

def index (hx : Fits x) (c : B p) (i : Block x c) : Fin (extent x c) :=
  ⟨start x i.1.val + i.2.val, (Nat.add_lt_add_left i.2.isLt _).trans_le
    ((inside x hx _).trans_eq (congrArg (extent x) i.1.2))⟩

theorem index_covers (hx : Fits x) (c : B p) (i : Block x c) :
    Intervals.covers ((pack x).2 i.1.val).2 (index x hx c i).val :=
  ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.2.isLt _⟩

theorem index_bijective (hx : Fits x) (hu : Unique x) (c : B p) :
    Function.Bijective (index x hx c) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ he
    have ha := index_covers x hx c ⟨i, a⟩
    have hb := index_covers x hx c ⟨j, b⟩
    rw [he] at ha
    have eq : j = i := Subtype.ext ((bounds x hx hu).apart i.val j.val _ (i.2.trans j.2.symm) ha hb)
    subst j
    have h := congrArg Fin.val he
    have : a = b := Fin.ext (Nat.add_left_cancel h)
    rw [this]
  · simp only [Block, Fintype.card_sigma, Fintype.card_fin]
    rw [extent, lengths _ hx]
    exact (sum_subtype _ (by simp) (len x)).symm

def channel (hx : Fits x) (hu : Unique x) (c : B p) : Block x c ≃ Fin (extent x c) :=
  Equiv.ofBijective (index x hx c) (index_bijective x hx hu c)

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! Local bank conditions for one side of a payload transfer. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan

open Coloring Finset
variable {E : Type} {m V k d p w n : ℕ}

abbrev Rows (m w p n : ℕ) := B m → (Input w p n).obj

def name (hd : d ≤ 2 ^ p) (place : E ↪ B m × Fin d) (e : E) := (place e).2.castLE hd

def size (hd : d ≤ 2 ^ p) (place : E ↪ B m × Fin d) (x : Rows m w p n) (e : E) :=
  extent (x (place e).1) (name hd place e)

structure Side (u : Payload m V k) (hd : d ≤ 2 ^ p) (place : E ↪ B m × Fin d)
    (x : Rows m w p n) : Prop where
  fits : ∀ b, Fits (x b)
  unique : ∀ b, Unique (x b)
  bound : ∀ b i, 0 < len (x b) i → offset (x b) i + len (x b) i ≤ u.length b
  apart : ∀ b i j a t, a < len (x b) i → t < len (x b) j →
    offset (x b) i + a = offset (x b) j + t → i = j
  assigned : ∀ b i, 0 < len (x b) i → ∃ e, (place e).1 = b ∧ name hd place e = port (x b) i

def Covers (u : Payload m V k) (x : Rows m w p n) : Prop :=
  ∀ b t, t < u.length b → ∃ i a, a < len (x b) i ∧ offset (x b) i + a = t

/-- A particular occurrence of a bit on a contact. -/
def Hit (x : (Input w p n).obj) (c : B p) (t z : ℕ) : Prop :=
  ∃ i a, port x i = c ∧ a < len x i ∧ start x i + a = t ∧ offset x i + a = z

namespace Hit
variable {x : (Input w p n).obj} {c : B p} {t z z' : ℕ}

theorem at_bit (h : Hit x c t z) : Payload.Script.At (pack x).2 c t z := by
  obtain ⟨i, a, hc, ha, rfl, rfl⟩ := h
  refine ⟨i, hc, ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ha _⟩, ?_⟩
  change offset x i + (start x i + a - start x i) = _
  omega

theorem determined (hx : Fits x) (hu : Unique x) (h : Hit x c t z) (h' : Hit x c t z') : z = z' := by
  obtain ⟨i, hi, ht, he⟩ := h.at_bit
  obtain ⟨j, hj, ht', he'⟩ := h'.at_bit
  have hij := (bounds x hx hu).apart i j t (hi.trans hj.symm) ht ht'
  subst j
  exact he.symm.trans he'

end Hit

namespace Side

variable {u : Payload m V k} {hd : d ≤ 2 ^ p} {place : E ↪ B m × Fin d} {x : Rows m w p n}
    (h : Side u hd place x)

include h in
theorem filled (e : E) (t : Fin (size hd place x e)) :
    ∃ v : Fin (u.length (place e).1), Hit (x (place e).1) (name hd place e) t.val v.val := by
  let Y := x (place e).1
  let c := name hd place e
  obtain ⟨⟨i, a⟩, ha⟩ := (index_bijective Y (h.fits _) (h.unique _) c).2 t
  have hb := (Nat.add_lt_add_left a.isLt (offset Y i.val)).trans_le
    (h.bound _ _ (Nat.zero_lt_of_lt a.isLt))
  exact ⟨⟨_, hb⟩, i.val, a.val, i.2, a.isLt, congrArg Fin.val ha, rfl⟩

include h in
theorem separate {e e' : E} {a b v : ℕ} (he : (place e).1 = (place e').1)
    (ha : Hit (x (place e).1) (name hd place e) a v)
    (hb : Hit (x (place e').1) (name hd place e') b v) : e = e' ∧ a = b := by
  rw [he] at ha
  obtain ⟨i, k, hi, hk, ht, hu⟩ := ha
  obtain ⟨j, l, hj, hl, ht', hu'⟩ := hb
  have hij := h.apart _ _ _ _ _ hk hl (hu.trans hu'.symm)
  subst j
  have hn : name hd place e = name hd place e' := hi.symm.trans hj
  have hkl : k = l := Nat.add_left_cancel (hu.trans hu'.symm)
  have hv := congrArg Fin.val hn
  exact ⟨place.injective (Prod.ext he (Fin.ext hv)), by rw [← ht, ← ht', hkl]⟩

def point (e : E) : Fin (size hd place x e) ↪ Fin (u.length (place e).1) where
  toFun t := (h.filled e t).choose
  inj' := by
    intro a b he
    have ha := (h.filled e a).choose_spec
    have hb := (h.filled e b).choose_spec
    change (h.filled e a).choose = (h.filled e b).choose at he
    rw [he] at ha
    exact Fin.ext (h.separate rfl ha hb).2

theorem spec (e : E) (t : Fin (size hd place x e)) :
    Hit (x (place e).1) (name hd place e) t.val (h.point e t).val :=
  (h.filled e t).choose_spec

theorem used (e : E) (i : B n) (hi : port (x (place e).1) i = name hd place e)
    (a : ℕ) (ha : a < len (x (place e).1) i) :
    ∃ t : Fin (size hd place x e), t.val = start (x (place e).1) i + a ∧
      (h.point e t).val = offset (x (place e).1) i + a := by
  let t := index _ (h.fits _) _ ⟨⟨i, hi⟩, ⟨a, ha⟩⟩
  exact ⟨t, rfl, Hit.determined (h.fits _) (h.unique _) (h.spec e t) ⟨i, a, hi, ha, rfl, rfl⟩⟩

include h in
theorem occupied (b : B m) (c : B p) (hc : 0 < extent (x b) c) :
    ∃ e, (place e).1 = b ∧ name hd place e = c := by
  obtain ⟨⟨i, a⟩, _⟩ := (index_bijective _ (h.fits b) (h.unique b) c).2 ⟨0, hc⟩
  obtain ⟨e, he, hi⟩ := h.assigned b i.val (Nat.zero_lt_of_lt a.isLt)
  exact ⟨e, he, hi.trans i.2⟩

theorem onto (hc : Covers u x) (j : u.Bit) :
    ∃ e t, (⟨(place e).1, h.point e t⟩ : u.Bit) = j := by
  obtain ⟨b, ⟨t, ht⟩⟩ := j
  obtain ⟨i, a, ha, rfl⟩ := hc b t ht
  obtain ⟨e, rfl, he⟩ := h.assigned b i (Nat.zero_lt_of_lt ha)
  obtain ⟨j, _, hj⟩ := h.used e i he.symm a ha
  exact ⟨e, j, congrArg (Sigma.mk _) (Fin.ext hj)⟩

end Side
end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! Pairing spans by order gives the same offsets at both ends. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring Finset

variable {w p n : ℕ} (x : (Input w p n).obj)

def amount (c : B p) (o : B n) := ∑ i with port x i = c ∧ pos x i = o, len x i

theorem amount_pos (c : B p) (o : B n) (h : 0 < amount x c o) :
    ∃ i, 0 < len x i ∧ port x i = c ∧ pos x i = o := by
  obtain ⟨i, hi, he⟩ := exists_ne_zero_of_sum_ne_zero h.ne'
  exact ⟨i, Nat.pos_of_ne_zero he, (mem_filter.mp hi).2⟩

theorem amount_at (hu : Unique x) (i : B n) (hi : 0 < len x i) :
    amount x (port x i) (pos x i) = len x i := by
  refine sum_eq_single i (fun j hj hn => ?_) (by simp)
  obtain ⟨hc, ho⟩ := (mem_filter.mp hj).2
  by_contra! hz
  exact hn (hu _ _ (Nat.pos_of_ne_zero hz) hi hc ho)

private theorem grouped (c : B p) (s : Finset (B n)) :
    ∑ j ∈ s, amount x c j = ∑ i with port x i = c ∧ pos x i ∈ s, len x i := by
  simpa only [amount, filter_filter] using
    sum_fiberwise_eq_sum_filter (univ.filter (fun i => port x i = c)) s (pos x) (len x)

theorem extent_eq (h : Fits x) (c : B p) : extent x c = ∑ j, amount x c j := by
  rw [extent, lengths _ h, grouped]
  simp only [mem_univ, and_true]

theorem start_eq_sum (h : Fits x) (i : B n) :
    start x i = ∑ j ∈ Iio (pos x i), amount x (port x i) j := by
  rw [start, starts _ h, grouped]
  simp only [mem_Iio]

variable {E : Type} {m V k m' V' k' d : ℕ}

def Match (hd : d ≤ 2 ^ p) (src : E ↪ B m × Fin d) (dst : E ↪ B m' × Fin d)
    (x : Rows m w p n) (y : Rows m' w p n) : Prop :=
  ∀ e o, amount (x (src e).1) (name hd src e) o = amount (y (dst e).1) (name hd dst e) o

variable {hd : d ≤ 2 ^ p} {src : E ↪ B m × Fin d} {dst : E ↪ B m' × Fin d}
    {x : Rows m w p n} {y : Rows m' w p n} {u : Payload m V k} {v : Payload m' V' k'}
    (hx : Side u hd src x) (hy : Side v hd dst y) (h : Match hd src dst x y)

include hx hy h in
theorem Match.size_eq (e : E) : size hd src x e = size hd dst y e := by
  unfold size
  rw [extent_eq _ (hx.fits _), extent_eq _ (hy.fits _)]
  exact sum_congr rfl fun j _ => h e j

structure Paired (hd : d ≤ 2 ^ p) (src : E ↪ B m × Fin d) (dst : E ↪ B m' × Fin d)
    (x : Rows m w p n) (y : Rows m' w p n) (e : E) (i j : B n) : Prop where
  source : port (x (src e).1) i = name hd src e
  target : port (y (dst e).1) j = name hd dst e
  order : pos (x (src e).1) i = pos (y (dst e).1) j
  left : 0 < len (x (src e).1) i
  right : 0 < len (y (dst e).1) j

include hx hy h in
theorem Match.aligned {e : E} {i j : B n} (hp : Paired hd src dst x y e i j) :
    len (x (src e).1) i = len (y (dst e).1) j ∧ start (x (src e).1) i = start (y (dst e).1) j := by
  constructor
  · rw [← amount_at _ (hx.unique _) i hp.left, ← amount_at _ (hy.unique _) j hp.right,
      hp.source, hp.target, hp.order]
    exact h _ _
  · rw [start_eq_sum _ (hx.fits _), start_eq_sum _ (hy.fits _), hp.source, hp.target, hp.order]
    exact sum_congr rfl fun j _ => h e j

include hx h in
theorem Match.partner {e : E} {i : B n} (hc : port (x (src e).1) i = name hd src e)
    (hi : 0 < len (x (src e).1) i) : ∃ j, Paired hd src dst x y e i j := by
  have he := amount_at _ (hx.unique _) i hi
  rw [hc, h] at he
  obtain ⟨j, hj, hc', ho⟩ := amount_pos _ _ _ (he.symm ▸ hi)
  exact ⟨j, hc, hc', ho.symm, hi, hj⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! Construct actual payload transfers from matched local span lists. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring

variable {E : Type} {w p n m V k m' V' k' d : ℕ}
variable {hd : d ≤ 2 ^ p} {src : E ↪ B m × Fin d} {dst : E ↪ B m' × Fin d}
    {x : Rows m w p n} {y : Rows m' w p n} {u : Payload m V k} {v : Payload m' V' k'}
    (hx : Side u hd src x) (hy : Side v hd dst y) (h : Match hd src dst x y) (hc : Covers v y)

def traffic : Payload.Traffic u v d where
  E := E
  src := src
  dst := dst
  length := size hd src x
  send := hx.point
  get e := (finCongr (h.size_eq hx hy e)).toEmbedding.trans (hy.point e)
  disjoint_send e e' i j he hv := hx.separate he (hx.spec e i) (hv.symm ▸ hx.spec e' j)
  disjoint_get e e' i j he hv := by
    let i' := i.cast (h.size_eq hx hy e)
    let j' := j.cast (h.size_eq hx hy e')
    change (hy.point e i').val = (hy.point e' j').val at hv
    exact hy.separate he (hy.spec e i') (hv.symm ▸ hy.spec e' j')
  covers j := by
    obtain ⟨e, t, ht⟩ := hy.onto hc j
    exact ⟨e, t.cast (h.size_eq hx hy e).symm, ht⟩

def assemble (u : B m → B w) (v : B m' → B w) (x : Rows m w p n) (y : Rows m' w p n)
    (peer : B (m + p) → B (m' + p)) : (Payload.Script m m' p w n).obj :=
  ((((u, fun i => (pack (x i)).1), (v, fun i => (pack (y i)).1)), peer),
    (fun i => (pack (x i)).2), (fun i => (pack (y i)).2))

theorem valid (a : B m → B w) (b : B m' → B w) (peer : B (m + p) → B (m' + p))
    (ha : ∀ i, (a i).val = u.length i) (hb : ∀ i, (b i).val = v.length i)
    (hp : ∀ e, 0 < size hd src x e → peer (PeerLayout.post hd (src e)) = PeerLayout.post hd (dst e)) :
    Payload.Script.Valid (traffic hx hy h hc) hd (assemble a b x y peer) := by
  refine ⟨⟨ha, hb, fun _ => rfl, fun e => (h.size_eq hx hy e).symm,
    hx.occupied, hy.occupied, hp⟩, fun _ => bounds _ (hx.fits _) (hx.unique _),
    fun _ => bounds _ (hy.fits _) (hy.unique _), fun e j => (hx.spec e j).at_bit,
    fun e j => (hy.spec e (j.cast (h.size_eq hx hy e))).at_bit⟩

theorem get_of_paired {e : E} {i j : B n} (hp : Paired hd src dst x y e i j) {a : ℕ}
    (ha : a < len (x (src e).1) i) :
    ∃ t : Fin ((traffic hx hy h hc).length e), t.val = start (x (src e).1) i + a ∧
      ((traffic hx hy h hc).send e t).val = offset (x (src e).1) i + a ∧
      ((traffic hx hy h hc).get e t).val = offset (y (dst e).1) j + a := by
  obtain ⟨he, hs⟩ := h.aligned hx hy hp
  obtain ⟨t, ht, hu⟩ := hx.used e i hp.source a ha
  obtain ⟨r, hr, hv⟩ := hy.used e j hp.target a (ha.trans_eq he)
  have eq : t.cast (h.size_eq hx hy e) = r := Fin.ext (ht.trans (by rw [hs, hr]))
  refine ⟨t, ht, hu, ?_⟩
  change (hy.point e (t.cast (h.size_eq hx hy e))).val = _
  rwa [eq]

theorem transmission (e : E) (t : Fin ((traffic hx hy h hc).length e)) :
    ∃ i j a, Paired hd src dst x y e i j ∧ a < len (x (src e).1) i ∧
      ((traffic hx hy h hc).send e t).val = offset (x (src e).1) i + a ∧
      ((traffic hx hy h hc).get e t).val = offset (y (dst e).1) j + a := by
  obtain ⟨i, a, hp, ha, ht, _⟩ := hx.spec e t
  obtain ⟨j, hj⟩ := h.partner hx hp (Nat.zero_lt_of_lt ha)
  obtain ⟨r, hr, hs, hg⟩ := get_of_paired hx hy h hc hj ha
  rw [show t = r from Fin.ext (ht.symm.trans hr.symm)]
  exact ⟨i, j, a, hj, ha, hs, hg⟩

/-- This equivalence applies to bit equality and to arbitrary predicates
on the two bank addresses. -/
theorem carries_iff (P : E → ℕ → ℕ → Prop) :
    (∀ e t, P e ((traffic hx hy h hc).send e t).val ((traffic hx hy h hc).get e t).val) ↔
      ∀ e i j, Paired hd src dst x y e i j → ∀ a, a < len (x (src e).1) i →
        P e (offset (x (src e).1) i + a) (offset (y (dst e).1) j + a) := by
  constructor
  · intro H e i j hp a ha
    obtain ⟨t, _, hs, hg⟩ := get_of_paired hx hy h hc hp ha
    rw [← hs, ← hg]
    exact H e t
  · intro H e t
    obtain ⟨i, j, a, hp, ha, hs, hg⟩ := transmission hx hy h hc e t
    rw [hs, hg]
    exact H _ _ _ hp _ ha

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! # Verifying a command against the two named exterior boundaries -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Coloring
open scoped Classical

variable {F : Type} [Field F] {S U : Scheme F} {x : S.format.obj} {y : U.format.obj}
  {a b : Wire} {G H : Diagram F a b} (p : S.Presentation x G) (q : U.Presentation y H)
  {V k V' k' : ℕ} (hx : S.Fits x V k) (hy : U.Fits y V' k')

def transferTo := S.transfer U hx hy (p.boundary ∘ q.boundary.symm)

theorem transfer_named (i : slots a ⊕ slots b) :
    p.transferTo q hx hy (U.index y hy (q.boundary i)) = S.index x hx (p.boundary i) := by
  simp only [transferTo, transfer, Function.comp_apply, Equiv.symm_apply_apply]

variable {l w n : ℕ} (cmd : (Payload.Script S.m U.m l w n).obj)

def Supplies : Prop :=
  ∃ M : Payload.Traffic (S.payload x hx) (U.payload y hy) (2 ^ l),
    Payload.Script.Valid M le_rfl cmd ∧ ∀ e t, p.transferTo q hx hy (M.target e t) = M.source e t

variable {p q hx hy cmd}
local notation "Z" => PeerLayout.S S.m V k U.m V' k' (2 ^ l)

theorem Supplies.carries (hs : p.Supplies q hx hy cmd) (i : Val a) (j : Val b)
    (out : (Fmt.payload U.m V' k').obj) :
    (Z).Carries (Payload.Script.decode le_rfl cmd) (S.store x hx (p.exterior i j)) out ↔
      U.store y hy (q.exterior i j) = out := by
  obtain ⟨M, hv, he⟩ := hs
  have hp : (p.exterior i j ∘ (S.index x hx).symm) ∘ p.transferTo q hx hy =
      q.exterior i j ∘ (U.index y hy).symm := by
    funext z
    obtain ⟨t, rfl⟩ := (U.index y hy).surjective z
    obtain ⟨k, rfl⟩ := q.boundary.surjective t
    simp only [Function.comp_apply, transfer_named, Equiv.symm_apply_apply, exterior_boundary]
  unfold store
  exact (hv.carries _ _).trans ((M.matches_iff _ he _ _).trans (by rw [hp, eq_comm]))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-! # Compiling endpoint words for a fixed list of payload contacts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring
open scoped Classical

abbrev Ports (m m' : ℕ) (E D : Format) := Format.pair (.vec m E) (.vec m' D)

variable {m m' w p n : ℕ} (q : B (m + p) → B (m' + p))
local notation "I" => entries w p n
local notation "R" => Row w p n
local notation "S" => Payload.Script m m' p w n

def organize (x : (Ports m m' R R).obj) : (S).obj :=
  ((((fun i => (x.1 i).1, fun i => (x.1 i).2.1), (fun i => (x.2 i).1, fun i => (x.2 i).2.1)), q),
    (fun i => (x.1 i).2.2), (fun i => (x.2 i).2.2))

def emit (x : (Ports m m' I I).obj) : (S).obj :=
  assemble (total ∘ x.1) (total ∘ x.2) (offsets ∘ x.1) (offsets ∘ x.2) q

def emitCost (m m' w p n : ℕ) :=
  (2 ^ m + 2 ^ m') * (2 ^ (n + p) * (100 + (2 * n + p + w)) ^ 140) +
    ((Ports m m' (Row w p n) (Row w p n)).width + 34 * (Payload.Script m m' p w n).width)

private theorem send (F : Type) [Field F] : Circuit F (Ports m m' R R) S (organize q)
    ((Ports m m' R R).width + 34 * (S).width) := by
  apply Window.Tile.project_const
  rintro ((((⟨i, j⟩|⟨i, j⟩)|(⟨i, j⟩|⟨i, j⟩))|⟨i, j⟩)|⟨i, j⟩|⟨i, j⟩)
  · exact .inl ⟨.inl (i, .inl j), fun _ => rfl⟩
  · exact .inl ⟨.inl (i, .inr (.inl j)), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inl j), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inl j)), fun _ => rfl⟩
  · exact .inr ⟨(Format.addr (m' + p)).code (q i) j, fun _ => rfl⟩
  · exact .inl ⟨.inl (i, .inr (.inr j)), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inr j)), fun _ => rfl⟩

theorem emit_net (F : Type) [Field F] :
    Circuit F (Ports m m' I I) S (emit q) (emitCost m m' w p n) := by
  let M := 2 ^ (n + p) * (100 + (2 * n + p + w)) ^ 140
  obtain ⟨k, hk, he⟩ := cheap_entries F w p n
  have make : Circuit F I R compile M := hk.mono (by unfold M; omega)
  have both := (Circuit.map _ (fun _ : B m => make)).par (Circuit.map _ (fun _ : B m' => make))
  have go := both.comp (send (w := w) (n := n) q F)
  have equal : (organize q ∘ Prod.map (fun (x : (Format.vec m I).obj) i => compile (x i))
    (fun (x : (Format.vec m' I).obj) i => compile (x i))) = emit q := rfl
  rw [equal] at go
  simpa only [emitCost, add_mul] using go

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-!
# Returning length declarations to a parent host

Append a query for each key after all the children's messages. The
first row of each key is a live message if present and an empty query
otherwise. A separate tag excludes zero-length declarations.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan.Scatter
open Coloring

abbrev Family (w z n : ℕ) := Format.vec z (entries w z n)
abbrev depth (z n : ℕ) := 1 + (z + n)
abbrev Key (n : ℕ) := Format.pair .bit (.addr n)

variable {z n w : ℕ}

def address : B (depth z n) ≃ B 1 × B z × B n :=
  (Assembly.Match.rowIndex 1 (z + n)).trans ((Equiv.refl _).prodCongr (Assembly.Match.rowIndex z n))

def query (i : B n) : B (depth z n) := address.symm (1, 0, i)

def body (x : (Family w z n).obj) (t : B (depth z n)) : (header w z n).obj :=
  let a := address t
  if a.1 = 0 then (a.2.1, (x a.2.1 a.2.2).2) else (0, 0, a.2.2)

def mark (t : B (depth z n)) (v : (header w z n).obj) : (Key n).obj :=
  (if (address t).1 = 0 then decide (v.2.1 = 0) else false, v.2.2)

def keys (x : (Family w z n).obj) := (Key n).keys (fun t => mark t (body x t))

def run (x : (Family w z n).obj) (i : B n) := body x (groupFirst (keys x) (query i))

private theorem first_key (x : (Family w z n).obj) (i : B n) :
    let t := groupFirst (keys x) (query i)
    mark t (body x t) = (false, i) := by
  have h := (Key n).serial.injective (first_spec (keys x) (query i)).1
  exact h.trans (by simp [mark, query, body])

theorem origin (x : (Family w z n).obj) (i : B n) (hi : 0 < (run x i).2.1.val) :
    ∃ c j, 0 < (x c j).2.1.val ∧ (x c j).2.2 = i ∧ run x i = (c, (x c j).2) := by
  let t := groupFirst (keys x) (query i)
  change 0 < (body x t).2.1.val at hi
  by_cases he : (address t).1 = 0
  · have hk : (body x t).2.2 = i := congrArg Prod.snd (first_key x i)
    simp only [body, he, ite_true] at hi hk
    exact ⟨_, _, hi, hk, ite_eq_left he⟩
  · simp [body, he] at hi

theorem positive (x : (Family w z n).obj) (c : B z) (j : B n)
    (hj : 0 < (x c j).2.1.val) : 0 < (run x (x c j).2.2).2.1.val := by
  let i := (x c j).2.2
  let t := groupFirst (keys x) (query i)
  let r : B (depth z n) := address.symm (0, c, j)
  have hn : (x c j).2.1 ≠ 0 := (show 0 < (x c j).2.1 from hj).ne'
  have eq : keys x r = keys x (query i) := by
    simp [keys, Format.keys, r, query, mark, body, hn, i]
  have hle : t ≤ r := (first_spec _ _).2 _ eq
  have he : (address t).1 = 0 := by
    by_contra he
    apply hle.not_gt
    rw [← address.symm_apply_apply t]
    exact (Scheme.rowIndex_lt _ _).mpr (.inl (pos_iff_ne_zero.mpr he))
  have hk : (mark t (body x t)).1 = false := congrArg Prod.fst (first_key x i)
  simp only [mark, he, ite_true, decide_eq_false_iff_not] at hk
  exact (show 0 < (body x t).2.1 from pos_iff_ne_zero.mpr hk)

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan.Scatter
end

/-! # Moving old exterior spans to subintervals of new exterior spans -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring
open scoped Classical

variable {F : Type} [Field F] {S U : Scheme F} {x : S.format.obj} {y : U.format.obj}
  {a b : Wire} {G H : Diagram F a b} (p : S.Presentation x G) (q : U.Presentation y H)
  {z w n : ℕ}

abbrev Entries (m w z n : ℕ) := B m → (entries w z n).obj

/-- A single contact carries all bits assigned to a given child. The
physical rows at both ends use the old row index as their pairing key. -/
structure Spec (child : B U.m ≃ B S.m × B z) (shift : S.Span → U.Span)
    (skip : S.Span → ℕ) (left right : S.Span → B n)
    (send : Entries S.m w z n) (take : Entries U.m w z n) : Prop where
  parent : ∀ t, 0 < S.borderLen x t → (child (shift t).1.1).1 = t.1.1
  bits : ∀ i, let u := (p.boundary i).val; let v := (q.boundary i).val
    v.1 = shift u.1 ∧ v.2.val = skip u.1 + u.2.val
  ordered : ∀ t t', 0 < S.borderLen x t → 0 < S.borderLen x t' →
    t.1.1 = t'.1.1 → S.spanOrd t < S.spanOrd t' → left t < left t'
  merged : ∀ t t', 0 < S.borderLen x t → 0 < S.borderLen x t' →
    (shift t).1.1 = (shift t').1.1 → right t < right t' →
    U.spanOrd (shift t) < U.spanOrd (shift t') ∨
      (shift t = shift t' ∧ skip t + S.borderLen x t ≤ skip t')
  source : ∀ t, 0 < S.borderLen x t →
    let a := send t.1.1 (left t)
    a.1 = (child (shift t).1.1).2 ∧ a.2.1.val = S.borderLen x t ∧ a.2.2 = left t
  target : ∀ t, 0 < S.borderLen x t →
    let a := take (shift t).1.1 (right t)
    a.1 = 0 ∧ a.2.1.val = S.borderLen x t ∧ a.2.2 = left t
  sourceCover : ∀ v i, 0 < (send v i).2.1.val →
    ∃ t, 0 < S.borderLen x t ∧ t.1.1 = v ∧ left t = i
  targetCover : ∀ v i, 0 < (take v i).2.1.val →
    ∃ t, 0 < S.borderLen x t ∧ (shift t).1.1 = v ∧ right t = i

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! # Comparing the physical span order with the logical bank order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Finset
open scoped Classical

namespace SpanPlan
variable {F : Type} [Field F] {S : Scheme F} {r : S.format.obj}
  {a b : Wire} {G : Diagram F a b} (p : S.Presentation r G) {z w n : ℕ}

abbrev Edge (a b : Wire) := slots a ⊕ slots b
abbrev here (i : Edge a b) := S.owner r (p.boundary i)
abbrev span (i : Edge a b) := (p.boundary i).val.1
abbrev sub (i : Edge a b) := (p.boundary i).val.2.val

structure Tiles (x : Entries S.m w z n) (row : Edge a b → B n) (off : Edge a b → ℕ) : Prop where
  bound : ∀ i, off i < (x (here p i) (row i)).2.1.val
  full : ∀ v j k, k < (x v j).2.1.val → ∃ i, here p i = v ∧ row i = j ∧ off i = k
  apart : ∀ i j, here p i = here p j → row i = row j → off i = off j → i = j
  sorted : ∀ i j, here p i = here p j → row i < row j ∨ row i = row j ∧ off i < off j →
    S.spanOrd (span p i) < S.spanOrd (span p j) ∨ span p i = span p j ∧ sub p i < sub p j

namespace Tiles
variable {p} {x : Entries S.m w z n} {row : Edge a b → B n} {off : Edge a b → ℕ}
  (h : Tiles p x row off) (v : B S.m)

private def orig (i : S.fiber r v) := p.boundary.symm i.val
private theorem local_host (i : S.fiber r v) : here p (orig (p:=p) v i) = v := by
  simp only [here, orig, Equiv.apply_symm_apply]; exact i.property

private abbrev L (x : Entries S.m w z n) (i : B n) := (x v i).2.1.val

private def tile : S.fiber r v ≃ Σ i : B n, Fin (L v x i) := by
  let g (i : S.fiber r v) := orig (p:=p) v i
  have host (i) : here p (g i) = v := local_host v i
  let f (i : S.fiber r v) : Σ j, Fin (L v x j) :=
    ⟨row (g i), ⟨off (g i), by simpa only [host] using h.bound (g i)⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j eq
    have e := h.apart (g i) (g j) ((host i).trans (host j).symm)
      (congrArg Sigma.fst eq) (congrArg (fun a => a.2.val) eq)
    exact Subtype.ext (p.boundary.symm.injective e)
  · rintro ⟨j, k⟩
    obtain ⟨i, hi, hj, hk⟩ := h.full _ _ k.val k.isLt
    refine ⟨⟨p.boundary i, hi⟩, ?_⟩
    apply Sigma.ext
    · simpa only [f, g, orig, Equiv.symm_apply_apply] using hj
    · apply (Fin.heq_ext_iff (by simp [f, g, orig, hj])).mpr
      simpa only [f, g, orig, Equiv.symm_apply_apply] using hk

include h in
theorem total_eq : (∑ i, (x v i).2.1.val) = S.load r v := by
  simpa only [Fintype.card_sigma, Fintype.card_fin, Scheme.load] using (Fintype.card_congr (h.tile v)).symm

variable {V k : ℕ} (hs : S.Fits r V k)

omit [Field F] in
private theorem index_lt (i j : S.exposed r) (hh : S.owner r i = S.owner r j)
    (ho : S.spanOrd i.val.1 < S.spanOrd j.val.1 ∨ i.val.1 = j.val.1 ∧ i.val.2.val < j.val.2.val) :
    (S.index r hs i).2.val < (S.index r hs j).2.val := by
  rw [S.index_val, S.index_val, hh]
  rcases ho with ho|⟨eq, hij⟩
  · have less : S.spanIndex i.val.1 < S.spanIndex j.val.1 := by
      change (Match.rowIndex _ _).symm
        ((Match.rowIndex S.h S.k).symm i.val.1.1.2, i.val.1.2) <
        (Match.rowIndex _ _).symm ((Match.rowIndex S.h S.k).symm j.val.1.1.2, j.val.1.2)
      simp [Scheme.spanOrd, Scheme.row, Scheme.rowIndex_lt, Prod.ext_iff] at ho ⊢
      tauto
    have small (u : S.exposed r) : u.val.2.val < S.extent r (S.owner r u) (S.spanIndex u.val.1) := by
      simp [Scheme.extent, Scheme.owner, u.property]
    have hi := small i
    rw [hh] at hi
    exact Routing.offset_lt (S.extent r (S.owner r j)) Fin.val
      (u := ⟨_, ⟨_, hi⟩⟩) (z := ⟨_, ⟨_, small j⟩⟩) less
  · rw [congrArg S.spanIndex eq]
    exact Nat.add_lt_add_left hij _

include h in
theorem ordinal (a : Edge a b) :
    (S.index r hs (p.boundary a)).2.val =
      (∑ j with j < row a, (x (here p a) j).2.1.val) + off a := by
  let v := here p a
  let e := (h.tile v).trans ((Routing.pack (L v x) Fin.val
    (fun _ _ _ _ he => Fin.ext he)).trans (finCongr (h.total_eq v)))
  let f (q : S.fiber r v) := orig (p:=p) v q
  have key (i j : S.fiber r v) (hi : e i < e j) :
      row (f i) < row (f j) ∨ row (f i) = row (f j) ∧ off (f i) < off (f j) := by
    rcases lt_trichotomy (row (f i)) (row (f j)) with lt|eq|gt
    · exact .inl lt
    · change Routing.offset (L v x) Fin.val (row (f i)) + off (f i) <
        Routing.offset (L v x) Fin.val (row (f j)) + off (f j) at hi
      exact .inr ⟨eq, by rw [eq] at hi; omega⟩
    · exact (hi.not_gt (Routing.offset_lt (L v x) Fin.val (u := h.tile v j) (z := h.tile v i) gt)).elim
  let idx (i : S.fiber r v) : Fin (S.load r v) :=
    ⟨(S.index r hs i.val).2.val, by
      have hb := (S.index r hs i.val).2.isLt
      change _ < S.load r (S.owner r i.val) at hb
      rwa [i.property] at hb⟩
  have mono : StrictMono (idx ∘ e.symm) := by
    intro i j hij
    let u := e.symm i
    let w := e.symm j
    have ho := h.sorted (f u) (f w) ((local_host v u).trans (local_host v w).symm)
      (key u w (by simpa [u, w] using hij))
    have ea (t : S.fiber r v) : p.boundary (f t) = t.val := p.boundary.apply_symm_apply _
    change (S.index r hs u.val).2.val < (S.index r hs w.val).2.val
    apply index_lt hs _ _ (u.property.trans w.property.symm)
    unfold span sub at ho
    rwa [ea u, ea w] at ho
  let i : S.fiber r v := ⟨p.boundary a, rfl⟩
  have he := congrFun mono.eq_id (e i)
  simp only [Function.comp_apply, Equiv.symm_apply_apply, id_eq] at he
  have hi := congrArg Fin.val he
  change _ = (∑ j with j < row (f i), (x v j).2.1.val) + off (f i) at hi
  rwa [show f i = a from p.boundary.symm_apply_apply a] at hi

end Tiles
end SpanPlan
end OAI.LinearAlgebra.MatrixExponent.Assembly
end
