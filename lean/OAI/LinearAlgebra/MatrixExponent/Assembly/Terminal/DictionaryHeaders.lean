import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortBack
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import Mathlib.Order.Interval.Finset.Fin
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Assembly.Hold
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress

/-! # Contracting two copies of a channel test with a station weight -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Kernel
open Coloring
open scoped Classical

variable {F : Type} [Field F] {u m n k : ℕ} {L : Set (Table F)} {A B C X Z : Format}

/-- Move the output record of a kernel to its input. -/
private theorem close {f : A.obj → B.obj → F} (h : Kernel F u L A B f m) (hu : 3 ≤ u) :
    Kernel F u L (A.pair B) (.wire .unit) (fun p _ => f p.1 p.2) (m + 4 * B.width) := by
  let a := word A.width
  let b := word B.width
  obtain ⟨s, hs, hf⟩ := h a b (names A) (names B)
  obtain ⟨t, ht, hg⟩ := (Tagged.cap (F := F) b).includeWide (L := L) hu
  have hw := (((hf.par hg).pre (Rewire.assoc a b b)).post (Rewire.swap .unit b)).trace
  refine of_layout (a := .pair a b) (b := .unit) ((names A).sumCongr (names B)) (.refl _)
    ⟨s + t, Nat.add_le_add hs (by simpa [b] using ht), ?_⟩
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hw
  exact hw

/-- Contract one latent tape with two constraints and a dictionary.
The exterior tape remains available as an independent argument. -/
theorem contract [Fintype Z.obj]
    {f : (A.pair Z).obj → Z.obj → F}
    {g : (B.pair Z).obj → X.obj → F} {c : C.obj → Z.obj → F}
    (hu : 3 ≤ u) (hf : Kernel F u L (A.pair Z) Z f m)
    (hg : Kernel F u L (B.pair Z) X g n) (hc : Kernel F u L C Z c k) :
    Kernel F u L (((A.pair B).pair C).pair X) (.wire .unit)
      (fun p _ => ∑ z, f (p.1.1.1, z) z * g (p.1.1.2, z) p.2 * c p.1.2 z)
      (m + n + k + 64 * (A.width + B.width + C.width + X.width + Z.width)) := by
  let Y := ((A.pair B).pair C).pair X
  let P := Y.pair Z
  let Q := (((A.pair Z).pair (B.pair Z)).pair C).pair ((Z.pair X).pair Z)
  let gather (p : P.obj) : Q.obj := ((((p.1.1.1.1, p.2), (p.1.1.1.2, p.2)), p.1.1.2), ((p.2, p.1.2), p.2))
  have hp : Circuit F P Q gather (P.width + 2 * Q.width) := by
    let atBit : Q.pins → P.pins
      | .inl (.inl (.inl (.inl i))) => .inl (.inl (.inl (.inl i)))
      | .inl (.inl (.inl (.inr i))) => .inr i
      | .inl (.inl (.inr (.inl i))) => .inl (.inl (.inl (.inr i)))
      | .inl (.inl (.inr (.inr i))) => .inr i
      | .inl (.inr i) => .inl (.inl (.inr i))
      | .inr (.inl (.inl i)) => .inr i
      | .inr (.inl (.inr i)) => .inl (.inr i)
      | .inr (.inr i) => .inr i
    exact Circuit.project atBit (by rintro _ ((((i|i)|(i|i))|i)|((i|i)|i)) <;> rfl)
  have joined := ((hf.par hg).par hc).close hu
  have result := (Map.circuit hu hp).then_kernel joined
  refine (sum_hidden (C := Z) hu result).mono ?_
  simp only [P, Q, Y, Format.width_pair]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Kernel
end

/-!
# A bank for the arguments of the live stations

The block order is unchanged. A station with no bits uses no
positions in the bank. Each live station uses a fixed-width record
of padded spans.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal

open Coloring
open scoped Classical
variable {F : Type} (S : Scheme F) (r : S.format.obj)

def Active (v : S.Vtx) := Nonempty (S.LocalPin r v)

abbrev Live := {v // Active S r v}

def position (v : Live S r) := v.val.1

abbrev localLive (i : B S.m) := {v : Live S r // position S r v = i}

def count (i : B S.m) := Fintype.card (localLive S r i)

def localIndex {i : B S.m} (v : localLive S r i) := (Match.rowIndex S.h S.k).symm v.val.val.2

private theorem local_inj {i : B S.m} : Function.Injective (localIndex S r (i := i)) := by
  intro a b h
  exact Subtype.ext (Subtype.ext (Prod.ext (a.2.trans b.2.symm)
    ((Match.rowIndex _ _).symm.injective h)))

def ordinal (i : B S.m) : localLive S r i ≃ Fin (count S r i) :=
  letI : LinearOrder (localLive S r i) := LinearOrder.lift' _ (local_inj S r)
  (Fintype.orderIsoFinOfCardEq _ rfl).toEquiv.symm

def serial : Live S r ≃ Σ i, Fin (count S r i) :=
  (Equiv.sigmaFiberEquiv (position S r)).symm.trans (Equiv.sigmaCongrRight (ordinal S r))

def height (t : ℕ) := S.h + S.k + (S.e + t)

structure Fits (V t : ℕ) : Prop where
  width : ∀ p, S.width r p ≤ 2 ^ t
  total : 2 ^ S.m + Fintype.card (Live S r) * 2 ^ (S.e + t) ≤ V

variable {V t : ℕ} (h : Fits S r V t)

def bank : Payload S.m V (height S t) where
  length i := count S r i * 2 ^ (S.e + t)
  total := by
    have hc : Fintype.card (Live S r) = ∑ i, count S r i := by
      rw [Fintype.card_congr (serial S r), Fintype.card_sigma]
      simp
    refine le_trans ?_ h.total
    rw [hc, Finset.sum_mul]
    have := Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
      show max 1 (count S r i * 2 ^ (S.e + t)) ≤ 1 + count S r i * 2 ^ (S.e + t) by omega
    simpa [Finset.sum_add_distrib] using this
  longest i := by
    have he := Fintype.card_le_of_injective _ (local_inj S r (i := i))
    rw [Fintype.card_fin] at he
    unfold height
    rw [pow_add 2 (S.h + S.k) (S.e + t)]
    exact Nat.mul_le_mul_right _ he

abbrev Row (S : Scheme F) (t : ℕ) := B S.e × B t
abbrev Data (t : ℕ) := Live S r × Row S t

def index : Data S r t ≃ (bank S r h).Bit :=
  ((serial S r).prodCongr (Match.rowIndex S.e t).symm).trans
    ((Equiv.sigmaProdDistrib _ _).trans (Equiv.sigmaCongrRight fun _ => finProdFinEquiv))

def pin : S.Pin r ↪ Data S r t where
  toFun i := (⟨i.1.1, ⟨i.1.2, i.2⟩⟩, i.1.2, i.2.castLE (h.width i.1))
  inj' x y he := by
    have ha : x.1.1 = y.1.1 := congrArg (fun i => i.1.val) he
    have hb : x.1.2 = y.1.2 := congrArg (fun i => i.2.1) he
    have hc : x.2.val = y.2.val := congrArg (fun i => i.2.2.val) he
    have hd : x.1 = y.1 := Prod.ext ha hb
    exact Sigma.ext hd ((Fin.heq_ext_iff (congrArg _ hd)).mpr hc)

def place : S.Pin r ↪ (bank S r h).Bit := (pin S r h).trans (index S r h).toEmbedding

def slot : Data S r t ↪ Fmt.Port S.m V (height S t) :=
  (index S r h).toEmbedding.trans (bank S r h).wire

def wire : S.Pin r ↪ Fmt.Port S.m V (height S t) := (pin S r h).trans (slot S r h)

def store (z : S.Pin r → Bool) : (Fmt.payload S.m V (height S t)).obj :=
  (bank S r h).store (Function.extend (place S r h) z (fun _ => false))

@[simp] theorem read_store (z : S.Pin r → Bool) (i : S.Pin r) :
    store S r h z (wire S r h i) = z i := by
  change (bank S r h).store _ ((bank S r h).wire (place S r h i)) = _
  rw [Payload.read_store, (place S r h).injective.extend_apply]

theorem store_injective : Function.Injective (store S r h) := by
  intro x y he
  funext i
  simpa using congrFun he (wire S r h i)

theorem pin_range (i : Data S r t) : i ∈ Set.range (pin S r h) ↔ i.2.2.val < S.width r (i.1.val, i.2.1) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact p.2.isLt
  · intro hp
    exact ⟨⟨(i.1.val, i.2.1), i.2.2.val, hp⟩, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! # Reserved payload space for each lane at an active station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring Finset
open scoped Classical

variable {F : Type} (S : Scheme F) (r : S.format.obj) (t : ℕ)

def chunk (s : S.Span) : ℕ := if Active S r s.1 then 2 ^ t else 0

def chunkStart (s : S.Span) :=
  ∑ j with j < S.spanIndex s, chunk S r t (S.hostSpan (s.1.1, j))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# Addresses in the padded terminal bank

Compaction removes inactive stations in order. Every lane of a
surviving station has one chunk, even if the lane itself is empty.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring Finset
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {v : B S.m}

private abbrev Lane (S : Scheme F) (r : S.format.obj) (v : B S.m) := localLive S r v × B S.e

private def original (p : Lane S r v) := S.spanIndex (p.1.val.val, p.2)

private theorem restore (p : Lane S r v) : S.hostSpan (v, original p) = (p.1.val.val, p.2) :=
  (congrArg (fun j => S.hostSpan (j, original p)) p.1.property.symm).trans
    (S.hostSpan_spanIndex (p.1.val.val, p.2))

private def ordinalLane (S : Scheme F) (r : S.format.obj) (v : B S.m) :
    Lane S r v ≃ Fin (count S r v * 2 ^ S.e) :=
  ((ordinal S r v).prodCongr (Equiv.refl _)).trans finProdFinEquiv

private theorem sum_lanes (f : B S.spanRows → ℕ) :
    (∑ j, if Active S r (S.hostSpan (v, j)).1 then f j else 0) =
      ∑ p : Lane S r v, f (original p) := by
  rw [←sum_filter]
  symm
  refine sum_bij (fun p _ => original p) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p _
    rw [mem_filter, restore]
    exact ⟨mem_univ _, p.1.val.property⟩
  · intro p _ q _ he
    have h := (restore p).symm.trans ((congrArg (fun j => S.hostSpan (v, j)) he).trans (restore q))
    exact Prod.ext (Subtype.ext (Subtype.ext (Prod.mk.inj h).1)) (Prod.mk.inj h).2
  · intro j hj
    let x := S.hostSpan (v, j)
    exact ⟨(⟨⟨x.1, (mem_filter.mp hj).2⟩, rfl⟩, x.2), mem_univ _, S.spanIndex_hostSpan v j⟩

private theorem pair_lt {n m : ℕ} (i j : Fin n) (p q : Fin m) :
    p.val + m * i.val < q.val + m * j.val ↔ i < j ∨ i = j ∧ p < q := by
  rcases lt_trichotomy i j with h|rfl|h
  · have := Nat.mul_le_mul_left m (show i.val + 1 ≤ j.val from h)
    rw [mul_add, mul_one] at this
    omega
  · simp
  · have := Nat.mul_le_mul_left m (show j.val + 1 ≤ i.val from h)
    rw [mul_add, mul_one] at this
    omega

private theorem lift_lt {I : Type} [Fintype I] {n : ℕ} (f : I → B n)
    (hf : Function.Injective f) (i j : I) :
    letI := LinearOrder.lift' f hf
    let o := (Fintype.orderIsoFinOfCardEq I rfl).symm
    o i < o j ↔ f i < f j := by
  let : LinearOrder I := LinearOrder.lift' f hf
  exact (Fintype.orderIsoFinOfCardEq I rfl).symm.lt_iff_lt

private theorem original_lt (p q : Lane S r v) :
    original p < original q ↔ ordinalLane S r v p < ordinalLane S r v q := by
  have hf : Function.Injective (localIndex S r (i := v)) := by
    intro x y h
    exact Subtype.ext (Subtype.ext (Prod.ext (x.property.trans y.property.symm)
      ((Match.rowIndex _ _).symm.injective h)))
  have h : ordinal S r v p.1 < ordinal S r v q.1 ↔ localIndex S r p.1 < localIndex S r q.1 :=
    lift_lt _ hf p.1 q.1
  change (p.2.val + 2 ^ S.e * (localIndex S r p.1).val < q.2.val + 2 ^ S.e * (localIndex S r q.1).val) ↔
    (p.2.val + 2 ^ S.e * (ordinal S r v p.1).val < q.2.val + 2 ^ S.e * (ordinal S r v q.1).val)
  simp only [pair_lt, h, hf.eq_iff, (ordinal S r v).injective.eq_iff]

variable {V t : ℕ} (h : Fits S r V t)

theorem chunks_sum (i : B S.m) :
    (∑ j, chunk S r t (S.hostSpan (i, j))) = (bank S r h).length i := by
  unfold chunk
  rw [sum_lanes]
  simp [bank, Lane, count, pow_add, mul_assoc]

private theorem chunk_start (p : Lane S r v) :
    chunkStart S r t (p.1.val.val, p.2) = (ordinalLane S r v p).val * 2 ^ t := by
  have he : p.1.val.val.1 = v := p.1.property
  simp only [chunkStart, he, sum_filter, chunk]
  have swap (i : B S.spanRows) :
      (if i < S.spanIndex (p.1.val.val, p.2) then if Active S r (S.hostSpan (v, i)).1 then 2 ^ t else 0 else 0) =
        if Active S r (S.hostSpan (v, i)).1 then if i < original p then 2 ^ t else 0 else 0 := by
    unfold original
    split_ifs <;> rfl
  simp_rw [swap]
  rw [sum_lanes]
  simp_rw [original_lt]
  rw [Equiv.sum_comp (ordinalLane S r v) (fun i => if i < ordinalLane S r v p then 2 ^ t else 0), ←sum_filter]
  rw [show (univ.filter fun i => i < ordinalLane S r v p) = Iio (ordinalLane S r v p) by ext; simp]
  simp

theorem index_val (i : Data S r t) :
    (index S r h i).2.val = chunkStart S r t (i.1.val, i.2.1) + i.2.2.val := by
  let v := position S r i.1
  let p : Lane S r v := (⟨i.1, rfl⟩, i.2.1)
  change (index S r h i).2.val = chunkStart S r t (p.1.val.val, p.2) + i.2.2.val
  rw [chunk_start]
  change i.2.2.val + 2 ^ t * i.2.1.val + 2 ^ (S.e + t) * (ordinal S r v p.1).val =
    (i.2.1.val + 2 ^ S.e * (ordinal S r v p.1).val) * 2 ^ t + i.2.2.val
  rw [pow_add]
  ring

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! # Summing over a padded bank of station arguments -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal

open Coloring
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {V t : ℕ}
  (h : Fits S r V t)

abbrev Tape (S : Scheme F) (V t : ℕ) := (Fmt.payload S.m V (height S t)).obj

def outerZero (z : Tape S V t) := ∀ i ∉ Set.range (bank S r h).wire, z i = false

def innerZero (z : Tape S V t) :=
  ∀ i : Data S r t, S.width r (i.1.val, i.2.1) ≤ i.2.2.val → z (slot S r h i) = false

theorem padded (z : S.Pin r → Bool) :
    outerZero h (store S r h z) ∧ innerZero h (store S r h z) := by
  refine ⟨(bank S r h).padding _, fun i hi => ?_⟩
  have he : index S r h i ∉ Set.range (place S r h) := by
    rintro ⟨p, he⟩
    exact hi.not_gt ((pin_range S r h i).mp ⟨p, (index S r h).injective he⟩)
  change (bank S r h).store _ ((bank S r h).wire _) = false
  rw [Payload.read_store]
  exact Function.extend_apply' _ _ _ he

theorem unpack (z : Tape S V t) (ho : outerZero h z) (hi : innerZero h z) :
    z = store S r h (z ∘ wire S r h) := by
  apply Payload.store_unique _ _ _ _ ho
  intro j
  by_cases he : j ∈ Set.range (place S r h)
  · obtain ⟨p, rfl⟩ := he
    rw [(place S r h).injective.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ he]
    obtain ⟨i, rfl⟩ := (index S r h).surjective j
    apply hi
    apply le_of_not_gt
    intro hb
    obtain ⟨p, rfl⟩ := (pin_range S r h i).mpr hb
    exact he ⟨p, rfl⟩

variable [Field F]

/-- Empty stations outside the bank are neutral. -/
def Neutral (S : Scheme F) (r : S.format.obj) :=
  ∀ v, ¬Active S r v → ∀ z, S.table r v z = 1

def localValue (z : Tape S V t) : F :=
  if innerZero h z then ∏ v : Live S r, S.table r v.val (z ∘ wire S r h ∘ S.port r v.val) else 0

theorem localValue_store (hn : Neutral S r) (z : S.Pin r → Bool) :
    localValue h (store S r h z) = ∏ v, S.table r v (z ∘ S.port r v) := by
  rw [localValue, ite_eq_left (padded h z).2]
  have he (v : Live S r) : store S r h z ∘ wire S r h ∘ S.port r v.val = z ∘ S.port r v.val :=
    funext (fun i => read_store _ _ _ _ _)
  simp_rw [he]
  rw [← Finset.prod_subtype (Finset.univ.filter (Active S r)) Finset.mem_filter_univ
    (fun v => S.table r v (z ∘ S.port r v))]
  exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi =>
    hn i (fun ha => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, ha⟩)) _

/-- Equality checks need only be characterized on canonical encodings.
On rejected outer padding they must vanish. -/
theorem contract (hn : Neutral S r) (x : S.exposed r → Bool)
    (check : Tape S V t → F) (hmask : ∀ z, check z ≠ 0 → outerZero h z)
    (he : ∀ z, check (store S r h z) = if S.Agrees r x z then 1 else 0) :
    ∑ z, check z * localValue h z = S.eval r x := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (store S r h)))]
  · rw [Finset.sum_image (store_injective S r h).injOn]
    unfold Scheme.eval
    simp only [he, localValue_store h hn, ite_mul, one_mul, zero_mul]
  · intro z _ hout
    by_cases h₀ : check z = 0
    · simp only [h₀, zero_mul]
    by_cases hi : innerZero h z
    · exact (hout (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, (unpack h z (hmask z h₀) hi).symm⟩)).elim
    · simp only [localValue, hi, ite_false, mul_zero]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! # A shared station table on complete records of the physical bank -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Dictionary

open Coloring Transcript
open scoped Classical
variable {F : Type} (S : Scheme F) (V t : ℕ)

abbrev Seat := Σ s : Slot (2 ^ S.m) V (height S t), Fin (capacity s / 2 ^ (S.e + t))
abbrev header := Format.pair .bit (.pair (.addr S.ℓ) (.addr S.k))
abbrev headers := Fmt.pi (fun _ : Seat S V t => header S)

def port (a : Seat S V t) (i : Row S t) : Fmt.Port S.m V (height S t) :=
  ⟨a.1, (finProdFinEquiv (a.2, (Match.rowIndex S.e t).symm i)).castLE (Nat.div_mul_le_self _ _)⟩

theorem footprint : Fintype.card (Seat S V t) * 2 ^ (S.e + t) ≤
    (Fmt.payload S.m V (height S t)).width := by
  simp only [Seat, Format.width, Fmt.payload, Fmt.Port, Fintype.card_sigma, Fintype.card_fin, Finset.sum_mul]
  exact Finset.sum_le_sum fun _ _ => Nat.div_mul_le_self _ _

def pad : (header S).obj := (false, 0, 0)

def name (r : S.format.obj) (v : Live S r) : (header S).obj :=
  (true, (r v.val.1).2 v.val.2.1, v.val.2.2)

variable {S V t} {r : S.format.obj} (h : Fits S r V t)

def seat : Live S r ↪ Seat S V t :=
  (serial S r).toEmbedding.trans (Function.Embedding.sigmaMap
    ⟨(bank S r h).seat.write, (bank S r h).seat.injective⟩
    (fun i => Fin.castLEEmb ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
      ((bank S r h).fits i))))

theorem seat_port (v : Live S r) (i : Row S t) :
    port S V t (seat h v) i = slot S r h (v, i) := rfl

def encode : (headers S V t).obj :=
  Function.extend (seat h) (name S r) (fun _ => pad S)

@[simp] theorem encode_seat (v : Live S r) : encode h (seat h v) = name S r v :=
  (seat h).injective.extend_apply _ _ _

theorem encode_pad (a : Seat S V t) (ha : a ∉ Set.range (seat h)) :
    encode h a = pad S := Function.extend_apply' _ _ _ ha

variable [Field F] (S V t)

def entry (q : (header S).obj) (x : Row S t → Bool) : F :=
  let p := S.decode q.2.1
  let j := q.2.2
  if q.1 then
    if ∀ i : Row S t, p.width j i.1 ≤ i.2.val → x i = false then
      p.value j (fun s i => x (s, Fin.ofNat _ i.val))
    else 0
  else 1

def weight (q : (headers S V t).obj) (z : Tape S V t) : F :=
  ∏ a, entry S t (q a) (z ∘ port S V t a)

variable {S V t}

private theorem entry_seat (z : Tape S V t) (v : Live S r) :
    entry S t (name S r v) (z ∘ port S V t (seat h v)) =
      if ∀ i : Row S t, S.width r (v.val, i.1) ≤ i.2.val → z (slot S r h (v, i)) = false then
        S.table r v.val (z ∘ wire S r h ∘ S.port r v.val) else 0 := by
  unfold entry name
  simp only [ite_true, Function.comp_apply, seat_port]
  congr 1
  apply congrArg ((S.pattern r v.val).value v.val.2.2)
  funext s i
  have he : Fin.ofNat (2 ^ t) i.val = i.castLE (h.width (v.val, s)) :=
    Fin.ext (Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt (h.width (v.val, s))))
  rw [he]
  rfl

theorem weight_encode (z : Tape S V t) : weight S V t (encode h) z = localValue h z := by
  unfold weight
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image (seat h)))]
  · rw [Finset.prod_image (seat h).injective.injOn]
    simp_rw [encode_seat, entry_seat]
    unfold localValue
    by_cases hi : innerZero h z
    · rw [ite_eq_left hi]
      exact Finset.prod_congr rfl fun v _ => ite_eq_left (fun i => hi (v, i))
    · rw [ite_eq_right hi]
      obtain ⟨⟨v, i⟩, hv⟩ := not_forall.mp hi
      exact Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right (fun hh => hv (hh i)))
  · intro a _ ha
    have he : a ∉ Set.range (seat h) := by simpa using ha
    rw [encode_pad h a he]
    rfl

variable (S V t)

abbrev record := Format.pair (header S) ⟨Row S t → Bool, Row S t, Equiv.refl _⟩
def arity := (header S).width + 2 ^ (S.e + t)
def price := 40 * ((headers S V t).width + (Fmt.payload S.m V (height S t)).width)

omit [Field F] in
theorem width_record : (record S t).width = arity S t := by
  rw [Format.width_pair]
  simp [arity, Format.width, Row, pow_add]

private def look (z : (record S t).pins → Bool) : F :=
  let x := (record S t).code.symm z
  entry S t x.1 x.2

def label : Table F :=
  let A := record S t
  ⟨word A.width, .unit, fun x _ => look S t (bits (word A.width) x ∘ names A)⟩

variable {S V t} {u : ℕ} {L : Set (Table F)}

private theorem one (ha : arity S t ≤ u) (hl : label S t ∈ L) :
    WideWeight F u L (look S t) (1 + arity S t) := by
  let A := record S t
  let a := word A.width
  let f := fun (x : Val a) (_ : Val .unit) => look S t (bits a x ∘ names A)
  have he : wd a = arity S t := (wd_word _).trans (width_record S t)
  have hw : Wide F u L a .unit f (1 + wd a) :=
    Wide.table _ _ _ (he.le.trans ha) (.inr hl)
  intro b j
  refine ⟨1 + wd a, by rw [he], ?_⟩
  simpa [f, Function.comp_def] using hw.pre (rewire_reindex ((names A).symm.trans j))

theorem realize (hu : 3 ≤ u) (ha : arity S t ≤ u) (hl : label S t ∈ L) :
    Kernel F u L (headers S V t) (Fmt.payload S.m V (height S t))
      (weight S V t) (price S V t) := by
  let A := headers S V t
  let D := Fmt.payload S.m V (height S t)
  let k := fun _ : Seat S V t => look S t
  let read (i : Seat S V t) : (record S t).pins → (A.pins ⊕ D.pins) ⊕ Empty
    | .inl p => .inl (.inl ⟨i, p⟩)
    | .inr p => .inl (.inr (port S V t i p))
  have hw := Kernel.factors (A := A) (B := D) k read (fun _ => 1 + arity S t) hu
    (fun _ => one ha hl)
  have he (q : A.obj) (z : D.obj) :
      weightedSum k read (Sum.elim (A.code q) (D.code z)) = weight S V t q z := by
    unfold weightedSum weight
    rw [Fintype.sum_unique]
    apply Finset.prod_congr rfl
    intro i _
    change entry S t ((header S).code.symm ((header S).code (q i))) _ = _
    rw [Equiv.symm_apply_apply]
    rfl
  simp only [he] at hw
  apply hw.mono
  have hb := footprint S V t
  have hc := (Nat.le_mul_of_pos_right (Fintype.card (Seat S V t)) (Nat.two_pow_pos (S.e + t))).trans hb
  simp only [price, A, D, arity, headers, Fmt.width_pi, Finset.sum_const, Finset.card_univ,
    Nat.nsmul_eq_mul, Fintype.card_empty, mul_add, mul_one]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Dictionary
end

/-! # Stable compaction of station headers on one host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header

open Coloring Dictionary
open scoped Classical
variable {F : Type} (S : Scheme F) (r : S.format.obj)

abbrev n := S.h + S.k
abbrev key := Format.pair (.addr S.ℓ) (.addr S.k)
abbrev line := Format.vec (n S) (header S)
abbrev wordSize (t : ℕ) := S.e + t + 1 + n S

def labels (i : B S.m) (j : B (n S)) : (key S).obj :=
  ((r i).2 (Match.rowIndex S.h S.k j).1, (Match.rowIndex S.h S.k j).2)

def select (x : (key S).obj) : (header S).obj :=
  if Nonempty (Σ s, Fin ((S.decode x.1).width x.2 s)) then (true, x) else pad S

def row (i : B S.m) : (line S).obj := select S ∘ labels S r i

def flag (b : Bool) : B 1 := if b then 0 else 1

def keys (x : (line S).obj) := fun j => flag (x j).1

def pack (x : (line S).obj) := x ∘ Coloring.order (keys S x)

def amount (t : ℕ) (b : Bool) : B (S.e + t + 1) :=
  if b then ⟨2 ^ (S.e + t), Nat.pow_lt_pow_right (by decide) (by omega)⟩ else 0

def length (t : ℕ) (x : (line S).obj) := total (n S) (S.e + t + 1) (fun j => amount S t (x j).1)

variable {S r} {i : B S.m}

private theorem local_inj : Function.Injective (localIndex S r (i := i)) := by
  intro a b h
  exact Subtype.ext (Subtype.ext (Prod.ext (a.2.trans b.2.symm)
    ((Match.rowIndex _ _).symm.injective h)))

private theorem row_live (v : localLive S r i) :
    row S r i (localIndex S r v) = name S r v.val := by
  rcases v with ⟨⟨⟨a, b⟩, hv⟩, rfl⟩
  simp only [row, Function.comp_apply, labels, localIndex, Equiv.apply_symm_apply]
  exact ite_eq_left hv

private theorem row_other (j : B (n S)) (hj : j ∉ Set.range (localIndex S r (i:=i))) :
    row S r i j = pad S := by
  apply ite_eq_right
  intro hv
  exact hj ⟨⟨⟨(i, Match.rowIndex S.h S.k j), hv⟩, rfl⟩, (Match.rowIndex _ _).symm_apply_apply j⟩

private theorem marked (j : B (n S)) :
    keys S (row S r i) j = 0 ↔ j ∈ Set.range (localIndex S r (i:=i)) := by
  by_cases hj : j ∈ Set.range (localIndex S r (i:=i))
  · obtain ⟨v, rfl⟩ := hj
    simp [keys, row_live, name, flag]
  · simp [keys, row_other j hj, pad, flag, hj]

theorem length_row (t : ℕ) (i : B S.m) :
    (length S t (row S r i)).val = count S r i * 2 ^ (S.e + t) := by
  change ∑ j, (amount S t (row S r i j).1).val = _
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (localIndex S r (i:=i))))]
  · rw [Finset.sum_image local_inj.injOn]
    simp [row_live, name, amount, count]
  · intro j _ hj
    have ho : j ∉ Set.range (localIndex S r (i:=i)) := by simpa using hj
    rw [row_other j ho]
    rfl

private theorem rank_index {I : Type} [Fintype I] {m : ℕ} (f : B m → B 1)
    (index : I → B m) (hindex : Function.Injective index)
    (h : ∀ u, f (index u) = 0) (hc : Control.histogram f 0 none = Fintype.card I) (v : I) :
    letI := LinearOrder.lift' index hindex
    ((Coloring.order f).symm (index v)).val = ((Fintype.orderIsoFinOfCardEq I rfl).symm v).val := by
  let a := f ∘ Coloring.order f
  let j := (Coloring.order f).symm (index v)
  have hj : a j = 0 := by simp [a, j, h]
  have hz : a 0 = a j := le_antisymm (order_mono f (Fin.zero_le _)) (by rw [hj]; exact Fin.zero_le _)
  have hl : leader a j = 0 :=
    le_antisymm ((leader_spec a (order_mono f) j).2 0 hz) (Fin.zero_le _)
  let g (u : I) : Fin (Fintype.card I) := ⟨Control.rank f (index u), by
    simpa only [h, hc] using Control.rank_lt f (index u)⟩
  let _ : LinearOrder I := LinearOrder.lift' _ hindex
  let e := Fintype.orderIsoFinOfCardEq (I) rfl
  have hm : StrictMono (g ∘ e) := fun x y hxy =>
    Control.rank_mono f ((h _).trans (h _).symm) (e.strictMono hxy)
  have he := congrFun hm.eq_id (e.symm v)
  simp only [Function.comp_apply, OrderIso.apply_symm_apply, id_eq] at he
  change j.val = (e.symm v).val
  rw [← he]
  change _ = Control.rank f (index v)
  rw [← groupRank_val]
  change _ = (j - leader a j).val
  rw [hl, sub_zero]

private theorem rank_live (v : localLive S r i) :
    ((Coloring.order (keys S (row S r i))).symm (localIndex S r v)).val =
      (ordinal S r i v).val := by
  let f := keys S (row S r i)
  have h (u : localLive S r i) : f (localIndex S r u) = 0 := (marked _).mpr ⟨u, rfl⟩
  have hc : Control.histogram f 0 none = count S r i := by
    rw [Control.histogram_none]
    have he : Finset.univ.filter (fun j => f j = 0) = Finset.univ.image (localIndex S r (i:=i)) := by
      ext j
      simpa only [Finset.mem_filter_univ, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
        using (marked (S:=S) (r:=r) (i:=i) j)
    rw [he, Finset.card_image_of_injective _ local_inj]
    rfl
  exact rank_index f (localIndex S r) local_inj h hc v

theorem pack_live (v : localLive S r i) (j : B (n S)) (hj : j.val = (ordinal S r i v).val) :
    pack S (row S r i) j = name S r v.val := by
  have he := Fin.ext (hj.trans (rank_live v).symm)
  rw [pack, Function.comp_apply, he, Equiv.apply_symm_apply, row_live]

theorem pack_other (j : B (n S)) (hj : ∀ v : localLive S r i, j.val ≠ (ordinal S r i v).val) :
    pack S (row S r i) j = pad S := by
  apply row_other
  rintro ⟨v, hv⟩
  apply hj v
  rw [← rank_live v, hv, Equiv.symm_apply_apply]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header
end

/-! # Distributing station headers into the physical dictionary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header
open Coloring Transcript Dictionary
open scoped Classical
variable {F : Type} (S : Scheme F) (V t : ℕ)

abbrev source := Redistribute.input S.m (wordSize S t) (line S)
abbrev dest := Redistribute.output S.m V (height S t) (line S)

def paired (r : S.format.obj) : (source S t).obj :=
  (fun i => length S t (row S r i), fun i => pack S (row S r i))

private theorem limit (a : Slot (2 ^ S.m) V (height S t)) :
    capacity a / 2 ^ (S.e + t) ≤ 2 ^ (n S) := by
  have he : capacity a ≤ 2 ^ (n S) * 2 ^ (S.e + t) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ a.1.isLt)
  exact Nat.div_le_of_le_mul (by simpa only [mul_comm] using he)

def pick (a : Seat S V t) : B (n S) := a.2.castLE (limit S V t a.1)

def cut (z : (dest S V t).obj) (a : Seat S V t) := z a.1 (pick S V t a)

def eval (r : S.format.obj) : (headers S V t).obj :=
  cut S V t (Redistribute.eval (line S) (fun _ => pad S) (paired S t r))

theorem width_dest : (dest S V t).width ≤ (height S t + 1) * (2 ^ S.m * (line S).width) := by
  simp only [dest, Redistribute.output, Fmt.width_pi, Finset.sum_const, Finset.card_univ,
    Nat.nsmul_eq_mul, ← mul_assoc]
  exact Nat.mul_le_mul_right _ (Transcript.card_slots _ _ _)

theorem width_headers : (headers S V t).width ≤ (dest S V t).width := by
  simp only [headers, dest, Redistribute.output, Fmt.width_pi, line, Format.width_vec]
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro a _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  exact Nat.mul_le_mul_right _ (limit S V t a)

variable {S V t} {r : S.format.obj} (h : Fits S r V t)

theorem correct : eval S V t r = encode h := by
  unfold eval
  rw [Redistribute.correct (bank S r h) _ _ _ (length_row t)]
  funext a
  simp only [cut]
  by_cases he : a ∈ Set.range (seat h)
  · obtain ⟨v, rfl⟩ := he
    have hs : (bank S r h).seat.read (seat h v).1 = some (position S r v) :=
      ((bank S r h).seat.valid _ _).mpr rfl
    rw [hs, encode_seat]
    exact pack_live (⟨v, rfl⟩ : localLive S r (position S r v)) _ rfl
  · rw [encode_pad h a he]
    cases hs : (bank S r h).seat.read a.1 with
    | none => rfl
    | some i =>
      refine pack_other (S:=S) (r:=r) (i:=i) (pick S V t a) ?_
      rintro ⟨v, rfl⟩ hv
      apply he
      have hf : (seat h v).1 = a.1 := (((bank S r h).seat.valid _ _).mp hs).symm
      exact ⟨v, Sigma.ext hf ((Fin.heq_ext_iff (congrArg (fun s => capacity s / 2 ^ (S.e + t)) hf)).mpr hv.symm)⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header
end
