import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal
import Mathlib.Algebra.BigOperators.Fin
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute

/-!
# The exterior payload bank of a stage

Only the occupied prefix of each assigned slot stores data.
All other positions are pinned to zero. The physical width
depends on the total length allowance, up to a factor for the
number of dyadic levels.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring Transcript
open scoped Classical

namespace Fmt

abbrev Port (m V k : ℕ) := Σ s : Slot (2 ^ m) V k, Fin (capacity s)

abbrev payload (m V k : ℕ) : Format := ⟨Port m V k → Bool, Port m V k, Equiv.refl _⟩

theorem width_payload (m V k : ℕ) : (payload m V k).width ≤ (k + 1) * (2 * V) := by
  simpa only [Format.width, payload, Fintype.card_sigma, Fintype.card_fin] using
    sum_capacity (2 ^ m) V k

end Fmt

variable {m V k : ℕ}

/-- An empty host takes one unit, so the usual dyadic capacity
bounds apply without an exception at zero. -/
structure Payload (m V k : ℕ) where
  length : B m → ℕ
  total : ∑ i, max 1 (length i) ≤ V
  longest : ∀ i, length i ≤ 2 ^ k

namespace Payload
variable (p : Payload m V k)

abbrev Bit := Σ i, Fin (p.length i)

def seat : Selector (B m) (Slot (2 ^ m) V k) :=
  Selector.packed (fun i => max 1 (p.length i)) (fun _ => lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) (by simp)
    p.total (fun i => max_le (Nat.two_pow_pos k) (p.longest i))

theorem fits (i : B m) : p.length i ≤ capacity (p.seat.write i) :=
  (le_max_right 1 _).trans (Selector.packed_size (fun t => max 1 (p.length t)) _ _ _ _ i)

/-- Number each channel's bits in their original order. -/
def wire : p.Bit ↪ Fmt.Port m V k :=
  Function.Embedding.sigmaMap ⟨p.seat.write, p.seat.injective⟩ (fun i => Fin.castLEEmb (p.fits i))

def store (f : p.Bit → Bool) : (Fmt.payload m V k).obj :=
  Function.extend p.wire f (fun _ => false)

@[simp] theorem read_store (f : p.Bit → Bool) (i : p.Bit) : p.store f (p.wire i) = f i :=
  p.wire.injective.extend_apply _ _ _

theorem padding (f : p.Bit → Bool) (i : Fmt.Port m V k) (hi : i ∉ Set.range p.wire) :
    p.store f i = false := Function.extend_apply' _ _ _ hi

theorem store_unique (f : p.Bit → Bool) (x : (Fmt.payload m V k).obj)
    (hr : ∀ i, x (p.wire i) = f i) (hz : ∀ i ∉ Set.range p.wire, x i = false) :
    x = p.store f := by
  funext i
  by_cases hi : i ∈ Set.range p.wire
  · obtain ⟨j, rfl⟩ := hi
    rw [hr, read_store]
  · rw [hz _ hi, padding _ _ _ hi]

theorem store_injective : Function.Injective p.store := by
  intro x y he
  funext i
  simpa using congrFun he (p.wire i)

end Payload
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Ordered bundles on a common host

Patterns use short neighbor indices at every occurrence. The decoding
table is independent of the global host names and the block number.
Port order inside each span is the same at its two ends. Width zero
permits unused seats, including a scalar with no arguments.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

structure Pattern (F : Type) (d k e : ℕ) where
  width : B k → B e → ℕ
  direction : B k → B e → Bool
  peer : B k → B e → Option (B d × B k × B e)
  value : (j : B k) → (∀ s : B e, Fin (width j s) → Bool) → F

structure Scheme (F : Type) where
  m : ℕ
  d : ℕ
  h : ℕ
  k : ℕ
  e : ℕ
  ℓ : ℕ
  decode : B ℓ → Pattern F d k e

namespace Scheme
variable {F : Type} (S : Scheme F)

abbrev format := Fmt.rows S.m S.d S.h (.addr S.ℓ)
abbrev Vtx := B S.m × B S.h × B S.k
abbrev Span := S.Vtx × B S.e

variable (r : S.format.obj)

def pattern (v : S.Vtx) := S.decode ((r v.1).2 v.2.1)

def width (p : S.Span) := (S.pattern r p.1).width p.1.2.2 p.2

def direction (p : S.Span) := (S.pattern r p.1).direction p.1.2.2 p.2

def peer (p : S.Span) : Option S.Span :=
  ((S.pattern r p.1).peer p.1.2.2 p.2).map
    fun t => (((r p.1.1).1 t.1, p.1.2.1, t.2.1), t.2.2)

def Proper : Prop := ∀ p q, S.peer r p = some q →
  S.peer r q = some p ∧ S.width r p = S.width r q ∧ S.direction r p ≠ S.direction r q

abbrev Pin := Σ p : S.Span, Fin (S.width r p)
abbrev LocalPin (v : S.Vtx) := Σ s : B S.e, Fin (S.width r (v, s))
abbrev exposed := {p : S.Pin r // S.peer r p.1 = none}

def port (v : S.Vtx) (p : S.LocalPin r v) : S.Pin r := ⟨(v, p.1), p.2⟩

def table (v : S.Vtx) (x : S.LocalPin r v → Bool) :=
  (S.pattern r v).value v.2.2 fun s i => x ⟨s, i⟩

def Joins (p q : S.Pin r) : Prop := S.peer r p.1 = some q.1 ∧ p.2.val = q.2.val

def Agrees (x : S.exposed r → Bool) (y : S.Pin r → Bool) : Prop :=
  (∀ p, y p.val = x p) ∧ ∀ p q, S.Joins r p q → y p = y q

def eval [Field F] (x : S.exposed r → Bool) :=
  ∑ y : S.Pin r → Bool, if S.Agrees r x y then ∏ v, S.table r v (y ∘ S.port r v) else 0

end Scheme
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Station tables in span order

Each side lists the spans in increasing order and the bits of each
span in increasing offset. Only the pattern and local station label
are needed to construct the table.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Pattern
open Coloring Transcript

variable {F : Type} {d k e : ℕ} (P : Pattern F d k e) (j : B k)

abbrev Pin := Σ s, Fin (P.width j s)
private abbrev Side (b : Bool) := {s // P.direction j s = b}
private abbrev lengths (b : Bool) (s : P.Side j b) := P.width j s.1
private abbrev Group (b : Bool) := Σ s, Fin (P.lengths j b s)

def wire (b : Bool) := word (Fintype.card (Lex (P.Group j b)))

private def serial (b : Bool) : slots (P.wire j b) ≃ P.Group j b :=
  ((positions (P.wire j b)).trans (finCongr (wd_word _))).trans
    ((Fintype.orderIsoFinOfCardEq (Lex (P.Group j b)) rfl).toEquiv.trans ofLex)

private def flat (b : Bool) (q : P.Group j b) : P.Pin j := ⟨q.1.1, q.2⟩

private theorem flat_inj (b : Bool) : Function.Injective (P.flat j b) := by
  rintro ⟨⟨s, h⟩, i⟩ ⟨⟨t, h'⟩, l⟩ he
  have eq : s = t := congrArg Sigma.fst he
  subst t
  have : i = l := Fin.ext (congrArg (fun x => x.2.val) he)
  rw [this]

private def sides : P.Group j false ⊕ P.Group j true ≃ P.Pin j :=
  Equiv.ofBijective (Sum.elim (P.flat j false) (P.flat j true)) (by
    constructor
    · rintro (i|i) (l|l) h
      · exact congrArg Sum.inl (P.flat_inj j _ h)
      · have he : i.1.1 = l.1.1 := congrArg Sigma.fst h
        have := i.1.2
        rw [he, l.1.2] at this
        cases this
      · have he : i.1.1 = l.1.1 := congrArg Sigma.fst h
        have := i.1.2
        rw [he, l.1.2] at this
        cases this
      · exact congrArg Sum.inr (P.flat_inj j _ h)
    · rintro ⟨s, i⟩
      cases h : P.direction j s
      · exact ⟨.inl ⟨⟨s, h⟩, i⟩, rfl⟩
      · exact ⟨.inr ⟨⟨s, h⟩, i⟩, rfl⟩)

def orderedPin : slots (P.wire j false) ⊕ slots (P.wire j true) ≃ P.Pin j :=
  ((P.serial j false).sumCongr (P.serial j true)).trans (P.sides j)

theorem pin_side (i : slots (P.wire j false) ⊕ slots (P.wire j true)) :
    P.direction j (P.orderedPin j i).1 = i.isRight := by
  cases i with
  | inl i => exact (P.serial j false i).1.2
  | inr i => exact (P.serial j true i).1.2

def orderedTable : Table F :=
  ⟨P.wire j false, P.wire j true, fun x y => P.value j fun s i =>
    Sum.elim (bits (P.wire j false) x) (bits (P.wire j true) y) ((P.orderedPin j).symm ⟨s, i⟩)⟩

theorem sample_ordered (t : P.Pin j → Bool) :
    sample (P.orderedTable j) (t ∘ P.orderedPin j) = P.value j (fun s i => t ⟨s, i⟩) := by
  unfold sample orderedTable
  apply congrArg (P.value j)
  funext s i
  simp only [Equiv.apply_symm_apply]
  have h (x : slots (P.wire j false) ⊕ slots (P.wire j true)) :
      Sum.elim (t ∘ P.orderedPin j ∘ Sum.inl) (t ∘ P.orderedPin j ∘ Sum.inr) x =
        t (P.orderedPin j x) := by cases x <;> rfl
  rw [← Function.comp_assoc, ← Function.comp_assoc] at h
  rw [h, Equiv.apply_symm_apply]

def start (s : B e) :=
  Processor.start (P.lengths j (P.direction j s)) ⟨s, rfl⟩

private theorem start_eq (b : Bool) (s : P.Side j b) :
    P.start j s.1 = Processor.start (P.lengths j b) s := by
  obtain ⟨s, h⟩ := s
  subst b
  rfl

theorem start_left {s t : B e} (h : P.direction j s = P.direction j t) (ht : s < t) :
    P.start j s + P.width j s ≤ P.start j t := by
  rw [P.start_eq j _ ⟨s, h⟩]
  exact Processor.start_left (P.lengths j _) ⟨s, h⟩ ⟨t, rfl⟩ ht

private theorem serial_position (b : Bool) (i : slots (P.wire j b)) :
    (positions (P.wire j b) i).val = P.start j (P.serial j b i).1.1 + (P.serial j b i).2.val := by
  rw [P.start_eq]
  let g := Fintype.orderIsoFinOfCardEq (Lex (P.Group j b)) rfl
  let x := (finCongr (wd_word (Fintype.card (Lex (P.Group j b))))) (positions (P.wire j b) i)
  calc
    _ = (g.symm (g x)).val := by rw [OrderIso.symm_apply_apply]; rfl
    _ = _ := Processor.serial_rank (P.lengths j b) rfl (g x)

theorem position_left (i : slots (P.wire j false)) :
    (positions (P.wire j false) i).val = P.start j (P.orderedPin j (.inl i)).1 +
      (P.orderedPin j (.inl i)).2.val := P.serial_position j false i

theorem position_right (i : slots (P.wire j true)) :
    (positions (P.wire j true) i).val = P.start j (P.orderedPin j (.inr i)).1 +
      (P.orderedPin j (.inr i)).2.val := P.serial_position j true i

end OAI.LinearAlgebra.MatrixExponent.Assembly.Pattern
end

/-!
# Computing the matching at one host position

The neighbor list is common to all blocks of the position. Only a
short index into that list and the neighbor's colony key enter a row.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring

abbrev Input (d h e k ℓ : ℕ) :=
  Format.pair (.vec h .bit) (.pair (.vec h (Fmt.occ d h e k ℓ)) (.vec h (.vec d (.addr ℓ))))

abbrev Labels (h ℓ d : ℕ) := Format.pair (.addr h) (.pair (.addr ℓ) (.addr d))

def rowIndex (h e : ℕ) : B (h + e) ≃ B h × B e :=
  (finCongr (pow_add 2 h e)).trans finProdFinEquiv.symm

variable {d h e k ℓ : ℕ}

def rows (x : (Input d h e k ℓ).obj) : Rows (h + e) (Labels h ℓ d).width :=
  let block i := (rowIndex h e i).1
  let stub i := (x.2.1 (block i)).2 (rowIndex h e i).2
  let code := (Labels h ℓ d).serial
  (fun i => (stub i).1, fun i => x.1 (block i),
   fun i => code (0, (x.2.1 (block i)).1, 0), fun i => code (block i, 0, 0),
   fun i => code (0, x.2.2 (block i) (stub i).2.1, (stub i).2.1))

theorem width_labels (h ℓ d : ℕ) : (Labels h ℓ d).width = h + (ℓ + d) := by simp [Labels]

variable (F : Type) [Field F]

theorem read_one (U : Format) {t : ℕ} (hh : d ≤ t) (hl : U.width ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F 0 t (.pair (.addr d) (.vec d U)) U (fun x => x.2 x.1) 12 := by
  let A := Format.pair (.addr d) (.vec d U)
  have ha : A.width ≤ 2 ^ d * (100 + t) ^ 2 := by
    simp only [A, Format.width_pair, Format.width_vec, Format.width_addr]
    calc
      _ ≤ 2 ^ d * d + 2 ^ d * U.width := Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (by positivity)) _
      _ ≤ _ := by rw [← mul_add]; gcongr; ring_nf; omega
  have hi : (Perm d).width ≤ 2 ^ d * (100 + t) ^ 2 :=
    (column_width _ hh).trans (by gcongr; omega)
  have hv : Cheap F d t A (Perm d) (fun x _ => x.1) 3 :=
    Cheap.project F ha hi (fun j => Sum.inl j.2) (fun _ _ => rfl)
  have hs := ((Cheap.id F ha).snd.pair hv).comp (Cheap.lookup F d t U hh hl)
  have hk : U.width ≤ 2 ^ d * (100 + t) ^ 1 := by
    rw [pow_one]
    exact (Nat.le_mul_of_pos_left _ (by positivity)).trans (Nat.mul_le_mul_left _ (by omega))
  have hm : (Format.vec d U).width ≤ 2 ^ d * (100 + t) ^ 1 := by
    rw [Format.width_vec, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have out : Cheap F d t (.vec d U) U (fun x => x 0) 2 :=
    Cheap.project F hm hk (fun j => (0, j)) (fun _ _ => rfl)
  obtain ⟨m, hm, hc⟩ := (hs.comp out).mono (d := 11) (by decide)
  refine ⟨m, hm, hc.trans ?_⟩
  rw [pow_zero, one_mul, show 12 = 11 + 1 from rfl, pow_succ' (100 + t) 11]
  exact Nat.mul_le_mul_right _ (by omega)

theorem input_bound (t : ℕ) (h₁ : d ≤ t) (h₂ : k ≤ t) (h₃ : ℓ ≤ t) (hd : 2 ^ d ≤ t) :
    (Input d h e k ℓ).width ≤ 2 ^ (h + e) * (100 + t) ^ 2 := by
  unfold Input
  rw [Format.width_pair, Format.width_pair, Format.width_vec, Format.width_bit, Format.width_vec,
    Fmt.width_occ, Format.width_vec, Format.width_vec, Format.width_addr, ← mul_add, ← mul_add,
    pow_add, mul_assoc]
  apply Nat.mul_le_mul_left
  have he : 0 < 2 ^ e := by positivity
  calc
    _ ≤ 2 ^ e * (1 + (ℓ + (1 + (d + k)) + 2 ^ d * ℓ)) := by
      simp only [mul_add]
      have := Nat.le_mul_of_pos_left ℓ he
      have := Nat.le_mul_of_pos_left (2 ^ d * ℓ) he
      omega
    _ ≤ _ := by gcongr; nlinarith only [h₁, h₂, h₃, Nat.mul_le_mul hd h₃]

theorem cheap_rows (d h e k ℓ t : ℕ) (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t)
    (hw : k ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F (h + e) t (Input d h e k ℓ) (RowFmt (h + e) (Labels h ℓ d).width) rows 30 := by
  let A := Input d h e k ℓ
  let b i := (rowIndex h e i).1
  let j i := (rowIndex h e i).2
  let stub (x : A.obj) i := (x.2.1 (b i)).2 (j i)
  have wt := ht
  rw [Rows.overhead, width_labels] at wt
  have ha := input_bound (h := h) (e := e) t (show d ≤ t by omega) hw (show ℓ ≤ t by omega) hd
  have hc (i : ℕ) (hi : i ≤ t) : (Column (h + e) i).width ≤ 2 ^ (h + e) * (100 + t) ^ 2 :=
    (column_width _ hi).trans (by gcongr; omega)
  have hb : (Format.vec (h + e) .bit).width ≤ 2 ^ (h + e) * (100 + t) ^ 2 := by
    rw [Format.width_vec, Format.width_bit]
    exact Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
  have hn : (Format.vec (h + e) (.vec d (.addr ℓ))).width ≤ 2 ^ (h + e) * (100 + t) ^ 2 := by
    rw [Format.width_vec, Format.width_vec, Format.width_addr, pow_two]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have active : Cheap F (h + e) t A (.vec (h + e) .bit) (fun x i => (stub x i).1) 3 :=
    Cheap.project F ha hb (fun z => .inr (.inl (b z.1, .inr (j z.1, .inl z.2)))) (fun _ _ => rfl)
  have thick : Cheap F (h + e) t A (.vec (h + e) .bit) (fun x i => x.1 (b i)) 3 :=
    Cheap.project F ha hb (fun z => .inl (b z.1, z.2)) (fun _ _ => rfl)
  have label : Cheap F (h + e) t A (Column (h + e) ℓ) (fun x i => (x.2.1 (b i)).1) 3 :=
    Cheap.project F ha (hc ℓ (by omega)) (fun z => .inr (.inl (b z.1, .inl z.2))) (fun _ _ => rfl)
  have near : Cheap F (h + e) t A (Column (h + e) d) (fun x i => (stub x i).2.1) 3 :=
    Cheap.project F ha (hc d (by omega))
      (fun z => .inr (.inl (b z.1, .inr (j z.1, .inr (.inl z.2))))) (fun _ _ => rfl)
  have remote : Cheap F (h + e) t A (.vec (h + e) (.vec d (.addr ℓ))) (fun x i => x.2.2 (b i)) 3 :=
    Cheap.project F ha hn (fun z => .inr (.inr (b z.1, z.2))) (fun _ _ => rfl)
  have addr := (near.pair remote).zip.comp
    (Cheap.map (fun _ => _) (fun _ => read_one (d := d) F (.addr ℓ) (by omega) (by simp; omega) hd))
  have zero (i : ℕ) (hi : i ≤ t) : Cheap F (h + e) t A (Column (h + e) i) (fun _ _ => 0) 3 :=
    Cheap.const F ha (hc i hi) (fun _ => 0)
  have keys := cheap_keys (Labels h ℓ d) F (h + e) (show (Labels h ℓ d).width ≤ t by rw [width_labels]; omega)
  have block := Cheap.const F ha (hc h (by omega)) b
  have src := ((zero h (by omega)).pair (label.pair (zero d (by omega))).zip).zip.comp keys
  have item := (block.pair ((zero ℓ (by omega)).pair (zero d (by omega))).zip).zip.comp keys
  have dest := ((zero h (by omega)).pair (addr.pair near).zip).zip.comp keys
  exact (active.pair (thick.pair (src.pair (item.pair dest)))).mono (by decide)

theorem cheap_match (d h e k ℓ t : ℕ) (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t)
    (hw : k ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F (h + e) t (Input d h e k ℓ) (.pair (.vec (h + e) .bit) (Perm (h + e)))
      (fun x => (rows x).control) 151 :=
  ((cheap_rows F d h e k ℓ t ht hw hd).comp ((Rows.cheap_control F _ _).widen ht)).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

/-! # Packing the exterior bits of a scheme by host and occurrence -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme

open Coloring
open scoped Classical
variable {F : Type} (S : Scheme F) (r : S.format.obj)

def owner (i : S.exposed r) : B S.m := i.val.1.1.1

abbrev fiber (i : B S.m) := {a : S.exposed r // S.owner r a = i}

def load (i : B S.m) := Fintype.card (S.fiber r i)

def Fits (V k : ℕ) : Prop :=
  (∑ i, max 1 (S.load r i)) ≤ V ∧ ∀ i, S.load r i ≤ 2 ^ k

def spanRows := S.h + S.k + S.e

def hostSpan : B S.m × B S.spanRows ≃ S.Span :=
  ((Equiv.refl _).prodCongr
    ((Match.rowIndex (S.h + S.k) S.e).trans
      ((Match.rowIndex S.h S.k).prodCongr (.refl _)))).trans (Equiv.prodAssoc _ _ _).symm

def spanIndex (p : S.Span) := (S.hostSpan.symm p).2

@[simp] theorem hostSpan_owner (i : B S.m) (t : B S.spanRows) : (S.hostSpan (i, t)).1.1 = i := rfl

@[simp] theorem spanIndex_hostSpan (i : B S.m) (t : B S.spanRows) :
    S.spanIndex (S.hostSpan (i, t)) = t := by rw [spanIndex, Equiv.symm_apply_apply]

@[simp] theorem hostSpan_spanIndex (p : S.Span) : S.hostSpan (p.1.1, S.spanIndex p) = p :=
  S.hostSpan.apply_symm_apply p

def extent (i : B S.m) (t : B S.spanRows) :=
  let p := S.hostSpan (i, t)
  if S.peer r p = none then S.width r p else 0

private def localBits (i : B S.m) : S.fiber r i ≃ Σ t, Fin (S.extent r i t) := by
  have he (a : S.fiber r i) : S.hostSpan (i, S.spanIndex a.val.val.1) = a.val.val.1 :=
    (congrArg (fun z => S.hostSpan (z, S.spanIndex a.val.val.1)) a.2.symm).trans
      (S.hostSpan_spanIndex _)
  let f : S.fiber r i → Σ t, Fin (S.extent r i t) := fun a =>
    ⟨S.spanIndex a.val.val.1, a.val.val.2.val, by
      unfold extent
      rw [he]
      simp only [a.val.property, ite_true]
      exact a.val.val.2.isLt⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b heq
    have h₁ : S.spanIndex a.val.val.1 = S.spanIndex b.val.val.1 := congrArg Sigma.fst heq
    have h₂ : a.val.val.2.val = b.val.val.2.val := congrArg (fun i => i.2.val) heq
    have h₃ : a.val.val.1 = b.val.val.1 := by rw [← he a, ← he b, h₁]
    exact Subtype.ext (Subtype.ext (Sigma.ext h₃ ((Fin.heq_ext_iff (congrArg _ h₃)).mpr h₂)))
  · rintro ⟨t, b⟩
    let u := S.hostSpan (i, t)
    have hb : b.val < if S.peer r u = none then S.width r u else 0 := b.isLt
    split at hb
    swap
    · omega
    rename_i hu
    let p : S.fiber r i := ⟨⟨⟨u, ⟨b.val, hb⟩⟩, hu⟩, rfl⟩
    have hp : (f p).1 = t := S.spanIndex_hostSpan _ _
    exact ⟨p, Sigma.ext hp ((Fin.heq_ext_iff (congrArg _ hp)).mpr rfl)⟩

theorem load_eq (i : B S.m) : S.load r i = ∑ j, S.extent r i j := by
  unfold load
  rw [Fintype.card_congr (S.localBits r i), Fintype.card_sigma]
  simp

/-- Order within one host is lexicographic by block, station, span
and offset within the span. -/
def serial (i : B S.m) : S.fiber r i ≃ Fin (S.load r i) :=
  (S.localBits r i).trans (finSigmaFinEquiv.trans (finCongr (S.load_eq r i).symm))

variable {V k : ℕ} (h : S.Fits r V k)

def payload : Payload S.m V k := ⟨S.load r, h.1, h.2⟩

def index : S.exposed r ≃ (S.payload r h).Bit :=
  (Equiv.sigmaFiberEquiv (S.owner r)).symm.trans (Equiv.sigmaCongrRight (S.serial r))

def start (i : B S.m) (t : B S.spanRows) := ∑ j with j < t, S.extent r i j

private theorem strict_sum {n : ℕ} (f : Fin n → ℕ) (b : Fin n) :
    (∑ i : Fin b.val, f (i.castLE b.isLt.le)) = ∑ i with i < b, f i := by
  let e : Fin b.val ≃ {i // i < b} :=
    { toFun := fun i => ⟨i.castLE b.isLt.le, i.isLt⟩
      invFun := fun i => ⟨i.val.val, i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Finset.sum_subtype (p := (· < b)) _ Finset.mem_filter_univ]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem index_val (a : S.exposed r) :
    (S.index r h a).2.val = S.start r (S.owner r a) (S.spanIndex a.val.1) + a.val.2.val := by
  let i := S.owner r a
  let q := S.localBits r i ⟨a, rfl⟩
  change (finSigmaFinEquiv q).val = _
  rw [finSigmaFinEquiv_apply, strict_sum]
  rfl

def wire : S.exposed r ↪ Fmt.Port S.m V k :=
  (S.index r h).toEmbedding.trans (S.payload r h).wire

def store (x : S.exposed r → Bool) : (Fmt.payload S.m V k).obj :=
  (S.payload r h).store (x ∘ (S.index r h).symm)

@[simp] theorem read_store (x : S.exposed r → Bool) (i : S.exposed r) :
    S.store r h x (S.wire r h i) = x i := by
  simp [store, wire]

theorem store_unique (x : S.exposed r → Bool) (y : (Fmt.payload S.m V k).obj)
    (hx : ∀ i, y (S.wire r h i) = x i) (hy : ∀ i ∉ Set.range (S.wire r h), y i = false) :
    y = S.store r h x := by
  apply Payload.store_unique
  · intro i
    simpa [wire] using hx ((S.index r h).symm i)
  · intro i hi
    exact hy i fun ⟨j, hj⟩ => hi ⟨S.index r h j, hj⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-!
# Matching reciprocal neighbor names

Sort by the unordered pair of names and return the other row with
that key. A row naming its own host stays fixed, so self-contacts
may have arbitrary multiplicity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring

private abbrev Names (m : ℕ) := Format.pair (.addr m) (.addr m)

private def sorted {m : ℕ} (z : B m × B m) := if z.1 < z.2 then z else z.swap

private theorem sorted_swap {m : ℕ} (a b : B m) : sorted (a, b) = sorted (b, a) := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [sorted, h, not_lt.mpr h.le]
  · rfl
  · simp [sorted, h, not_lt.mpr h.le]

private theorem cheap_sorted (F : Type) [Field F] {m t : ℕ} (hm : m ≤ t) :
    Cheap F 0 t (Names m) (Names m) sorted 12 := by
  have lt : Cheap F 0 t (Names m) .bit (fun z => decide (z.1 < z.2)) 3 := by
    refine ⟨_, numeric_lt F m, ?_⟩
    simp only [Format.width_pair, Format.width_addr]
    rw [Format.width_bit]
    ring_nf
    omega
  have hw : (Names m).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp [Names]; ring_nf; omega
  have a := Cheap.id F hw
  have l := (a.pair lt).comp ((cheap_select F m).widen hm)
  have r := ((a.snd.pair a.fst).pair lt).comp ((cheap_select F m).widen hm)
  convert (l.pair r).mono (d := 12) (by decide) using 1
  funext z
  obtain ⟨x, y⟩ := z
  by_cases he : x < y <;> simp [sorted, he]

variable {j m : ℕ} (host p : B j → B m)

private def keys := (Names m).keys (fun i => sorted (host i, p i))

private def neighbor (i : B j) :=
  if host i = p i then i else other (keys host p) i

private theorem reverse_eq
    (h : ∀ i, p i ≠ host i → ∃! l, p i = host l ∧ p l = host i)
    (i l : B j) (hi : p i ≠ host i) (hl : p i = host l ∧ p l = host i) :
    neighbor host p i = l := by
  have hn : l ≠ i := fun he => hi (he ▸ hl.1)
  have he : keys host p l = keys host p i := by
    unfold keys Format.keys
    simp only [Function.comp_apply, ← hl.1, hl.2, sorted_swap]
  rw [neighbor, ite_eq_right hi.symm]
  let t := other (keys host p) i
  obtain ⟨ht, hne⟩ := other_spec (keys host p) i
  have hti : t ≠ i := hne l he hn
  have hh : sorted (host t, p t) = sorted (host i, p i) := (Names m).serial.injective ht
  have hk : (host t = host i ∧ p t = p i) ∨ (p i = host t ∧ p t = host i) := by
    unfold sorted at hh
    split_ifs at hh <;> simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hh <;> tauto
  rcases hk with hk | hk
  · have hn' : p l ≠ host l := by rw [hl.2, ← hl.1]; exact hi.symm
    exact (hti ((h l hn').unique ⟨hl.2.trans hk.1.symm, hk.2.trans hl.1⟩ ⟨hl.2, hl.1⟩)).elim
  · exact (h i hi).unique hk hl

theorem contacts (F : Type) [Field F] (j m : ℕ) (host : B j → B m) :
    ∃ f : (B j → B m) → B j → B j,
      Cheap F j (j + 3 * m + 1) (.vec j (.addr m)) (Perm j) f 200 ∧
      ∀ p, (∀ i, p i ≠ host i → ∃! l, p i = host l ∧ p l = host i) →
        Function.Bijective (f p) ∧ ∀ i, host (f p i) = p i := by
  refine ⟨neighbor host, ?_, fun p h => ?_⟩
  · let t := j + 3 * m + 1
    have hm : m ≤ t := by omega
    have hj : j ≤ t := by omega
    have hw : j + (Names m).width ≤ t := by simp [Names]; omega
    have a := column_width j hm
    have pair := ((Cheap.const F a a host).pair (Cheap.id F a)).zip
    have sort := pair.comp (Cheap.map _ (fun _ => cheap_sorted F hm))
    have key := sort.comp (cheap_keys (Names m) F j (k := t) (by omega))
    have peer := key.comp ((cheap_other F j _).widen hw)
    have eq := pair.comp (Cheap.map _ (fun _ => cheap_eq F hm))
    have self := Cheap.const F a (column_width j hj) id
    have pick := (((self.pair peer).zip.pair eq).zip.comp (Cheap.map _ (fun _ => (cheap_select F j).widen hj)))
    convert pick.mono (d := 200) (by decide) using 1
    funext p i
    simp [neighbor, keys]
  · have both (i : B j) : neighbor host p (neighbor host p i) = i ∧
        host (neighbor host p i) = p i := by
      by_cases he : p i = host i
      · have hi : neighbor host p i = i := ite_eq_left he.symm
        rw [hi, hi]
        exact ⟨rfl, he.symm⟩
      · obtain ⟨l, hl, _⟩ := h i he
        have hn : p l ≠ host l := by rw [hl.2, ← hl.1]; exact Ne.symm he
        rw [reverse_eq host p h i l he hl]
        exact ⟨reverse_eq host p h l i hn ⟨hl.2, hl.1⟩, hl.1.symm⟩
    exact ⟨Function.Involutive.bijective (fun i => (both i).1), fun i => (both i).2⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Exchanging full block records across a variable host

Long names are routed only once per incident neighbor, independently
of the number of blocks carried by a record. Empty neighbor entries
name their own host. They need not be distinct.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} [Field F] {u v n m d : ℕ} {L : Set (Table F)}
  {I : Type*} (A : Format)

abbrev Fmt.bank (m d : ℕ) (A : Format) := Format.vec m (.pair (.vec d (.addr m)) A)

namespace Fmt

def Reciprocal (x : (bank m d A).obj) := ∀ i j, (x i).1 j ≠ i →
  ∃! l, (x ((x i).1 j)).1 l = i

def gather (x : (bank m d A).obj) (i : B m) (j : B d) := (x ((x i).1 j)).2

end Fmt

private abbrev Col (m d : ℕ) := Format.vec (m + d) (.addr m)
private abbrev Vec (m d : ℕ) (A : Format) := Format.vec (m + d) A

private def targets (x : (Fmt.bank m d A).obj) (j : B (m + d)) :=
  (x (Match.rowIndex m d j).1).1 (Match.rowIndex m d j).2

private def hosts (m d : ℕ) (j : B (m + d)) := (Match.rowIndex m d j).1

private theorem reciprocal_edges (x : (Fmt.bank m d A).obj) (h : Fmt.Reciprocal A x)
    (i : B (m + d)) (hi : targets A x i ≠ hosts m d i) :
    ∃! l, targets A x i = hosts m d l ∧ targets A x l = hosts m d i := by
  let e := Match.rowIndex m d
  obtain ⟨t, ht, hu⟩ := h (e i).1 (e i).2 hi
  refine ⟨e.symm (targets A x i, t), ?_, fun j hj => ?_⟩
  · simpa only [targets, hosts, e, Equiv.apply_symm_apply, true_and] using ht
  · apply e.injective
    rw [e.apply_symm_apply]
    refine Prod.ext hj.1.symm (hu _ ?_)
    change (x (targets A x i)).1 (e j).2 = (e i).1
    rw [hj.1]
    exact hj.2

private theorem packets (hu : 3 ≤ u) (f : (Col m d).obj → (Perm (m + d)).obj)
    (hf : Circuit F (Col m d) (Perm (m + d)) f n) :
    Map F u L (Fmt.bank m d A) (exchangeIn A (m + d))
      (fun x => (f (targets A x), fun j => (x (hosts m d j)).2))
      (4 * (7 * (Fmt.bank m d A).width + 2 * ((Col m d).width + (Vec m d A).width) + n)) := by
  let X := Fmt.bank m d A
  have select : Circuit F X (Col m d) (targets A) (X.width + 2 * (Col m d).width) :=
    Circuit.project (fun p => let q := Match.rowIndex m d p.1; (q.1, .inl (q.2, p.2))) (fun _ _ => rfl)
  have data : Circuit F X (Vec m d A) (fun x j => (x (hosts m d j)).2)
      (X.width + 2 * (Vec m d A).width) :=
    Circuit.project (fun p => (hosts m d p.1, .inr p.2)) (fun _ _ => rfl)
  exact (Map.circuit hu ((select.comp hf).pair data)).mono (by unfold X; omega)

def gatherCost (m d v n : ℕ) :=
  4 * n + 4 * (2 ^ (m + d) * (100 + (m + d + 3 * m + 1)) ^ 200) + 1100 * 2 ^ (m + d) * (m + d + v + 1)

theorem gather_neighbors (hu : 3 ≤ u) (ht : Access F u L (m + d) v n) (ha : A.width ≤ v)
    (X : I → (Fmt.bank m d A).obj) (hx : ∀ i, Fmt.Reciprocal A (X i)) :
    Computes F u L (Fmt.bank m d A) (.vec m (.vec d A)) X (fun i => Fmt.gather A (X i))
      (fun _ => 1) (gatherCost m d v n) := by
  obtain ⟨f, ⟨c, hf, hc⟩, he⟩ := contacts F (m + d) m (hosts m d)
  let out := Format.vec m (.vec d A)
  have post : Map F u L (exchangeOut A (m + d)) out
      (fun x i j => x ((Match.rowIndex m d).symm (i, j)))
      (4 * ((Vec m d A).width + 2 * out.width)) :=
    Map.circuit hu (Circuit.project (fun z => ((Match.rowIndex m d).symm (z.1, z.2.1), z.2.2))
      fun _ _ => rfl)
  have pre := packets (L := L) A hu f hf
  have k := pre.then_kernel (ht A ha)
  let y i j := (X i (targets A (X i) j)).2
  have relay : Computes F u L (Fmt.bank m d A) (exchangeOut A (m + d))
      X y (fun _ => 1) _ := ⟨_, k, fun i z => by
        obtain ⟨hh, hh'⟩ := he _ (reciprocal_edges A (X i) (hx i))
        have hy : (fun j => (X i (hosts m d j)).2) ∘ f (targets A (X i)) = y i :=
          funext fun j => congrArg (fun l => (X i l).2) (hh' j)
        simp only [exchange, hh, true_and, hy, eq_comm]⟩
  have h := relay.comp (Computes.of_map (x := y) post (y := fun i => Fmt.gather A (X i)) (by
    intro i; funext j l
    simp only [y, targets, Fmt.gather, Equiv.apply_symm_apply]))
  simp only [mul_one] at h
  refine h.mono ?_
  have hc' : c ≤ 2 ^ (m + d) * (100 + (m + d + 3 * m + 1)) ^ 200 :=
    (Nat.le_add_left _ _).trans hc
  have hv : 2 ^ m * A.width ≤ 2 ^ (m + d) * v :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)) ha
  have ha' := Nat.mul_le_mul_left (2 ^ (m + d)) ha
  simp only [out, Fmt.bank, Col, Vec, Format.width_vec, Format.width_pair, Format.width_addr,
    gatherCost, mul_add, ← mul_assoc, ← pow_add]
  simp only [mul_assoc]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Closed neighborhoods of a reciprocal host graph

A walk may stay put at any step. A fixed dictionary enumerates all
walk instructions. At each center keep the first occurrence of each
destination and replace every repeated occurrence by the center.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
open Coloring

abbrev Rows (m d : ℕ) := Format.vec m (.vec d (.addr m))

variable {m d : ℕ} (g : B m → B d → B m)

def Reach : ℕ → B m → B m → Prop
  | 0, x, y => x = y
  | r + 1, x, y => ∃ z, (z = x ∨ ∃ i, g x i = z) ∧ Reach r z y

theorem Reach.refl (r : ℕ) (x : B m) : Reach g r x x := by
  induction r with
  | zero => rfl
  | succ r ih => exact ⟨x, Or.inl rfl, ih⟩

variable {g} {r : ℕ} {x y z : B m}

theorem Reach.tail (h : Reach g r x y) (he : z = y ∨ ∃ i, g y i = z) :
    Reach g (r + 1) x z := by
  induction r generalizing x with
  | zero =>
    change x = y at h
    subst x
    exact ⟨z, he, rfl⟩
  | succ r ih =>
    obtain ⟨a, ha, h⟩ := h
    exact ⟨a, ha, ih h⟩

theorem Reach.symm (h : Reach g r x y) (hg : ∀ i j, g i j ≠ i → ∃ l, g (g i j) l = i) :
    Reach g r y x := by
  induction r generalizing x with
  | zero => exact Eq.symm h
  | succ r ih =>
    obtain ⟨a, ha, h⟩ := h
    apply (ih h).tail
    by_cases he : a = x
    · exact .inl he.symm
    · obtain ⟨i, rfl⟩ := ha.resolve_left he
      exact .inr (hg _ _ he)

def Walk (d : ℕ) : ℕ → Type
  | 0 => Unit
  | r + 1 => Option (B d) × Walk d r

instance walkFinite (d : ℕ) : (r : ℕ) → Fintype (Walk d r)
  | 0 => inferInstanceAs (Fintype Unit)
  | r + 1 =>
    let _ := walkFinite d r
    inferInstanceAs (Fintype (Option (B d) × Walk d r))

private def stay (d : ℕ) : (r : ℕ) → Walk d r
  | 0 => ()
  | r + 1 => (none, stay d r)

instance (d r : ℕ) : Nonempty (Walk d r) := ⟨stay d r⟩

private theorem walk_card (d r : ℕ) : Fintype.card (Walk d r) ≤ 2 ^ ((d + 1) * r) := by
  induction r with
  | zero => exact (Fintype.card_unit).le
  | succ r ih =>
    change Fintype.card (Option (B d) × Walk d r) ≤ _
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.mul_succ, pow_add,
      Nat.mul_comm (2 ^ ((d + 1) * r))]
    apply Nat.mul_le_mul _ ih
    rw [pow_succ]
    have := Nat.two_pow_pos d
    omega

private def code (d r : ℕ) : Walk d r ↪ B ((d + 1) * r) :=
  let e := (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (walk_card d r))
  e.trans (Equiv.swap (e (stay d r)) 0).toEmbedding

def path (d r : ℕ) := Function.invFun (code d r)

def run (g : B m → B d → B m) : (r : ℕ) → Walk d r → B m → B m
  | 0, _, x => x
  | r + 1, w, x => run g r w.2 (w.1.elim x (g x))

theorem path_surjective (d r : ℕ) : Function.Surjective (path d r) :=
  fun w => ⟨code d r w, Function.leftInverse_invFun (code d r).injective w⟩

def walks (r : ℕ) (g : B m → B d → B m) (x : B m) (i : B ((d + 1) * r)) :=
  run g r (path d r i) x

private theorem reach_iff : Reach g r x y ↔ ∃ w, run g r w x = y := by
  induction r generalizing x with
  | zero => exact ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩
  | succ r ih =>
    constructor
    · rintro ⟨a, ha, h⟩
      obtain ⟨w, hw⟩ := ih.mp h
      rcases ha with rfl | ⟨i, rfl⟩
      · exact ⟨(none, w), hw⟩
      · exact ⟨(some i, w), hw⟩
    · rintro ⟨⟨_|i, w⟩, hw⟩
      · exact ⟨x, Or.inl rfl, ih.mpr ⟨w, hw⟩⟩
      · exact ⟨g x i, Or.inr ⟨i, rfl⟩, ih.mpr ⟨w, hw⟩⟩

def dedup {q : ℕ} (x : B m) (a : B q → B m) (i : B q) :=
  if groupFirst a i = i then a i else x

def expand (r : ℕ) (g : B m → B d → B m) (x : B m) : B ((d + 1) * r) → B m :=
  dedup x (fun i => run g r (path d r i) x)

theorem origin : expand r g x 0 = x := by
  have hc : code d r (stay d r) = 0 := Equiv.swap_apply_left _ _
  have he : path d r 0 = stay d r := by
    rw [← hc]
    exact Function.leftInverse_invFun (code d r).injective _
  have hx (n : ℕ) : run g n (stay d n) x = x := by
    induction n with
    | zero => rfl
    | succ _ ih => exact ih
  simp only [expand, dedup, he, hx, ite_self]

theorem mem : (∃ i, expand r g x i = y) ↔ Reach g r x y := by
  let a i := run g r (path d r i) x
  constructor
  · rintro ⟨i, rfl⟩
    unfold expand dedup
    split
    · exact reach_iff.mpr ⟨_, rfl⟩
    · exact Reach.refl _ _ _
  · intro h
    obtain ⟨w, hw⟩ := reach_iff.mp h
    let i := code d r w
    have hi : a i = y := by
      unfold a path i
      rw [Function.leftInverse_invFun (code d r).injective]
      exact hw
    let j := groupFirst a i
    have hj : a j = a i := (first_spec a i).1
    have hfix : groupFirst a j = j := le_antisymm ((first_spec a j).2 j rfl)
      ((first_spec a i).2 _ ((first_spec a j).1.trans hj))
    exact ⟨j, (ite_eq_left hfix).trans (hj.trans hi)⟩

theorem unique {i j : B ((d + 1) * r)} (hi : expand r g x i = y) (hj : expand r g x j = y)
    (hy : y ≠ x) : i = j := by
  let a i := run g r (path d r i) x
  have least (t : B ((d + 1) * r)) (ht : expand r g x t = y) :
      a t = y ∧ ∀ v, a v = y → t ≤ v := by
    change (if groupFirst a t = t then a t else x) = y at ht
    split at ht
    next h => exact ⟨ht, fun v hv => h ▸ (first_spec a t).2 v (hv.trans ht.symm)⟩
    next => exact (hy ht.symm).elim
  exact le_antisymm ((least i hi).2 j (least j hj).1) ((least j hj).2 i (least i hi).1)

theorem reciprocal {A D : Format} {a : (Fmt.bank m d A).obj} (ha : Fmt.Reciprocal A a)
    (r : ℕ) (b : B m → D.obj) :
    Fmt.Reciprocal D (fun i => (expand r (fun j => (a j).1) i, b i)) := by
  intro i j h
  let g k := (a k).1
  have he : Reach g r i (expand r g i j) := mem.mp ⟨j, rfl⟩
  obtain ⟨l, hl⟩ := mem.mpr (he.symm fun i j h => (ha i j h).exists)
  exact ⟨l, hl, fun k hk => unique hk hl (Ne.symm h)⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
end
