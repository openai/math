import OAI.LinearAlgebra.MatrixExponent.Control.BucketNet
import OAI.LinearAlgebra.MatrixExponent.Control.Named
import OAI.LinearAlgebra.MatrixExponent.Install.Products
import OAI.LinearAlgebra.MatrixExponent.Diagonal.AlphabetCode
import OAI.LinearAlgebra.MatrixExponent.Processor.Guard
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels

section
/-!
# Reading a compact sequence at the marked slots

The prefix counter and the indirect reader use the same address
width. Doubling the array avoids truncating the extra counter bit.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.PackCode

open Install Control
abbrev Index (w : ℕ) := Fin (2 ^ w)

def scatter (w : ℕ) (x : Index w ⊕ Index w → Bool) (i : Index w) : Bool :=
  x (.inr (Fin.ofNat (2 ^ w) (histogram (x ∘ Sum.inl) true (some i))))

private def low (w : ℕ) (i : Index (w + 1)) : Index w := Fin.ofNat (2 ^ w) i.val

private def high (w : ℕ) (i : Index w) : Index (w + 1) :=
  i.castLE (by rw [pow_succ]; omega)

@[simp] private theorem low_high (w : ℕ) (i : Index w) : low w (high w i) = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

private theorem decode_bits (w u : ℕ) (hu : u < 2 ^ w) :
    decode w (bits (word w) (Lookup.bits w u)) = ⟨u, hu⟩ :=
  (decode w).apply_symm_apply ⟨u, hu⟩

theorem scatter_net (F : Type) [Field F] (w : ℕ) :
    BNet F (scatter w) (200000 * 2 ^ w * (w + 1) ^ 3) := by
  let A := Option (Index w) × slots (word (w + 1))
  have counts := (prefix_bnet F w).parallel (BNet.id F (Index w))
  let addr : Index (w + 1) ⊕ Index (w + 1) × slots (word (w + 1)) → A ⊕ Index w
    | .inl i => .inr (low w i)
    | .inr (i, j) => .inl (some (low w i), j)
  have h := (counts.comp ((read_net F (w + 1)).pull addr)).comp
    ((BNet.id F (Index w)).pull (high w))
  convert h.mono (n := 200000 * 2 ^ w * (w + 1) ^ 3) (by
    simp only [A, Index, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_option, card_slots, wd_word, Fintype.card_unit, slots]
    have hp : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by decide)
    have := Nat.le_mul_of_pos_right w hp
    ring_nf
    omega) using 1
  funext x i
  have hu : histogram (x ∘ Sum.inl) true (some i) < 2 ^ (w + 1) := by
    have := histogram_le (x ∘ Sum.inl) true (some i)
    have := Nat.one_le_pow w 2 (by decide)
    rw [pow_succ]
    omega
  change scatter w x i = x (.inr (low w (decode (w + 1)
    (bits (word (w + 1)) (Lookup.bits (w + 1) (histogram (x ∘ Sum.inl) true (some (low w (high w i)))))))))
  rw [low_high, decode_bits _ _ hu]
  rfl

def Matches (w : ℕ) (v marks data : Index w → Bool) : Prop :=
  ∀ i, marks i = true → v i = scatter w (Sum.elim marks data) i

open Classical in
theorem matches_net (F : Type) [Field F] (w : ℕ) :
    Weight F (fun x : Index w ⊕ Index w ⊕ Index w → Bool =>
      if Matches w (x ∘ Sum.inl) (fun j => x (.inr (.inl j))) (fun j => x (.inr (.inr j)))
      then 1 else 0) (210000 * 2 ^ w * (w + 1) ^ 3) := by
  let I := Index w ⊕ Index w ⊕ Index w
  have gather := (BNet.id F I).pair ((scatter_net F w).pull (Sum.inr : Index w ⊕ Index w → I))
  let row (x : Fin 3 → Bool) : F := if x 0 = true → x 1 = x 2 then 1 else 0
  let addr (p : Index w × Fin 3) : I ⊕ Index w :=
    if p.2 = 0 then .inl (.inr (.inl p.1)) else if p.2 = 1 then .inl (.inl p.1) else .inr p.1
  have h := gather.weight (((Weight.dense F (Fin 3) row).prod w).pull addr)
  convert h.mono (n := 210000 * 2 ^ w * (w + 1) ^ 3) (by
    simp only [I, Index, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring_nf
    omega) using 1
  funext x
  have he : Sum.elim (fun j => x (.inr (.inl j))) (fun j => x (.inr (.inr j))) =
      x ∘ Sum.inr := by funext j; cases j <;> rfl
  simp only [Matches, he]
  change _ = ∏ i, if x (.inr (.inl i)) = true → x (.inl i) = scatter w (x ∘ Sum.inr) i
    then 1 else 0
  simp only [Finset.prod_ite_zero, Finset.mem_univ, forall_const, Finset.prod_const_one, Function.comp_apply]

end OAI.LinearAlgebra.MatrixExponent.Processor.PackCode
end

section
/-! # Relating marked positions to ordered block concatenation -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.PackCode

open Finset Diagonal.Expansion
variable {w l : ℕ} {marks values data : Index w → Bool}

/-- The rank at a marked position is its index in the list of marks. -/
theorem rank_image {f : Fin l → Index w} (hf : StrictMono f)
    (hm : ∀ i, marks i = true ↔ ∃ j, f j = i) (j : Fin l) :
    Control.histogram marks true (some (f j)) = j.val := by
  rw [Control.histogram_some]
  have h : (univ.filter fun i => marks i = true ∧ i < f j) = (Iio j).image f := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_Iio, hm]
    constructor
    · rintro ⟨⟨k, rfl⟩, hk⟩
      exact ⟨k, hf.lt_iff_lt.mp hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, rfl⟩, hf hk⟩
  rw [h, card_image_of_injective _ hf.injective, Fin.card_Iio]

theorem matches_image {f : Fin l → Index w} (hf : StrictMono f)
    (hm : ∀ i, marks i = true ↔ ∃ j, f j = i) (hl : l ≤ 2 ^ w) :
    Matches w values marks data ↔ ∀ j, values (f j) = data (Fin.castLE hl j) := by
  have h (j : Fin l) : scatter w (Sum.elim marks data) (f j) = data (Fin.castLE hl j) := by
    change data (Fin.ofNat _ (Control.histogram marks true (some (f j)))) = _
    rw [rank_image hf hm]
    exact congrArg data (Fin.ext (Nat.mod_eq_of_lt (j.isLt.trans_le hl)))
  constructor
  · exact fun hs j => (hs _ ((hm _).mpr ⟨j, rfl⟩)).trans (h j)
  · intro hs i hi
    obtain ⟨j, rfl⟩ := (hm i).mp hi
    exact (hs j).trans (h j).symm

/-- Any order-preserving placement of the active cells works. Slots
between them, and compact-array positions past the last cell, are ignored. -/
theorem matches_pack {P : Type} [LinearOrder P] [Fintype P] (f : P → ℕ)
    (x : (p : P) → Fin (f p) → Bool) (hl : ∑ p, f p = l) (hw : l ≤ 2 ^ w)
    (addr : Lex (Σ p, Fin (f p)) → Index w) (ha : StrictMono addr)
    (hm : ∀ i, marks i = true ↔ ∃ z, addr z = i)
    (hx : ∀ z, values (addr z) = x z.1 z.2) :
    Matches w values marks data ↔ pack f hl.le x = data ∘ Fin.castLE hw := by
  subst l
  let e := packOrder f
  have h : ∀ i, marks i = true ↔ ∃ j, (addr ∘ e) j = i := by
    intro i
    rw [hm]
    exact ⟨fun ⟨z, hz⟩ => ⟨e.symm z, by simpa using hz⟩, fun ⟨j, hj⟩ => ⟨e j, hj⟩⟩
  rw [matches_image (ha.comp e.strictMono) h hw, funext_iff]
  apply forall_congr'
  intro j
  have he := pack_at f le_rfl x (e j)
  change pack f le_rfl x (e.symm (e j)) = _ at he
  rw [e.symm_apply_apply] at he
  simp only [Function.comp_apply, hx, he]

variable {P : Type} [LinearOrder P] [Fintype P] {s : ℕ}

/-- Absolute positions in the uncompressed array. Its first `s`
bits are reserved for the fixed-length selector prefix. -/
noncomputable def grid (cap : P → ℕ) (hc : s + ∑ p, cap p ≤ 2 ^ w) (p : P) (j : Fin (cap p)) :
    Index w :=
  Fin.castLE hc (Fin.natAdd s ((packOrder cap).symm ⟨p, j⟩))

private theorem grid_mono {f cap : P → ℕ} (hf : ∀ p, f p ≤ cap p)
    (hc : s + ∑ p, cap p ≤ 2 ^ w) :
    StrictMono (fun z : Lex (Σ p, Fin (f p)) => grid cap hc z.1 (Fin.castLE (hf _) z.2)) := by
  intro x y h
  change s + _ < s + _
  apply Nat.add_lt_add_left
  apply (packOrder cap).symm.strictMono
  rcases Sigma.Lex.lt_def.mp h with h | ⟨he, h⟩
  · exact Sigma.Lex.lt_def.mpr (.inl h)
  · obtain ⟨p, i⟩ := x
    obtain ⟨q, j⟩ := y
    change p = q at he
    subst q
    exact Sigma.Lex.lt_def.mpr (.inr ⟨rfl, h⟩)

private theorem mono_append {m : ℕ} (hs : s ≤ 2 ^ w)
    (g : Fin m → Index w) (hg : StrictMono g) (hstart : ∀ i, s ≤ (g i).val) :
    StrictMono (Fin.append (Fin.castLE hs) g) := by
  intro i j h
  induction i using Fin.addCases <;> induction j using Fin.addCases
  all_goals simp only [Fin.append_left, Fin.append_right]
  · exact h
  · exact (Fin.isLt (n := s) _).trans_le (hstart _)
  · simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
    omega
  · apply hg
    simpa only [Fin.lt_def, Fin.val_natAdd, add_lt_add_iff_left] using h

/-- Mark the entire fixed prefix and the initial `f p` slots of each
reserved block. The comparison checks the prefix and packed blocks. -/
theorem matches_grid {f cap : P → ℕ} (hf : ∀ p, f p ≤ cap p)
    (hl : ∑ p, f p = l) (hc : s + ∑ p, cap p ≤ 2 ^ w) (hw : s + l ≤ 2 ^ w)
    (head : Fin s → Bool) (x : (p : P) → Fin (f p) → Bool)
    (hm : ∀ i, marks i = true ↔ i.val < s ∨
      ∃ (p : P) (j : Fin (cap p)), j.val < f p ∧ grid cap hc p j = i)
    (hhead : ∀ (i : Fin s), values (Fin.castLE (by omega) i) = head i)
    (htail : ∀ (p : P) (j : Fin (f p)), values (grid cap hc p (j.castLE (hf p))) = x p j) :
    Matches w values marks data ↔ Fin.append head (pack f hl.le x) = data ∘ Fin.castLE hw := by
  subst l
  have hs : s ≤ 2 ^ w := by omega
  let addr (z : Lex (Σ p, Fin (f p))) := grid cap hc z.1 (Fin.castLE (hf _) z.2)
  let e := packOrder f
  let loc := Fin.append (Fin.castLE hs) (addr ∘ e)
  have hmono : StrictMono loc := mono_append hs _ ((grid_mono hf hc).comp e.strictMono)
    (fun i => Nat.le_add_right _ _)
  have hmark (i) : marks i = true ↔ ∃ j, loc j = i := by
    rw [hm]
    constructor
    · rintro (hi | ⟨p, j, hj, rfl⟩)
      · exact ⟨Fin.castAdd _ ⟨i, hi⟩, by dsimp only [loc]; rw [Fin.append_left]; rfl⟩
      · refine ⟨Fin.natAdd s (e.symm (toLex ⟨p, ⟨j, hj⟩⟩)), ?_⟩
        dsimp only [loc]; rw [Fin.append_right, Function.comp_apply, e.apply_symm_apply]
        rfl
    · rintro ⟨j, rfl⟩
      induction j using Fin.addCases with
      | left i => dsimp only [loc]; rw [Fin.append_left]; exact .inl i.isLt
      | right i =>
        dsimp only [loc]; rw [Fin.append_right]
        exact .inr ⟨(e i).1, Fin.castLE (hf _) (e i).2, (e i).2.isLt, rfl⟩
  rw [matches_image hmono hmark hw, funext_iff]
  apply forall_congr'
  intro i
  induction i using Fin.addCases with
  | left j => simp only [loc, Fin.append_left, Function.comp_apply, hhead]
  | right j =>
    have he := pack_at f le_rfl x (e j)
    change pack f le_rfl x (e.symm (e j)) = _ at he
    rw [e.symm_apply_apply] at he
    simp only [loc, Fin.append_right, Function.comp_apply, he, addr, htail]

end OAI.LinearAlgebra.MatrixExponent.Processor.PackCode

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Processor.PackCode
attribute [local instance] memberOrder

variable {F : Type} [Field F] {n r d h N w : ℕ} (A : Expansion F n h)
  {hn : 2 ≤ n} {R : A.Report r d} {c : Class r} {marks values data : Index w → Bool}

abbrev crossLen (z : A.Alphabet hn N R c) (p : A.Members hn R c) :=
  A.width (z.1.val p) R.1 (A.shared N R c)

/-- A shared class uses all the bits charged by its report. A single
prefix-count check therefore verifies its entire symbol. -/
theorem matches_alphabet (z : A.Alphabet hn N R c) (hsh : A.shared N R c = true)
    (cap : A.Members hn R c → ℕ) (hf : ∀ p, A.crossLen z p ≤ cap p)
    (hc : A.selectorWidth hn R c + ∑ p, cap p ≤ 2 ^ w) (hw : A.classWidth R c ≤ 2 ^ w)
    (hm : ∀ i, marks i = true ↔ i.val < A.selectorWidth hn R c ∨
      ∃ (p : A.Members hn R c) (j : Fin (cap p)),
        j.val < A.crossLen z p ∧ grid cap hc p j = i)
    (hhead : ∀ i : Fin (A.selectorWidth hn R c),
      values (Fin.castLE (by omega) i) = A.selectorPrefix z.1 i)
    (htail : ∀ (p : A.Members hn R c) (j : Fin (A.crossLen z p)),
      values (grid cap hc p (j.castLE (hf p))) = z.2 p j) :
    Matches w values marks data ↔ A.alphabetCode hn N R c z = data ∘ Fin.castLE hw := by
  have hlen : A.classWidth R c = A.selectorWidth hn R c + ∑ p, A.crossLen z p := by
    simpa only [crossLen, width, hsh, ite_true] using A.classWidth_split z.1
  have hl : ∑ p, A.crossLen z p = A.classWidth R c - A.selectorWidth hn R c := by omega
  have hw' : A.selectorWidth hn R c + (A.classWidth R c - A.selectorWidth hn R c) ≤ 2 ^ w := by omega
  rw [matches_grid hf hl hc hw' (A.selectorPrefix z.1) z.2 hm hhead htail]
  constructor
  · intro h
    funext j
    exact congrFun h (A.codeSplit z.1 j)
  · intro h
    funext j
    exact congrFun h ((A.codeSplit z.1).symm j)

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

/-!
# Fixed-width private packet records

The selector and its crossing bits fit in one record of constant size
for a fixed cube identity. Out-of-range selector codes and nonzero
padding bits carry zero weight.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel

open Diagonal Finset Classical
variable {F : Type} [Field F] {n h p w t : ℕ} (A : Expansion F n h)

inductive Mode where
  | joint
  | both
  | side (b : Bool)
  deriving Fintype, DecidableEq

def Mode.cut : Mode → Bool
  | .joint => false
  | _ => true

def Mode.share : Mode → Bool
  | .side _ => true
  | _ => false

abbrev prefixSize := Nat.clog 2 (Fintype.card A.I)
def reserve := ∑ s, ∑ i, A.cross s i

theorem width_le (s : A.I) (i : Fin n) (b : Bool) : A.width s i b ≤ reserve A := by
  cases b
  · exact Nat.zero_le _
  · exact (single_le_sum (f := A.cross s) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
      (single_le_sum (f := fun z => ∑ j, A.cross z j) (fun _ _ => Nat.zero_le _) (mem_univ s))

abbrev Code := Fin (prefixSize A) ⊕ Fin (reserve A)
abbrev Row := (Bool × Spectral.Cube n × Fin h) ⊕ Code A
abbrev Inputs (p w t : ℕ) := (Fin p × Row A) ⊕ (A.I × Fin w) ⊕ PackCode.Index t

private theorem inhabited : Nonempty A.I := by
  by_contra hempty
  have : IsEmpty A.I := not_nonempty_iff.mp hempty
  have := A.full (fun _ => false) (fun _ => false)
  simp at this

def selector (z : Code A → Bool) : A.I :=
  letI := inhabited A
  Function.invFun A.selectorCode (z ∘ Sum.inl)

def used (i : Fin n) (b : Bool) (z : Code A → Bool) := A.width (selector A z) i b

def crossing (i : Fin n) (b : Bool) (z : Code A → Bool) (j : Fin (used A i b z)) :=
  z (.inr (j.castLE (width_le A _ _ _)))

def encode (i : Fin n) (b : Bool) (s : A.I) (v : Fin (A.width s i b) → Bool) : Code A → Bool :=
  Sum.elim (A.selectorCode s) (fun j => if hj : j.val < A.width s i b then v ⟨j, hj⟩ else false)

@[simp] theorem selector_encode (i : Fin n) (b : Bool) (s : A.I) (v : Fin (A.width s i b) → Bool) :
    selector A (encode A i b s v) = s := by
  have := inhabited A
  exact Function.leftInverse_invFun A.selectorCode.injective s

def ok (i : Fin n) (b : Bool) (z : Code A → Bool) : Prop :=
  encode A i b (selector A z) (crossing A i b z) = z

private theorem apply_encode {X : Type} (i : Fin n) (b : Bool)
    (s : A.I) (v : Fin (A.width s i b) → Bool)
    (g : (t : A.I) → (Fin (A.width t i b) → Bool) → X) :
    g (selector A (encode A i b s v)) (crossing A i b (encode A i b s v)) = g s v := by
  let k (t : A.I) (j : Fin (A.width t i b)) := encode A i b s v (.inr (j.castLE (width_le A t i b)))
  change g _ (k _) = _
  rw [selector_encode]
  apply congrArg (g s)
  funext j
  simp [k, encode, j.isLt]

@[simp] theorem ok_encode (i : Fin n) (b : Bool) (s : A.I) (v : Fin (A.width s i b) → Bool) :
    ok A i b (encode A i b s v) :=
  apply_encode A i b s v (encode A i b)

def modeValue (mode : Mode) (s : A.I) (i : Fin n) (x y : Block n h) :
    (cut : Bool) → (Fin (A.width s i cut) → Bool) → F
  | false, _ => A.weight s x y
  | true, z => match mode with
    | .side b => A.side s i b x y z
    | _ => A.value s i x y true z

def entry (i : Fin n) (mode : Mode) (u : Row A → Bool) : F :=
  let z := u ∘ Sum.inr
  if ok A i mode.cut z then
    modeValue A mode (selector A z) i (fun j => u (.inl (false, j))) (fun j => u (.inl (true, j)))
      mode.cut (crossing A i mode.cut z)
  else 0

theorem entry_encode (i : Fin n) (mode : Mode) (b : Bool) (hb : mode.cut = b)
    (s : A.I) (v : Fin (A.width s i b) → Bool) (u : Row A → Bool)
    (hu : u ∘ Sum.inr = encode A i b s v) :
    entry A i mode u =
      modeValue A mode s i (fun j => u (.inl (false, j))) (fun j => u (.inl (true, j))) b v := by
  unfold entry
  dsimp only
  rw [hu, hb, ite_eq_left (ok_encode A i b s v)]
  exact apply_encode A i b s v (fun t v =>
    modeValue A mode t i (fun j => u (.inl (false, j))) (fun j => u (.inl (true, j))) b v)

def row (x : Inputs A p w t → Bool) (j : Fin p) (u : Row A) := x (.inl (j, u))
def raw (x : Inputs A p w t → Bool) (j : Fin p) := row A x j ∘ Sum.inr
def expected (x : Inputs A p w t → Bool) (s : A.I) := number (fun j => x (.inr (.inl (s, j))))
def compact (x : Inputs A p w t → Bool) (j : PackCode.Index t) := x (.inr (.inr j))

def tally (x : Inputs A p w t → Bool) (s : A.I) := multiplicity (selector A ∘ raw A x) s

/-- Uncompressed addresses reserve the full selector prefix and a
fixed crossing capacity for every packet in order. -/
def address (p : ℕ) : Fin p × Code A ≃ Fin (p * prefixSize A + p * reserve A) :=
  (Equiv.prodSumDistrib _ _ _).trans ((finProdFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv)

def position (p : ℕ) (z : Fin p × Code A) := (address A p z).val

theorem position_inj (p : ℕ) : Function.Injective (position A p) :=
  Fin.val_injective.comp (address A p).injective

def valueAt (x : Inputs A p w t → Bool) (k : PackCode.Index t) : Bool :=
  Function.extend (position A p) (fun z => raw A x z.1 z.2) (fun _ => false) k.val

def markAt (i : Fin n) (mode : Mode) (x : Inputs A p w t → Bool) (k : PackCode.Index t) : Bool :=
  Function.extend (position A p) (fun z => Sum.elim (fun _ => true)
    (fun j => decide (j.val < used A i mode.cut (raw A x z.1))) z.2) (fun _ => false) k.val

def kernel (i : Fin n) (mode : Mode) (x : Inputs A p w t → Bool) : F :=
  if (∀ s, tally A x s = expected A x s) ∧
      (mode.share = true → PackCode.Matches t (valueAt A x) (markAt A i mode x) (compact A x)) then
    ∏ j, entry A i mode (row A x j)
  else 0

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end

/-! # An exact count check on fixed-width packet records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
open Install Classical Diagonal Finset
variable {F : Type} [Field F] {n h p w t v : ℕ} (A : Expansion F n h)

private theorem register_eq {I : Type} [Fintype I] {f g : (I → Bool) → ℕ} {a b : ℕ}
    (hf : Register F v f a) (hg : Register F v g b)
    (h₁ : ∀ x, f x < 2 ^ v) (h₂ : ∀ x, g x < 2 ^ v) :
    Weight F (fun x => if f x = g x then 1 else 0)
      (15 * Fintype.card I + 2 * a + 2 * b + 2100 * (1 + v)) := by
  have h := (hf.less hg h₁ h₂).pair (hg.less hf h₂ h₁)
  have k := h.weight (Weight.dense F (Unit ⊕ Unit)
    (fun x => if x (.inl ()) = false ∧ x (.inr ()) = false then 1 else 0))
  convert k.mono (n := 15 * Fintype.card I + 2 * a + 2 * b + 2100 * (1 + v)) (by simp; omega) using 1
  funext x
  simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr, decide_eq_false_iff_not, not_lt,
    ← le_antisymm_iff]
  simp only [eq_comm]

theorem raw_support (j : Fin p) :
    ∃ S : Finset (Inputs A p w t), S.card ≤ Fintype.card (Code A) ∧
      ∀ x y, (∀ u ∈ S, x u = y u) → raw A x j = raw A y j := by
  let k : Code A → Inputs A p w t := fun u => .inl (j, .inr u)
  exact ⟨univ.image k, card_image_le,
    fun x y he => funext (fun i => he _ (mem_image_of_mem k (mem_univ i)))⟩

private theorem tally_net (s : A.I) (v : ℕ) :
    Register F v (fun x : Inputs A p w t → Bool => tally A x s)
      (Fintype.card (Inputs A p w t) + localCost (Fintype.card (Code A)) * p +
        20000 * (1 + p) * (1 + v)) := by
  let f (x : Inputs A p w t → Bool) (j : Fin p) := decide (selector A (raw A x j) = s)
  have dep : Depends f (Fintype.card (Code A)) := by
    intro j
    obtain ⟨S, hS, h⟩ := raw_support A (w := w) (t := t) j
    exact ⟨S, hS, fun x y he => by simp only [f, h x y he]⟩
  have hh := (dep.bnet F).comp (Register.weighted F v (fun _ : Fin p => 1))
  rw [Fintype.card_fin] at hh
  unfold Register
  convert hh using 1
  funext x
  congr 1
  simp [f, tally, Diagonal.multiplicity, Fintype.card_subtype]

private theorem expected_net (s : A.I) (v : ℕ) :
    Register F v (fun x : Inputs A p w t → Bool => expected A x s)
      (Fintype.card (Inputs A p w t) + 2 * w + 20000 * (1 + w) * (1 + v)) := by
  have h := BNet.pull (Register.weighted F v (fun j : Fin w => 2 ^ j.val))
    (fun j => (.inr (.inl (s, j)) : Inputs A p w t))
  rw [Fintype.card_fin] at h
  exact h

def countCost (p w t : ℕ) :=
  30 * Fintype.card (Inputs A p w t) + 2 * localCost (Fintype.card (Code A)) * p +
    100000 * (1 + p + w) * (2 + t + w)

theorem checked_counts (hp : p ≤ 2 ^ t) :
    Weight F (fun x : Inputs A p w t → Bool => if ∀ s, tally A x s = expected A x s then 1 else 0)
      ((1 + Fintype.card A.I) * countCost A p w t) := by
  let v := 1 + t + w
  let I := Inputs A p w t
  let test (s : A.I) (x : I → Bool) := if tally A x s = expected A x s then (1 : F) else 0
  have hh (s : A.I) : Weight F (test s) (countCost A p w t - 5 * Fintype.card I) := by
    have ht (x : I → Bool) : tally A x s < 2 ^ v := calc
      tally A x s ≤ Fintype.card (Fin p) := Fintype.card_subtype_le (fun j => selector A (raw A x j) = s)
      _ ≤ 2 ^ t := by simpa using hp
      _ < 2 ^ v := Nat.pow_lt_pow_right (by decide) (by omega)
    have he (x : I → Bool) : expected A x s < 2 ^ v :=
      (number_lt _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    apply (register_eq (tally_net A s v) (expected_net A s v) ht he).mono
    unfold countCost I v
    ring_nf
    omega
  have net := Weight.finite_product test hh
  simp only [test, prod_ite_zero, mem_univ, forall_const, prod_const_one] at net
  apply net.mono
  have ht : 5 * Fintype.card I ≤ countCost A p w t := by unfold countCost I; omega
  rw [Nat.add_sub_of_le ht, add_mul, one_mul]
  omega

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end

/-!
# A trivalent network for one packet class

Prepare marks and values with bounded input dependence. The remaining
work is one batched read, histogram comparisons, and independent
constant-arity weights.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel

open Install Classical Diagonal Finset PackCode
variable {F : Type} [Field F] {n h p w t : ℕ} (A : Expansion F n h) (i : Fin n) (mode : Mode)

private def requests (x : Inputs A p w t → Bool) : Index t ⊕ Index t ⊕ Index t → Bool :=
  Sum.elim (valueAt A x) (Sum.elim (fun j => mode.share && markAt A i mode x j) (compact A x))

private theorem request_dep :
    Depends (requests (p := p) (w := w) (t := t) A i mode) (1 + Fintype.card (Code A)) := by
  have both (j : Index t) :
      ∃ S : Finset (Inputs A p w t), S.card ≤ 1 + Fintype.card (Code A) ∧
        ∀ x y, (∀ u ∈ S, x u = y u) →
          valueAt A x j = valueAt A y j ∧ markAt A i mode x j = markAt A i mode y j := by
    by_cases hj : ∃ k, position A p k = j.val
    · obtain ⟨⟨u, k⟩, he⟩ := hj
      obtain ⟨S, hS, hs⟩ := raw_support A (w := w) (t := t) u
      refine ⟨S, by omega, fun x y h => ?_⟩
      simp only [valueAt, markAt, ← he, (position_inj A p).extend_apply, hs x y h, and_self]
    · refine ⟨∅, by simp, fun x y _ => ?_⟩
      simp only [valueAt, markAt, Function.extend_apply' _ _ _ hj, and_self]
  rintro (j|j|j)
  · obtain ⟨S, hS, he⟩ := both j
    exact ⟨S, hS, fun x y h => (he x y h).1⟩
  · obtain ⟨S, hS, he⟩ := both j
    exact ⟨S, hS, fun x y h => congrArg (mode.share && ·) (he x y h).2⟩
  · exact ⟨{.inr (.inr j)}, by simp, fun x y h => h _ (mem_singleton_self _)⟩

private theorem checked_stream :
    Weight F (fun x : Inputs A p w t → Bool =>
      if mode.share = true → Matches t (valueAt A x) (markAt A i mode x) (compact A x) then 1 else 0)
      (Fintype.card (Inputs A p w t) + localCost (1 + Fintype.card (Code A)) * (3 * 2 ^ t) +
        210000 * 2 ^ t * (t + 1) ^ 3) := by
  have hr := (request_dep (p := p) (w := w) (t := t) A i mode).bnet F
  have hs := hr.weight (matches_net F t)
  convert hs using 1
  · funext x
    cases he : mode.share <;> simp [requests, Matches, he]
  · simp only [Fintype.card_sum, Fintype.card_fin, Index]
    ring

private theorem entries_net :
    Weight F (fun x : Inputs A p w t → Bool => ∏ j, entry A i mode (row A x j))
      (Fintype.card (Inputs A p w t) + 2 * (p * Fintype.card (Row A)) +
        p * (8 * 2 ^ Fintype.card (Row A))) := by
  have h := Weight.sigma_prod (fun _ : Fin p => entry A i mode)
    (fun _ => Weight.dense F (Row A) (entry A i mode))
  let addr (z : Σ _ : Fin p, Row A) : Inputs A p w t := .inl (z.1, z.2)
  convert h.pull addr using 1 <;> try rfl
  simp only [Fintype.card_sigma, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin]

private def rawCost (p w t : ℕ) :=
  12 * Fintype.card (Inputs A p w t) + (1 + Fintype.card A.I) * countCost A p w t +
    localCost (1 + Fintype.card (Code A)) * (3 * 2 ^ t) + 210000 * 2 ^ t * (t + 1) ^ 3 +
    2 * (p * Fintype.card (Row A)) + p * (8 * 2 ^ Fintype.card (Row A))

private theorem raw_net (hp : p ≤ 2 ^ t) :
    Weight F (kernel (p := p) (w := w) (t := t) A i mode) (rawCost A p w t) := by
  have h := (checked_counts (w := w) A hp).mul ((checked_stream A i mode).mul (entries_net A i mode))
  convert h using 1
  · funext x
    simp only [kernel, ite_and, ite_mul, one_mul, zero_mul]
  · unfold rawCost
    ring

def cost :=
  let M := 1 + Fintype.card (Row A) + Fintype.card A.I
  12 * M + (1 + Fintype.card A.I) * (30 * M + 2 * localCost (Fintype.card (Code A)) + 400000) +
    3 * localCost (1 + Fintype.card (Code A)) + 210000 +
    2 * Fintype.card (Row A) + 8 * 2 ^ Fintype.card (Row A)

theorem kernel_net (hp : p ≤ 2 ^ t) :
    Weight F (kernel (p := p) (w := w) (t := t) A i mode) (cost A * 2 ^ t * (1 + w + t) ^ 3) := by
  apply (raw_net A i mode hp).mono
  let M := 1 + Fintype.card (Row A) + Fintype.card A.I
  let v := 1 + w + t
  let U := 2 ^ t * v ^ 3
  have hB : 0 < 2 ^ t := by positivity
  have hv : 0 < v := by omega
  have ht : 2 ^ t ≤ U := Nat.le_mul_of_pos_right _ (by positivity)
  have hp' := hp.trans ht
  have hv' : v ≤ U := (Nat.le_pow (by decide : 0 < 3)).trans (Nat.le_mul_of_pos_left _ hB)
  have hi : Fintype.card (Inputs A p w t) ≤ M * U := by
    rw [Fintype.card_sum, Fintype.card_sum (α := A.I × Fin w),
      Fintype.card_prod (Fin p) (Row A), Fintype.card_prod A.I (Fin w),
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    calc
      _ ≤ U * Fintype.card (Row A) + (Fintype.card A.I * U + U) := by gcongr; omega
      _ = _ := by unfold M; ring
  have hw : (1 + p + w) * (2 + t + w) ≤ 4 * U := by
    calc
      _ ≤ (2 ^ t + v) * (2 * v) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ (2 ^ t * v + 2 ^ t * v) * (2 * v) := by
        gcongr
        · exact Nat.le_mul_of_pos_right _ hv
        · exact Nat.le_mul_of_pos_left _ hB
      _ = 4 * 2 ^ t * v ^ 2 := by ring
      _ ≤ _ := by unfold U; rw [← mul_assoc]; gcongr; decide
  have hh : countCost A p w t ≤ (30 * M + 2 * localCost (Fintype.card (Code A)) + 400000) * U := by
    unfold countCost
    rw [mul_assoc 100000]
    calc
      _ ≤ 30 * (M * U) + 2 * localCost (Fintype.card (Code A)) * U + 100000 * (4 * U) := by gcongr
      _ = _ := by ring
  have hh' : 210000 * 2 ^ t * (t + 1) ^ 3 ≤ 210000 * U := by unfold U; rw [← mul_assoc]; gcongr; omega
  unfold rawCost
  calc
    _ ≤ 12 * (M * U) + (1 + Fintype.card A.I) * ((30 * M + 2 * localCost (Fintype.card (Code A)) + 400000) * U) +
        localCost (1 + Fintype.card (Code A)) * (3 * U) + 210000 * U +
        2 * (U * Fintype.card (Row A)) + U * (8 * 2 ^ Fintype.card (Row A)) := by gcongr
    _ = cost A * U := by unfold cost; dsimp only [M]; ring
    _ = _ := by rw [mul_assoc]

def rowSize := prefixSize A + reserve A + 1
def height (p : ℕ) := Nat.clog 2 ((p + 1) * rowSize A)

theorem height_bounds (p : ℕ) :
    (p + 1) * rowSize A ≤ 2 ^ height A p ∧ 2 ^ height A p ≤ 2 * ((p + 1) * rowSize A) := by
  let k := (p + 1) * rowSize A
  have hk : 0 < k := by unfold k rowSize; positivity
  refine ⟨Nat.le_pow_clog (by decide) _, ?_⟩
  have hu : height A p ≤ Nat.log 2 k + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide : 1 < 2) k).le
  calc
    _ ≤ 2 ^ (Nat.log 2 k + 1) := Nat.pow_le_pow_right (by decide) hu
    _ ≤ 2 * k := by rw [pow_succ']; exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ hk.ne')

theorem capacity (p : ℕ) : p * (prefixSize A + reserve A) ≤ 2 ^ height A p :=
  (Nat.mul_le_mul (Nat.le_succ p) (Nat.le_succ _)).trans (height_bounds A p).1

def rate :=
  Weight.switchCost 2 * (Fintype.card (Row A) + Fintype.card A.I + 2 * rowSize A +
    cost A * (2 * rowSize A) * (2 + Nat.clog 2 (rowSize A)) ^ 3 + 1)

/-- A two-bit mode can vary with the report. The cost per member is
polynomial in the width of the count fields and independent of the cut. -/
theorem switched_net (pick : (Fin 2 → Bool) → Mode) (hp : p < 2 ^ w) :
    Weight F (fun x : Fin 2 ⊕ Inputs A p w (height A p) → Bool =>
      kernel A i (pick (x ∘ Sum.inl)) (x ∘ Sum.inr)) (rate A * (1 + p) * (1 + w) ^ 3) := by
  let t := height A p
  have hs : 0 < rowSize A := by unfold rowSize; omega
  obtain ⟨hlo, hhi⟩ := height_bounds A p
  have hpt : p ≤ 2 ^ t := ((Nat.le_succ p).trans (Nat.le_mul_of_pos_right _ hs)).trans hlo
  have ht : t ≤ w + Nat.clog 2 (rowSize A) := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    exact Nat.mul_le_mul hp (Nat.le_pow_clog (by decide) _)
  let v := 2 + Nat.clog 2 (rowSize A)
  have hlen : 1 + w + t ≤ v * (1 + w) := by unfold v; ring_nf; omega
  have hc : Fintype.card (Inputs A p w t) ≤
      p * Fintype.card (Row A) + Fintype.card A.I * w + 2 * ((p + 1) * rowSize A) := by
    rw [Fintype.card_sum, Fintype.card_sum (α := A.I × Fin w),
      Fintype.card_prod (Fin p) (Row A), Fintype.card_prod A.I (Fin w),
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, ← add_assoc]
    exact Nat.add_le_add_left hhi _
  apply (Weight.switch _ (fun z => kernel_net A i (pick z) (w := w) hpt)).mono
  rw [Fintype.card_fin, rate, mul_assoc _ (1 + p), mul_assoc (Weight.switchCost 2)]
  apply Nat.mul_le_mul_left
  calc
    _ ≤ p * Fintype.card (Row A) + Fintype.card A.I * w + 2 * ((p + 1) * rowSize A) +
        cost A * (2 * ((p + 1) * rowSize A)) * (v * (1 + w)) ^ 3 + 1 := by gcongr
    _ ≤ _ := by rw [show 2 + Nat.clog 2 (rowSize A) = v from rfl]; ring_nf; omega

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end

/-! # Private assignments for a fixed class and public report -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel

open Classical Diagonal
variable {F : Type} [Field F] {n h p w t r N d : ℕ} (A : Expansion F n h)
  {hn : 2 ≤ n} {R : A.Report r d} {c : Class r}

attribute [local instance] Expansion.memberOrder

scoped instance memberLE : LE (A.Members hn R c) := (A.memberOrder hn R c).toLE
scoped instance memberLT : LT (A.Members hn R c) := (A.memberOrder hn R c).toLT

abbrev MemberOrder (hn : 2 ≤ n) (R : A.Report r d) (c : Class r) (p : ℕ) :=
  @OrderIso (Fin p) (A.Members hn R c) _ (A.memberOrder hn R c).toLE

def enumerate (hp : Fintype.card (A.Members hn R c) = p) : MemberOrder A hn R c p :=
  Fintype.orderIsoFinOfCardEq _ hp

def symbol (e : MemberOrder A hn R c p) (z : A.Alphabet hn N R c) (j : Fin p) : Code A → Bool :=
  encode A R.1 (A.shared N R c) (z.1.val (e j)) (z.2 (e j))

theorem symbol_injective (e : MemberOrder A hn R c p) :
    Function.Injective (symbol A (N := N) e) := by
  rintro ⟨s, x⟩ ⟨s', y⟩ he
  have hs : s = s' := by
    apply Subtype.ext
    funext j
    obtain ⟨k, rfl⟩ := e.surjective j
    simpa only [symbol, selector_encode] using congrArg (selector A) (congrFun he k)
  subst s'
  congr 1
  funext j k
  obtain ⟨l, rfl⟩ := e.surjective j
  have h' := congrFun (congrFun he l) (.inr (k.castLE (width_le A _ _ _)))
  simpa [symbol, encode, k.isLt] using h'

private theorem multiplicity_equiv {I J Z : Type} [Fintype I] [Fintype J] [DecidableEq Z]
    (e : I ≃ J) (f : J → Z) (z : Z) : multiplicity (f ∘ e) z = multiplicity f z :=
  Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

theorem symbol_iff (e : MemberOrder A hn R c p) (x : Inputs A p w t → Bool) :
    (∀ j, ok A R.1 (A.shared N R c) (raw A x j)) ∧
      (∀ s, tally A x s = (R.2 (c, s)).val) ↔ ∃ z : A.Alphabet hn N R c, symbol A e z = raw A x := by
  constructor
  · rintro ⟨hraw, ht⟩
    let f := selector A ∘ raw A x
    let s : A.Selectors hn R c :=
      ⟨f ∘ e.symm, fun k => (multiplicity_equiv e.symm.toEquiv f k).trans (ht k)⟩
    let z : A.Alphabet hn N R c :=
      ⟨s, fun j => crossing A R.1 (A.shared N R c) (raw A x (e.symm j))⟩
    refine ⟨z, funext fun j => ?_⟩
    exact (hraw (e.symm (e j))).trans (by rw [e.symm_apply_apply])
  · rintro ⟨z, hz⟩
    constructor
    · rw [← hz]
      exact fun j => ok_encode A _ _ _ _
    · intro s
      have hf : selector A ∘ raw A x = z.1.val ∘ e := by
        funext j
        rw [← hz]
        exact selector_encode A _ _ _ _
      rw [tally, hf]
      exact (multiplicity_equiv e.toEquiv _ _).trans (z.1.2 s)

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end

/-! # Checking a packed shared symbol in a fixed rectangular layout -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel

open Finset Diagonal Diagonal.Expansion PackCode
variable {F : Type} [Field F] {n h p w t r N d : ℕ} (A : Expansion F n h)
  {hn : 2 ≤ n} {R : A.Report r d} {c : Class r}

attribute [local instance] memberOrder

private theorem fixed_rank {P : Type} [LinearOrder P] [Fintype P] (e : Fin p ≃o P)
    (D : ℕ) (j : Fin p) (k : Fin D) :
    ((packOrder (fun _ : P => D)).symm (toLex ⟨e j, k⟩)).val = (finProdFinEquiv (j, k)).val := by
  rw [packOrder, serial_rank]
  change start (fun _ => D) (e j) + k.val = k.val + D * j.val
  rw [start, sum_filter, ← e.toEquiv.sum_comp]
  change (∑ i, if e i < e j then D else 0) + k.val = _
  simp only [e.lt_iff_lt, ← sum_filter]
  rw [show univ.filter (fun i => i < j) = Iio j by ext; simp]
  simp [Fin.card_Iio, mul_comm, add_comm]

theorem symbol_width (e : MemberOrder A hn R c p) (z : A.Alphabet hn N R c) :
    A.classWidth R c ≤ p * (prefixSize A + reserve A) := by
  have hp : Fintype.card (A.Members hn R c) = p := (Fintype.card_congr e.symm.toEquiv).trans (Fintype.card_fin _)
  rw [A.classWidth_spec z.1]
  calc
    _ ≤ ∑ _ : A.Members hn R c, (prefixSize A + reserve A) := by
      apply sum_le_sum
      intro j _
      rw [add_comm]
      exact Nat.add_le_add_left (width_le A _ _ true) _
    _ = _ := by simp only [sum_const, card_univ, hp, nsmul_eq_mul, Nat.cast_id]

private theorem value_at (x : Inputs A p w t → Bool) (j : Fin p) (k : Code A)
    (i : Index t) (hi : position A p (j, k) = i.val) :
    valueAt A x i = raw A x j k := by
  unfold valueAt
  rw [← hi, (position_inj A p).extend_apply]

private theorem mark_at (i : Fin n) (mode : Mode) (x : Inputs A p w t → Bool) (j : Fin p)
    (k : Code A) (u : Index t) (hu : position A p (j, k) = u.val) :
    markAt A i mode x u = Sum.elim (fun _ => true)
      (fun b => decide (b.val < used A i mode.cut (raw A x j))) k := by
  unfold markAt
  rw [← hu, (position_inj A p).extend_apply]

theorem match_code (e : MemberOrder A hn R c p) (z : A.Alphabet hn N R c) (mode : Mode)
    (x : Inputs A p w t → Bool) (hz : symbol A e z = raw A x)
    (hcut : mode.cut = A.shared N R c) (hsh : A.shared N R c = true)
    (hcap : p * (prefixSize A + reserve A) ≤ 2 ^ t) :
    Matches t (valueAt A x) (markAt A R.1 mode x) (compact A x) ↔
      A.alphabetCode hn N R c z = compact A x ∘ Fin.castLE ((symbol_width A e z).trans hcap) := by
  let P := A.Members hn R c
  let : LT P := (A.memberOrder hn R c).toLT
  let D := fun _ : P => reserve A
  let H := fun _ : P => prefixSize A
  have hp : Fintype.card P = p := (Fintype.card_congr e.symm.toEquiv).trans (Fintype.card_fin _)
  have hs : A.selectorWidth hn R c = p * prefixSize A := by
    change (∑ _j : P, prefixSize A) = _
    simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, hp]
  have hc : A.selectorWidth hn R c + ∑ j, D j ≤ 2 ^ t := by
    simpa only [D, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, hp, hs, ← mul_add] using hcap
  have hu (j) : used A R.1 mode.cut (raw A x j) = A.crossLen z (e j) := by
    simp only [← hz, used, symbol, selector_encode, hcut, crossLen]
  have hpos (j : Fin p) (k : Fin (reserve A)) :
      position A p (j, .inr k) = (grid D hc (e j) k).val := by
    change p * prefixSize A + (finProdFinEquiv (j, k)).val =
      A.selectorWidth hn R c + ((packOrder D).symm (toLex ⟨e j, k⟩)).val
    rw [hs]
    exact congrArg _ (fixed_rank e (reserve A) j k).symm
  refine A.matches_alphabet z hsh D (fun _ => width_le A _ _ _) hc _ ?_ ?_ ?_
  · intro i
    constructor
    · intro hm
      have hex : ∃ y, position A p y = i.val := by
        by_contra! hh
        unfold markAt at hm
        rw [Function.extend_apply' _ _ _ (not_exists.mpr hh)] at hm
        contradiction
      obtain ⟨⟨j, k|k⟩, he⟩ := hex
      · left
        rw [hs, ← he]
        exact (finProdFinEquiv (j, k)).isLt
      · right
        rw [mark_at A R.1 mode x j (.inr k) i he] at hm
        refine ⟨e j, k, ?_, Fin.ext ((hpos j k).symm.trans he)⟩
        simpa only [Sum.elim_inr, decide_eq_true_eq, hu] using hm
    · rintro (hi | ⟨j, k, hk, rfl⟩)
      · rw [hs] at hi
        obtain ⟨⟨j, k⟩, hh⟩ := finProdFinEquiv.surjective (⟨i.val, hi⟩ : Fin (p * prefixSize A))
        exact mark_at A R.1 mode x j (.inl k) i (congrArg Fin.val hh)
      · obtain ⟨u, rfl⟩ := e.surjective j
        rw [mark_at A R.1 mode x u (.inr k) _ (hpos u k)]
        simp only [Sum.elim_inr, decide_eq_true_eq, hu, hk]
  · intro i
    obtain ⟨⟨j, k⟩, rfl⟩ := (packOrder H).symm.surjective i
    obtain ⟨u, rfl⟩ := e.surjective j
    have hh := pack_at H le_rfl (fun j => A.selectorCode (z.1.val j)) (toLex ⟨e u, k⟩)
    calc
      _ = raw A x u (.inl k) := by
        apply value_at
        exact (fixed_rank e (prefixSize A) u k).symm
      _ = _ := by rw [← hz]; exact hh.symm
  · intro j k
    obtain ⟨u, rfl⟩ := e.surjective j
    rw [value_at A x u (.inr _) _ (hpos u _), ← hz]
    simp [symbol, encode, k.isLt]

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end
