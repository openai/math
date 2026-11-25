import OAI.LinearAlgebra.MatrixExponent.Coloring.Add
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Processor.Guard
import OAI.LinearAlgebra.MatrixExponent.Control.BucketNet

section
/-!
# Simultaneous arithmetic on valid inputs

The same circuit handles every setting in the indicated domain.
Registers are interpreted modulo their capacity. Only comparisons and
indirect reads need hypotheses about the sizes of their operands.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector
open Coloring
variable {F S : Type} [Field F] {w : ℕ} {U : Coloring.Format}

abbrev Array (S : Type) (w : ℕ) := S → B w → ℕ

def fits (f : Array S w) := ∀ s i, f s i < 2 ^ w

def packed (F : Type) [Field F] (inp : S → U.obj) (f : Array S w) (c : ℕ) : Prop :=
  ∃ g, Coloring.Cheap F w w U (Perm w) g c ∧ ∀ s i, g (inp s) i = Fin.ofNat (2 ^ w) (f s i)

namespace packed

variable {inp : S → U.obj} {f g : Array S w} {m n : ℕ}

theorem mono (h : packed F inp f m) (le : m ≤ n) : packed F inp f n := by
  obtain ⟨a, ha, he⟩ := h
  exact ⟨a, ha.mono le, he⟩

theorem const (F : Type) [Field F] (inp : S → U.obj) (f : B w → ℕ)
    (hw : U.width ≤ 2 ^ w * (100 + w) ^ m) : packed F inp (fun _ => f) (m + 2) := by
  have h₁ : U.width ≤ 2 ^ w * (100 + w) ^ (m + 1) := hw.trans (by gcongr; omega)
  have h₂ : (Perm w).width ≤ 2 ^ w * (100 + w) ^ (m + 1) := by
    rw [Format.width_vec, Format.width_addr]
    exact Nat.mul_le_mul_left _ ((Nat.le_add_left _ _).trans (Nat.le_pow (by omega)))
  exact ⟨_, Cheap.const F h₁ h₂ (fun i => Fin.ofNat (2 ^ w) (f i)), fun _ _ => rfl⟩

theorem width (hf : packed F inp f m) : U.width ≤ 2 ^ w * (100 + w) ^ m := by
  obtain ⟨_, ⟨v, _, hv⟩, _⟩ := hf
  omega

theorem lookup (hf : packed F inp f m) (hg : packed F inp g n) :
    packed F inp (fun s i => f s (Fin.ofNat (2 ^ w) (g s i))) (max m n + 10) := by
  obtain ⟨a, ha, he⟩ := hf
  obtain ⟨b, hb, hi⟩ := hg
  have h := (ha.pair hb).comp (Cheap.lookup F w w (.addr w) le_rfl (by simp))
  exact ⟨_, h.mono (by omega), fun s i => by simp only [Function.comp_apply, hi, he]⟩

/-- A fixed unary table may be evaluated on every register at once. -/
theorem unary (hf : packed F inp f m) (h : fits f) (t : ℕ → ℕ) :
    packed F inp (fun s i => t (f s i)) (m + 12) := by
  have he := ((const F inp (fun i : B w => t i.val) hf.width).lookup hf).mono
    (n := m + 12) (by omega)
  convert he using 1
  funext s i
  exact congrArg t (Nat.mod_eq_of_lt (h s i)).symm

theorem add (hf : packed F inp f m) (hg : packed F inp g n) :
    packed F inp (fun s i => f s i + g s i) (max m n + 7) := by
  obtain ⟨a, ha, he⟩ := hf
  obtain ⟨b, hb, hi⟩ := hg
  have h : Coloring.Cheap F 0 w (.pair (.addr w) (.addr w)) (.addr w) (fun x => x.1 + x.2) 4 :=
    ⟨_, numeric_add F w, by simp only [Format.width_pair, Format.width_addr]; ring_nf; omega⟩
  refine ⟨_, (((ha.pair hb).zip).comp (Coloring.Cheap.map _ (fun _ => h))).mono (by omega), ?_⟩
  intro s i
  change a (inp s) i + b (inp s) i = _
  rw [he, hi]
  exact Fin.ext (Nat.add_mod _ _ _).symm

theorem select {t u : Array S w} {a b : ℕ}
    (hf : packed F inp f m) (hg : packed F inp g n)
    (ht : packed F inp t a) (hu : packed F inp u b) (h : fits f) (k : fits g) :
    packed F inp (fun s i => if f s i < g s i then t s i else u s i)
      (max (max m n) (max a b) + 12) := by
  obtain ⟨x, hx, hx'⟩ := hf
  obtain ⟨y, hy, hy'⟩ := hg
  obtain ⟨z, hz, hz'⟩ := ht
  obtain ⟨v, hv, hv'⟩ := hu
  have cmp : Coloring.Cheap F 0 w (.pair (.addr w) (.addr w)) .bit (fun x => decide (x.1 < x.2)) 3 :=
    ⟨_, numeric_lt F w, by simp only [Format.width_pair, Format.width_addr]; rw [Format.width_bit]; ring_nf; omega⟩
  have bit := ((hx.pair hy).zip).comp (Coloring.Cheap.map _ (fun _ => cmp))
  have step := (((hz.pair hv).zip.pair bit).zip).comp (Coloring.Cheap.map _ (fun _ => cheap_select F w))
  refine ⟨_, step.mono (by omega), ?_⟩
  intro s i
  simp only [Function.comp_apply, hx', hy', hz', hv', decide_eq_true_eq]
  change (if f s i % 2 ^ w < g s i % 2 ^ w then _ else _) = _
  rw [Nat.mod_eq_of_lt (h s i), Nat.mod_eq_of_lt (k s i)]
  split <;> rfl

end packed
end OAI.LinearAlgebra.MatrixExponent.Processor.Vector
end

section
/-! # Routing lanes to one of two computations by a fixed partition -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring

variable {F S I J K : Type} [Field F] {w c : ℕ} {U : Coloring.Format} {inp : S → U.obj}

/-- Both stages may use every lane. Empty index sets need no dummy input. -/
theorem casesOn (hw : 1 ≤ w) (f : S → K → I ⊕ J → ℕ) (idx : B w → K) (arg : B w → I ⊕ J)
    (h₁ : ∀ a : B w → I, packed F inp (fun s j => f s (idx j) (.inl (a j))) c)
    (h₂ : ∀ a : B w → J, packed F inp (fun s j => f s (idx j) (.inr (a j))) c) :
    packed F inp (fun s j => f s (idx j) (arg j)) (c + 14) := by
  classical
  rcases isEmpty_or_nonempty I with he|hi
  · let k := Sum.elim (isEmptyElim : I → J) id
    have h (x : I ⊕ J) : Sum.inr (k x) = x := by cases x; exact isEmptyElim ‹I›; rfl
    simpa only [Function.comp_apply, h] using (h₂ (k ∘ arg)).mono (n := c + 14) (by omega)
  rcases isEmpty_or_nonempty J with he|hj
  · let k := Sum.elim id (isEmptyElim : J → I)
    have h (x : I ⊕ J) : Sum.inl (k x) = x := by cases x; rfl; exact isEmptyElim ‹J›
    simpa only [Function.comp_apply, h] using (h₁ (k ∘ arg)).mono (n := c + 14) (by omega)
  let l := Sum.elim id (fun _ : J => hi.some)
  let r := Sum.elim (fun _ : I => hj.some) id
  let mask := Sum.elim (fun _ : I => 0) (fun _ : J => 1)
  have a := h₁ (l ∘ arg)
  have b := h₂ (r ∘ arg)
  have m := const F inp (mask ∘ arg) a.width
  have n := const F inp (fun _ => 1) a.width
  have hp : 1 < 2 ^ w := Nat.one_lt_pow (by omega) (by decide)
  have hf := m.select n a b (fun _ j => by cases h : arg j <;> simp [mask, h, hp])
    (fun _ _ => hp)
  convert hf.mono (n := c + 14) (by omega) using 1
  funext s j
  cases h : arg j <;> simp [l, r, mask, h]

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-! # Indirect reads through fixed finite lookup tables -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring

variable {F S J : Type} [Field F] {w : ℕ} {U : Coloring.Format}
  {inp : S → U.obj} {c d : ℕ}

theorem reduce {f : Array S w} (h : packed F inp f c) :
    packed F inp (fun s i => f s i % 2 ^ w) c := by
  obtain ⟨t, ht, he⟩ := h
  exact ⟨t, ht, fun s i => (he s i).trans (Fin.ext (Nat.mod_mod _ _).symm)⟩

/-- A fixed indexing of the possible requests suffices. It is not
necessary to compute an inverse table from the input data. -/
theorem fetch [Nonempty J] (keys : S → B w → J) (idx : J ↪ B w) (f : S → J → ℕ)
    (hk : packed F inp (fun s i => (idx (keys s i)).val) c)
    (ht : ∀ key : B w → J, packed F inp (fun s i => f s (key i)) d) :
    packed F inp (fun s i => f s (keys s i)) (max d c + 10) := by
  classical
  let j := Function.invFun idx
  have hh := (ht j).lookup hk
  have he (s : S) (i : B w) : Fin.ofNat (2 ^ w) (idx (keys s i)).val = idx (keys s i) :=
    Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))
  have hi (k : J) : j (idx k) = k := Function.leftInverse_invFun idx.injective _
  simpa only [he, hi] using hh

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-! # Converting circuits on named bits into packed word arrays -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector
open Install Coloring

abbrev raw (I : Type) [Fintype I] : Coloring.Format := ⟨I → Bool, I, .refl _⟩

variable {F S I J : Type} [Field F] [Fintype I] [Fintype J] {w : ℕ}
  {inp : S → I → Bool} {f : Array S w} {m c : ℕ}

theorem packed.of_net (k : (I → Bool) → B w × slots (word w) → Bool)
    (hk : BNet F k m) (hc : Fintype.card I + 2 ^ w * w + m ≤ 2 ^ w * (100 + w) ^ c)
    (he : ∀ s j b, k (inp s) (j, b) = digits w (f s j) b) :
    packed (U := raw I) F inp f c := by
  refine ⟨(Perm w).code.symm ∘ k, ⟨m, ?_, ?_⟩, ?_⟩
  · simpa only [Circuit, Function.comp_def, Equiv.apply_symm_apply, raw, Equiv.refl_symm, Equiv.refl_apply] using hk
  · simpa [raw, Perm] using hc
  · intro s i
    change Control.decode w (fun t => k (inp s) (i, t)) = _
    simp only [he, digits, Equiv.apply_symm_apply]

theorem packed.reshape (k : (I → Bool) → J × slots (word w) → Bool) (idx : B w → J)
    (hk : BNet F k m) (hc : Fintype.card I + 4 * 2 ^ w * w + Fintype.card J * w + m ≤ 2 ^ w * (100 + w) ^ c)
    (he : ∀ s j b, k (inp s) (idx j, b) = digits w (f s j) b) :
    packed (U := raw I) F inp f c := by
  let e : B w × slots (word w) → J × slots (word w) := Prod.map idx id
  have h := hk.comp ((BNet.id F _).pull e)
  refine packed.of_net _ h ?_ he
  simp only [Fintype.card_prod, Fintype.card_fin, card_slots, wd_word]
  nlinarith only [hc]

theorem packed.unpack {U : Coloring.Format} {inp : S → U.obj}
    (h : packed F inp f c) (idx : J → B w) :
    ∃ k : (U.pins → Bool) → (J × slots (word w)) → Bool,
      BNet F k (2 ^ w * (100 + w) ^ c + 3 * Fintype.card J * w) ∧
      ∀ s j b, k (U.code (inp s)) (j, b) = digits w (f s (idx j)) b := by
  obtain ⟨g, ⟨m, hg, hm⟩, he⟩ := h
  let e : J × slots (word w) → B w × slots (word w) := Prod.map idx id
  have t := BNet.comp hg ((BNet.id F _).pull e)
  refine ⟨_, t.mono ?_, fun s j b => ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin, card_slots, wd_word, Perm, Format.width_vec,
      Format.width_addr] at hm ⊢
    nlinarith only [hm]
  · simp only [Function.comp_apply, id_eq, Equiv.symm_apply_apply]
    change (Control.decode w).symm (g (inp s) (idx j)) b = _
    rw [he]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector
end

section
/-! # Row sums of small square arrays of channel lengths -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector

open Coloring Install
variable {F S : Type} [Field F] {w R : ℕ} [NeZero R]

abbrev Pair (R : ℕ) := Fin R × Fin R

def index (w : ℕ) (p : Pair R) : B w := Fin.ofNat (2 ^ w) (p.1.val * R + p.2.val)

def atPair (R : ℕ) [NeZero R] (i : B w) : Pair R :=
  finProdFinEquiv.symm (Fin.ofNat (R * R) i.val)

theorem pair_index (hw : R ^ 2 ≤ 2 ^ w) (p : Pair R) : atPair R (index w p) = p := by
  apply finProdFinEquiv.injective
  simp only [atPair, Equiv.apply_symm_apply]
  apply Fin.ext
  have he : p.1.val * R + p.2.val = (finProdFinEquiv p).val := by
    change _ = p.2.val + R * p.1.val
    ring
  change (p.1.val * R + p.2.val) % 2 ^ w % (R * R) = _
  rw [he, Nat.mod_eq_of_lt ((finProdFinEquiv p).isLt.trans_le (by rwa [pow_two] at hw)),
    Nat.mod_eq_of_lt (finProdFinEquiv p).isLt]

def matrix (w : ℕ) (f : S → Fin R → Fin R → ℕ) : Array S w :=
  fun s i => f s (atPair R i).1 (atPair R i).2

theorem matrix_index (hw : R ^ 2 ≤ 2 ^ w) (f : S → Fin R → Fin R → ℕ) (s : S) (u v : Fin R) :
    matrix w f s (Fin.ofNat (2 ^ w) (u.val * R + v.val)) = f s u v := by
  change matrix w f s (index w (u, v)) = _
  rw [matrix, pair_index hw]

abbrev Cell (R w : ℕ) := Pair R × slots (word w)

private def decode (x : Cell R w → Bool) (p : Pair R) := (Control.decode w (fun k => x (p, k))).val

omit [NeZero R] in
private theorem decoded (F : Type) [Field F] (p : Pair R) :
    Register F w (fun x => decode (w := w) x p) (Fintype.card (Cell R w) + 3 * w) := by
  have hp := (BNet.id F (slots (word w))).pull (fun i => (p, i))
  unfold Register
  have he (x : Cell R w → Bool) : digits w (decode x p) = fun i => x (p, i) := by
    unfold digits decode
    rw [show Fin.ofNat (2 ^ w) (Control.decode w (fun k => x (p, k))).val =
      Control.decode w (fun k => x (p, k)) from Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))]
    exact (Control.decode w).symm_apply_apply _
  simp only [he]
  exact hp.mono (by unfold Cell; rw [card_slots, wd_word]; omega)

def prefixWords (x : Cell R w → Bool) (p : Pair R) :=
  ∑ j : Fin R, if j < p.2 then decode x (p.1, j) else 0

theorem prefixWords_net :
    BNet F (fun (x : Cell R w → Bool) (q : Cell R w) => digits w (prefixWords x q.1) q.2)
      (100000 * R ^ 5 * (w + 1)) := by
  let T := Fintype.card (Cell R w)
  have hj (p : Pair R) (j : Fin R) :
      Register F w (fun x : Cell R w → Bool => if j < p.2 then decode x (p.1, j) else 0)
        (T + 16 * w) := by
    by_cases h : j < p.2
    · simp only [ite_eq_left h]
      exact (decoded F _).mono (by omega)
    · simp only [ite_eq_right h]
      exact Register.const _
  have hp (p : Pair R) := Register.sum _ (hj p)
  apply (BNet.collect _ hp).mono
  have ht : Fintype.card (Cell R w) = R ^ 2 * w := by simp [Cell, Pair, pow_two]
  have hr : 1 ≤ R := NeZero.pos R
  have hR : R ^ 2 ≤ R ^ 5 := Nat.pow_le_pow_right hr (by decide)
  have h₁ : 1 ≤ R ^ 2 := Nat.one_le_pow _ _ hr
  have hh : w ≤ R ^ 2 * w := Nat.le_mul_of_pos_left _ h₁
  unfold T
  rw [ht, show Fintype.card (Pair R) = R ^ 2 by simp [Pair, pow_two], Fintype.card_fin]
  calc
    _ ≤ R ^ 5 * w + R ^ 2 * (2 * (R ^ 2 * w) + (2 * R) * (40000 * R ^ 2 * (w + 1))) := by
      gcongr
      · omega
      · nlinarith only [hh, h₁]
    _ ≤ _ := by
      have h : R ^ 4 * w ≤ R ^ 5 * w := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hr (by decide))
      nlinarith only [h, Nat.zero_le (R ^ 5 * w), Nat.zero_le (R ^ 5)]

omit [NeZero R] in
theorem prefixWords_eq (x : Cell R w → Bool) (g : Pair R → ℕ) (p : Pair R)
    (h : ∀ q k, x (q, k) = digits w (g q) k) (hb : ∀ q, g q < 2 ^ w) :
    prefixWords x p = ∑ j ∈ Finset.Iio p.2, g (p.1, j) := by
  unfold prefixWords decode
  simp only [h, digits, Equiv.apply_symm_apply, Fin.val_ofNat, Nat.mod_eq_of_lt (hb _)]
  rw [← Finset.sum_filter, show Finset.univ.filter (fun j : Fin R => j < p.2) = Finset.Iio p.2 by
    ext; simp]

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector
end

section
/-! # Loading bits into word lanes and checking simultaneous assertions -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed

open Install Coloring
variable {F S I : Type} [Field F] [Fintype I] {w c : ℕ}

private theorem slack (w c : ℕ) :
    2 * (2 ^ w * (100 + w) ^ c) + 35 * (2 ^ w * w) + 1 ≤ 2 ^ w * (100 + w) ^ (c + 2) := by
  let T := 2 ^ w * (100 + w) ^ c
  have hh : 2 ^ w ≤ T := Nat.le_mul_of_pos_right _ (by positivity)
  have ht : 0 < T := by unfold T; positivity
  rw [pow_add, ← mul_assoc (2 ^ w)]
  calc
    _ ≤ 2 * T + 35 * (T * w) + T := by gcongr; omega
    _ = T * (3 + 35 * w) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith)

theorem named (F : Type) [Field F] (inp : S → I → Bool) (idx : B w → I)
    (hi : Fintype.card I ≤ 2 ^ w * (100 + w) ^ c) :
    packed (U := raw I) F inp (fun s i => (inp s (idx i)).toNat) (c + 2) := by
  let k (x : I → Bool) (i : B w × slots (word w)) := digits w (x (idx i.1)).toNat i.2
  have hd : Depends k 1 := by
    intro i
    refine ⟨{idx i.1}, by simp, fun x y h => ?_⟩
    unfold k
    rw [h _ (Finset.mem_singleton_self _)]
  refine of_net k (hd.bnet F) ?_ (fun _ _ _ => rfl)
  simp only [Fintype.card_prod, Fintype.card_fin, card_slots, wd_word]
  rw [show localCost 1 = 34 by decide]
  have := slack w c
  omega

open Classical in
private theorem equal (z : I → Bool) :
    BNet F (fun x => fun _ : Unit => decide (x = z)) (10 * Fintype.card I + 1) := by
  let a := word (Fintype.card I)
  let e : I ≃ slots (word (Fintype.card I)) := Fintype.equivOfCardEq (by simp)
  let r := (bits a).trans (e.symm.arrowCongr (.refl Bool))
  apply BNet.of_layout (a := a) (b := .bit) e (.refl Unit)
  have h := Control.equal_net F a (r.symm z)
  change DNet F a .bit (fun x => decide (r x = z)) _
  simpa only [r.eq_symm_apply, a, wd_word] using h

theorem conjunction {inp : S → I → Bool} {f : Array S w} (hw : 1 ≤ w)
    (h : packed (U := raw I) F inp f c) (hfit : fits f) :
    ∃ b : (I → Bool) → Unit → Bool, BNet F b (2 ^ w * (100 + w) ^ (c + 2)) ∧
      ∀ s, b (inp s) () = decide (∀ i, f s i = 1) := by
  classical
  obtain ⟨k, hk, he⟩ := h.unpack id
  let z (i : B w × slots (word w)) := digits w 1 i.2
  have H := hk.comp (equal (F := F) z)
  refine ⟨_, H.mono ?_, fun s => ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin, card_slots, wd_word]
    rw [mul_assoc 3]
    have := slack w c
    omega
  · simp only [Function.comp_apply, decide_eq_decide]
    have hm : 1 < 2 ^ w := Nat.one_lt_pow (by omega) (by decide)
    change k (inp s) = z ↔ _
    have hv (i j) : k (inp s) (i, j) = digits w (f s i) j := he s i j
    constructor
    · intro h i
      have hd : digits w (f s i) = digits w 1 := funext fun j =>
        (hv i j).symm.trans (congrFun h (i, j))
      have := congrArg Fin.val ((Control.decode w).symm.injective hd)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt (hfit s i), Nat.mod_eq_of_lt hm] using this
    · intro h
      funext ⟨i, j⟩
      rw [hv, h]

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-!
# Static tables indexed by two smaller keys

A worker number and a local record number can jointly index a table
even when the record is used many times. The product of the two key
ranges must fit in the shared array.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring

variable {F S : Type} [Field F] {w m n : ℕ} {U : Coloring.Format}
  {inp : S → U.obj} {f g : Array S w} {c d : ℕ}

theorem binary (a : ℕ → ℕ → ℕ) (hw : m * n ≤ 2 ^ w)
    (hf : packed F inp f c) (hg : packed F inp g d)
    (hm : ∀ s i, f s i < m) (hn : ∀ s i, g s i < n) :
    packed F inp (fun s i => a (f s i) (g s i)) (max c d + 32) := by
  have hw' : fits f := fun s i => (hm s i).trans_le
    ((Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt (hn s i))).trans hw)
  have he : fits (fun s i => f s i * n + g s i) := by
    intro s i
    exact (Nat.add_lt_add_left (hn s i) _).trans_le
      (by rw [← Nat.succ_mul]; exact (Nat.mul_le_mul_right _ (hm s i)).trans hw)
  have ha := ((hf.unary hw' (·*n)).add hg).unary he (fun x => a (x / n) (x % n))
  convert ha.mono (n := max c d + 32) (by omega) using 1
  funext s i
  have hpos : 0 < n := Nat.zero_lt_of_lt (hn s i)
  rw [mul_comm (f s i), Nat.mul_add_div hpos, Nat.div_eq_of_lt (hn s i), add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt (hn s i)]

theorem named_table {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (a : A → B → ℕ) (ha : Fintype.card A * Fintype.card B ≤ 2 ^ w)
    (x : S → Coloring.B w → A) (y : S → Coloring.B w → B)
    (p : A ≃ Fin (Fintype.card A)) (q : B ≃ Fin (Fintype.card B))
    (hp : packed F inp (fun s i => (p (x s i)).val) c)
    (hq : packed F inp (fun s i => (q (y s i)).val) d) :
    packed F inp (fun s i => a (x s i) (y s i)) (max c d + 32) := by
  let _ : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  let _ : NeZero (Fintype.card B) := ⟨Fintype.card_ne_zero⟩
  have h := binary (fun u v => a (p.symm (Fin.ofNat _ u)) (q.symm (Fin.ofNat _ v)))
    ha hp hq (fun _ _ => Fin.isLt _) (fun _ _ => Fin.isLt _)
  have he {m : ℕ} [NeZero m] (i : Fin m) : Fin.ofNat m i.val = i :=
    Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [he, Equiv.symm_apply_apply] using h

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-! # Changing the input and the lane indexing of a packed computation -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring
variable {F S T I J : Type} [Field F] [Fintype I] [Fintype J] {w c : ℕ}
  {inp : S → I → Bool} {f : Array S w}

theorem lift (h : packed (U := raw I) F inp f c)
    (inp' : T → J → Bool) (k : T → S) (p : I → J) (hi : Fintype.card J ≤ 2 ^ w)
    (he : ∀ t, inp' t ∘ p = inp (k t)) :
    packed (U := raw J) F inp' (fun t => f (k t)) (c + 2) := by
  have hw : (raw J).width ≤ 2 ^ w * (100 + w) ^ c :=
    hi.trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hp := Cheap.project F (f := fun (x : (raw J).obj) => (x ∘ p : (raw I).obj))
    hw h.width p (fun _ _ => rfl)
  obtain ⟨a, ha, hf⟩ := h
  refine ⟨_, (hp.comp ha).mono (by omega), ?_⟩
  intro t i
  change a (inp' t ∘ p) i = _
  rw [he]
  exact hf _ _

/-- Renumber a packed domain by any static function. -/
theorem remap {D : Type} {U : Coloring.Format} {inp : S → U.obj}
    (a : S → B w → D) (idx : D ↪ B w) (ha : packed F inp (fun s j => (idx (a s j)).val) c)
    (fn : D → ℕ) : packed F inp (fun s j => fn (a s j)) (c + 12) := by
  classical
  let g (k : ℕ) := Function.extend idx fn (fun _ => 0) (Fin.ofNat (2 ^ w) k)
  have h := ha.unary (fun _ _ => Fin.isLt _) g
  have he (s : S) (j : B w) : g (idx (a s j)).val = fn (a s j) := by
    unfold g
    rw [show Fin.ofNat (2 ^ w) (idx (a s j)).val = idx (a s j) from
      Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))]
    exact idx.injective.extend_apply _ _ _
  simpa only [he] using h

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-! # Returning named Boolean results from a packed calculation -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring Install
variable {F S I J : Type} [Field F] [Fintype I] [Fintype J] {w c : ℕ}
  {inp : S → I → Bool}

private theorem read_flag (hw : 1 ≤ w) :
    ∃ (k : slots (word w)) (t : Bool → Bool), ∀ b : Bool, t (digits w b.toNat k) = b := by
  have hz : 1 < 2 ^ w := Nat.one_lt_pow (by omega) (by decide)
  have hn : digits w 0 ≠ digits w 1 := by
    intro he
    have := congrArg Fin.val ((Control.decode w).symm.injective he)
    simp only [Fin.val_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt hz] at this
    omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  exact ⟨i, fun a => decide (a = digits w 1 i), by rintro (_|_) <;> simp [hi]⟩

/-- If the register in each lane represents a bit, any fixed naming
of the requested bits can be used for the output of the circuit. -/
theorem output (hw : 1 ≤ w) (hi : Fintype.card I ≤ 2 ^ w) (hj : Fintype.card J ≤ 2 ^ w)
    (f : S → J → Bool)
    (hf : ∀ ix : B w → J, packed (U := raw I) F inp (fun s j => (f s (ix j)).toNat) c) :
    ∃ t, BNet F t (2 ^ w * (100 + w) ^ (c + 2)) ∧ ∀ s, t (inp s) = f s := by
  classical
  have hsize : 2 ^ w * (100 + w) ^ c + 4 * Fintype.card J * w + 34 * Fintype.card J ≤ 2 ^ w * (100 + w) ^ (c + 2) := by
    have hc : 1 ≤ (100 + w) ^ c := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ 2 ^ w * (100 + w) ^ c + 4 * 2 ^ w * w + 34 * 2 ^ w := by gcongr
      _ = 2 ^ w * ((100 + w) ^ c + (4 * w + 34)) := by ring
      _ ≤ 2 ^ w * ((100 + w) ^ c * (1 + (4 * w + 34))) := by
        rw [mul_add ((100 + w) ^ c), mul_one]
        gcongr
        exact Nat.le_mul_of_pos_left _ hc
      _ ≤ _ := by rw [pow_add]; gcongr; nlinarith
  cases isEmpty_or_nonempty J
  · have hd : Depends (fun (_ : I → Bool) (_ : J) => false) 0 :=
      fun _ => ⟨∅, by simp, fun _ _ _ => rfl⟩
    refine ⟨_, (hd.bnet F).mono ?_, fun _ => Subsingleton.elim _ _⟩
    simpa only [Fintype.card_eq_zero, mul_zero, add_zero] using
      hi.trans (Nat.le_mul_of_pos_right _ (by positivity : 0 < (100 + w) ^ (c + 2)))
  · obtain ⟨idx⟩ : Nonempty (J ↪ B w) := Function.Embedding.nonempty_of_card_le (by simpa using hj)
    obtain ⟨k, t, he⟩ := read_flag hw
    obtain ⟨g, hg, hg'⟩ := (hf (Function.invFun idx)).unpack idx
    let a (x : J × slots (word w) → Bool) (j : J) := t (x (j, k))
    have ha : Depends a 1 := fun j => ⟨{(j, k)}, by simp, fun x y h => congrArg t (h _ (by simp))⟩
    refine ⟨_, (hg.comp (ha.bnet F)).mono ?_, fun s => funext fun j => ?_⟩
    · rw [Fintype.card_prod, card_slots, wd_word]
      rw [show localCost 1 = 34 by decide]
      exact le_trans (le_of_eq (by ring)) hsize
    · have h := hg' s j k
      rw [Function.leftInverse_invFun idx.injective j] at h
      exact (congrArg t h).trans (he _)

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end
