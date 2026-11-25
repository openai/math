import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import OAI.LinearAlgebra.MatrixExponent.Diagram.Pad
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortOne
import OAI.LinearAlgebra.MatrixExponent.Batcher
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Rounds.Bins
import OAI.LinearAlgebra.MatrixExponent.Tagged.Hard
import OAI.LinearAlgebra.MatrixExponent.Lookup.Scan
import OAI.LinearAlgebra.MatrixExponent.Lookup.Single
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import Mathlib.Algebra.BigOperators.Fin
import OAI.LinearAlgebra.MatrixExponent.Packing.Beat
import OAI.LinearAlgebra.MatrixExponent.Packing.Budget
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement

/-!
# Compact initial stacks

Use one product table at each original station in each block. Keep all
old wires, including loops, and expose the copies in the original order.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
open Finset Packing Transcript
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} {h u n : ℕ}

abbrev tensor (B : Table F) (u : ℕ) : Table F :=
  ⟨copies B.1 u, copies B.2.1 u, fun x y => ∏ i : Fin u,
    B.2.2 ((bits B.1).symm (fun k => bits (copies B.1 u) x ((Diagonal.port B.1 u).symm (i, k))))
      ((bits B.2.1).symm (fun k => bits (copies B.2.1 u) y ((Diagonal.port B.2.1 u).symm (i, k))))⟩

def pin (B : Table F) (u : ℕ) : Ports (tensor B u) ≃ Fin u × Ports B :=
  ((Diagonal.port B.1 u).sumCongr (Diagonal.port B.2.1 u)).trans
    (Equiv.prodSumDistrib _ _ _).symm

theorem sample_tensor (B : Table F) (u : ℕ) (z : Ports (tensor B u) → Bool) :
    sample (tensor B u) z = ∏ i : Fin u, sample B (fun p => z ((pin B u).symm (i, p))) := by
  unfold sample tensor
  simp only [Equiv.apply_symm_apply]
  rfl

variable (G : Diagram F a b) (c : Cell h × Fin u ≃ Fin n)

private def unpack (W : G.V → Wire) :
    (Σ v : Cell h × G.V, slots (copies (W v.2) u)) ≃
      (Σ v : (Cell h × Fin u) × G.V, slots (W v.2)) where
  toFun q :=
    let p := Diagonal.port (W q.1.2) u q.2
    ⟨((q.1.1, p.1), q.1.2), p.2⟩
  invFun q := ⟨(q.1.1.1, q.1.2), (Diagonal.port (W q.1.2) u).symm (q.1.1.2, q.2)⟩
  left_inv q := by simp
  right_inv q := by obtain ⟨⟨⟨i, t⟩, v⟩, k⟩ := q; simp

abbrev gathered : Diagram F (copies a n) (copies b n) where
  V := Cell h × G.V
  E := (G.replicate c).E
  table v := tensor (G.table v.2) u
  src := (unpack G (fun v => (G.table v).1)).trans (G.replicate c).src
  dst := (unpack G (fun v => (G.table v).2.1)).trans (G.replicate c).dst

private theorem gather_src (i : Cell h) (t : Fin u) (v : G.V) (p : slots (G.table v).1) :
    (gathered G c).src ⟨(i, v), (Diagonal.port (G.table v).1 u).symm (t, p)⟩ =
      (G.replicate c).src ⟨((i, t), v), p⟩ := by simp [gathered, unpack, Equiv.trans_apply]

private theorem gather_dst (i : Cell h) (t : Fin u) (v : G.V) (p : slots (G.table v).2.1) :
    (gathered G c).dst ⟨(i, v), (Diagonal.port (G.table v).2.1 u).symm (t, p)⟩ =
      (G.replicate c).dst ⟨((i, t), v), p⟩ := by simp [gathered, unpack, Equiv.trans_apply]

private theorem vertex_gathered (x : Val (copies a n)) (y : Val (copies b n))
    (z : (G.replicate c).E → Bool) (i : Cell h) (v : G.V) :
    (gathered G c).vertex x y z (i, v) = ∏ t, (G.replicate c).vertex x y z ((i, t), v) := by
  unfold Diagram.vertex
  dsimp only [gathered, tensor]
  simp only [Equiv.apply_symm_apply]
  refine prod_congr rfl fun t _ => ?_
  apply congrArg₂ (G.table v).2.2 <;> apply congrArg <;> funext p
  · exact congrArg _ (gather_src G c i t v p)
  · exact congrArg _ (gather_dst G c i t v p)

theorem eval_gathered : (gathered G c).eval = (G.replicate c).eval := by
  funext x y
  unfold Diagram.eval
  refine sum_congr rfl fun z _ => ?_
  simp only [Fintype.prod_prod_type, vertex_gathered]
  exact prod_congr rfl fun _ _ => prod_comm

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end

section
/-!
# Sorting services for the diagonal descent

Large sorting tables are permitted only if their entries themselves
have efficient trivalent realizations. Column sorting lifts both kinds
of network while charging each layer for every constituent short sort.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

variable (F : Type) [Field F]

def Fast (a : Wire) [L : LinearOrder (Val a)] : Prop :=
  DNet F (.pair a a) .bit (fun x => decide (x.1 < x.2)) (10000 * (wd a + 1))

theorem select_net (a : Wire) :
    DNet F (.pair (.pair a a) .bit) a (fun x => if x.2 then x.1.1 else x.1.2) (10 * wd a + 2) := by
  obtain ⟨f, hf, _⟩ := Rewire.exists_of_width (a := a) (b := word (wd a)) (wd_word _).symm
  obtain ⟨g, hg, he⟩ := hf.inverse
  have k := ((selectWord F (wd a)).pre ((hf.par hf).par (.id _))).post hg
  convert k using 1
  funext ⟨⟨x, y⟩, b⟩
  cases b <;> exact (he _ _).mp rfl

variable (a : Wire) [LinearOrder (Val a)]

theorem Fast.exchange (h : Fast F a) :
    DNet F (.pair a a) (.pair a a) (fun x => (min x.1 x.2, max x.1 x.2)) (11000 * (wd a + 1)) := by
  have lo := select_net F a
  have hi := lo.pre ((Rewire.swap a a).par (.id .bit))
  have k := ((DNet.id F (.pair a a)).pair h).comp (lo.pair hi)
  convert k.mono (n := 11000 * (wd a + 1)) (by simp only [wd]; omega) using 1
  funext ⟨x, y⟩
  by_cases hh : x < y
  · simp [hh, min_eq_left hh.le, max_eq_right hh.le]
  · simp [hh, min_eq_right (le_of_not_gt hh), max_eq_left (le_of_not_gt hh)]

def sorter (j : ℕ) : Table F :=
  ⟨tree j a, tree j a, fun x y => if sortTree j x = y then 1 else 0⟩

@[simp] theorem arity_sorter (j : ℕ) : Processor.arity (sorter F a j) = 2 * 2 ^ j * wd a := by
  simp [Processor.arity, sorter, wd_tree]
  ring

theorem sort_cheap (hf : Fast F a) (j : ℕ) (hb : 1 ≤ wd a) :
    sorter F a j ∈ Processor.Cheap F 50000 2 := by
  obtain ⟨m, hm, h⟩ := sortTree_net (Fast.exchange F a hf) j
  refine ⟨m, ?_, h⟩
  simp only [arity_sorter]
  have hj : j ≤ Nat.clog 2 (1 + 2 * 2 ^ j * wd a) := by
    calc
      _ = Nat.clog 2 (2 ^ j) := (Nat.clog_pow 2 j (by decide)).symm
      _ ≤ _ := Nat.clog_mono_right 2 (by have := Nat.le_mul_of_pos_right (2 * 2 ^ j) hb; omega)
  calc
    _ ≤ 2 ^ j * (j + 1) ^ 2 * (50000 * wd a) := hm.trans (by gcongr; omega)
    _ = (2 ^ j * wd a) * 50000 * (1 + j) ^ 2 := by ring
    _ ≤ _ := by gcongr; nlinarith [Nat.zero_le (2 ^ j)]

/-- Lift cheap sorting gates of short length to a whole long sort. -/
theorem sort_wide (hf : Fast F a) (j l D k : ℕ) (hb : 1 ≤ wd a) (hj : 2 ≤ j)
    (harity : 2 * 2 ^ j * wd a ≤ D) (hl : 2 ^ k * (j + l - 2) ≤ 3 ^ k * (j - 2)) :
    DWide F D (Processor.Cheap F 50000 2) (tree (j + l) a) (tree (j + l) a)
      (sortTree (j + l)) (4 ^ k * (2 ^ l * (1 + 2 * 2 ^ j * wd a))) := by
  have h : DWide F D (Processor.Cheap F 50000 2) (tree j a) (tree j a)
      (sortTree j) (1 + 2 * 2 ^ j * wd a) := by
    have ha := arity_sorter F a j
    change wd (tree j a) + wd (tree j a) = _ at ha
    rw [← ha]
    exact ⟨_, le_rfl, Wide.table _ _ _ (ha.trans_le harity) (.inr (sort_cheap F a hf j hb))⟩
  exact (DWide.columnModel F D (Processor.Cheap F 50000 2)).sort_lift_iterate hj k hl (h.many (2 ^ l))

theorem sort_trivalent (hf : Fast F a) (w l m k : ℕ) (hw : 2 ≤ w) (hb : wd a ≤ 4 * w)
    (tag : Net F (Tagged.inputs w (word w)) .unit (Tagged.tag F w (word w)) m)
    (hl : 2 ^ k * (w + l - 2) ≤ 3 ^ k * (w - 2)) :
    DNet F (tree (w + l) a) (tree (w + l) a)
      (sortTree (w + l)) (4 ^ k * (2 ^ l * (4 * m + 10000 * 2 ^ w * (w + 10000 * (wd a + 1) + 1)))) := by
  have h := Tagged.sort_one tag hb hf
  let n := 4 * m + 10000 * 2 ^ w * (w + 10000 * (wd a + 1) + 1)
  have many (t : ℕ) : DNet F (copies (tree w a) t) (copies (tree w a) t)
      (mapCopies (sortTree w) t) (t * n) := by
    induction t with
    | zero => exact ⟨0, Nat.zero_le _, Net.empty⟩
    | succ t ih => rw [Nat.succ_mul, Nat.add_comm (t * n)]; exact h.par ih
  exact Columns.sort_lift_iterate hw k hl (many (2 ^ l))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# A trivalent network with its exterior bits held fixed

Use two host positions per original station. One holds all copies
in the current block, the other holds their exterior ends. The
frozen charge is exactly the number of exterior bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
open Classical Finset Packing Rounds.Stack

variable {F : Type} {a b : Wire} (G : Diagram F a b)

private theorem other_other (e : G.End) : other G (other G e) = e := by
  rcases e with (i|e)|(i|e) <;> rfl

def near (v : G.V) : Finset G.V :=
  insert v ((univ.filter (fun e => G.station e = v)).image (fun e => G.station (other G e)))

theorem near_symm (v w : G.V) (h : w ∈ near G v) : v ∈ near G w := by
  simp only [near, mem_insert, mem_image, mem_filter, mem_univ, true_and] at h ⊢
  rcases h with rfl|⟨e, hv, hw⟩
  · exact .inl rfl
  · exact .inr ⟨other G e, hw, by rw [other_other, hv]⟩

theorem card_near (v : G.V) : (near G v).card ≤ G.arity v + 1 := by
  rw [← G.degree, Fintype.card_subtype]
  exact (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le _)

theorem target_mem (e : G.E) : G.target e ∈ near G (G.source e) :=
  mem_insert_of_mem (mem_image.mpr ⟨.inl (.inr e), mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩)

def adjacent (v : G.V × Bool) := (near G v.1) ×ˢ (univ : Finset Bool)

theorem adj_symm (v w) (h : w ∈ adjacent G v) : v ∈ adjacent G w :=
  mem_product.mpr ⟨near_symm G _ _ (mem_product.mp h).1, mem_univ _⟩

theorem adj_size (ht : G.Trivalent) (v) : (adjacent G v).card ≤ 8 := by
  rw [adjacent, card_product, card_univ, Fintype.card_bool]
  exact Nat.mul_le_mul_right 2 ((card_near G v.1).trans (Nat.add_le_add_right (ht v.1) 1))

abbrev Outer (a b : Wire) := slots a ⊕ slots b

def fringe (a b : Wire) : Fringe a b (Outer a b) where
  tensor := id
  charge _ := 1
  cover t := by simp
  scale := 1
  pos := zero_lt_one
  le := le_rfl

theorem fringe_total (a b : Wire) : (fringe a b).Z = wd a + wd b := by
  simp [Fringe.Z, Fringe.reserve, fringe, Outer]

variable [Field F] {h n u : ℕ} (c : Cell h × Fin u ≃ Fin n)

def locate (s : Bool) (v : (gathered G c).V) : (G.V × Bool) × Cell h := ((v.2, s), v.1)

def groups : HostNet F (fringe (copies a n) (copies b n)) h u where
  diagram := gathered G c
  V := G.V × Bool
  E := G.E × Cell h
  src e := (G.source e.1, false)
  dst e := (G.target e.1, false)
  ix := Prod.snd
  units := {
    place := locate G c false
    bits := (Equiv.prodComm _ _).trans (Equiv.prodAssoc _ _ _).symm
    left := fun ⟨_, _⟩ => rfl
    right := fun ⟨_, _⟩ => rfl }
  park := locate G c true ∘ portEnd (gathered G c)
  frozen p := p.2 = true
  N := adjacent G
  C := adjacent G
  ns := adj_symm G
  cs := adj_symm G
  sub _ := Subset.rfl
  kept _ := rfl
  core _ := ⟨Bool.false_ne_true, Bool.false_ne_true⟩
  edge e := mem_product.mpr ⟨target_mem G e.1, mem_univ _⟩
  tether _ := ⟨Bool.false_ne_true, rfl, mem_product.mpr ⟨mem_insert_self _ _, mem_univ _⟩⟩

private theorem arity_sum (ht : G.Trivalent) (s : Bool) (v : (G.V × Bool) × Cell h) :
    push (locate G c s) (fun i => ((gathered G c).arity i : ℝ)) v ≤
      if s = v.1.2 then 3 * u else 0 := by
  have bound (i : (gathered G c).V) : ((gathered G c).arity i : ℝ) ≤ 3 * u := by
    have he : (gathered G c).arity i = u * G.arity i.2 := by
      simp only [Diagram.arity, wd_copies, mul_add]
    rw [he, Nat.cast_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (ht i.2)) (Nat.cast_nonneg _)
  refine (push_le_push _ bound v).trans ?_
  unfold push
  change (∑ i : Cell h × G.V, @ite ℝ (((i.2, s), i.1) = v) (propDecidable _) (3 * u) 0) ≤ _
  obtain ⟨⟨z, r⟩, i⟩ := v
  simp only [Fintype.sum_prod_type, Prod.mk.injEq]
  by_cases eq : s = r <;> simp [eq, ite_and]

theorem bounded (ht : G.Trivalent) : (groups G c).Bounded 8 8 (3 * u) := by
  refine ⟨adj_size G ht, adj_size G ht, fun v i => ?_⟩
  rw [(groups G c).load_eq (v, i)]
  simp only [show (groups G c).past (v, i) = 0 from rfl, Nat.cast_zero, mul_zero, add_zero]
  change push (locate G c false) _ (v, i) +
    1 * push (locate G c true ∘ portEnd (gathered G c)) (fun _ => 1) (v, i) ≤ _
  rw [one_mul, ← port_load]
  have h₁ := arity_sum G c ht false (v, i)
  have h₂ := arity_sum G c ht true (v, i)
  rw [site_arity] at h₂
  refine (add_le_add h₁ ((le_add_of_nonneg_right (Nat.cast_nonneg _)).trans h₂)).trans_eq ?_
  cases v.2 <;> simp

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end

section
/-!
# Sorting on the exceptional length sequence

One version uses trivalent tables and pays for the exceptional tag
verifier. The other uses cheap sorting tables of bounded arity and has
a constant cost per bit. All exponents below refer to bit lengths.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Filter

variable {F : Type} [Field F]

/-- One cost measured in two models at the same length. -/
def Service (F : Type) [Field F] (w : ℕ) (C : ℝ) (a b : Wire)
    (k : Val a → Val b → F) (budget : ℕ) : Prop :=
  (∃ v, Net F a b k v ∧ (v : ℝ) ≤ C * budget) ∧
    ∃ s ≤ budget, Wide F (2 ^ (w / 2)) (Processor.Cheap F 50000 2) a b k s

theorem arity_cap (w : ℕ) : (2 ^ (w / 2)) ^ 2 ≤ 2 ^ w := by
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  omega

private theorem row_cap {w : ℕ} (hw : 64 ≤ w) : 8 * w ≤ 2 ^ (w / 4) := by
  have aux (n : ℕ) (hn : 16 ≤ n) : 32 * (n + 1) ≤ 2 ^ n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ k _ ih => rw [pow_succ]; omega
  have := aux (w / 4) (by omega)
  omega

theorem cheap_arity {w b : ℕ} (hw : 64 ≤ w) (hb : b ≤ 4 * w) :
    2 * 2 ^ (w / 4) * b ≤ 2 ^ (w / 2) := by
  calc
    _ ≤ 2 ^ (w / 4) * (8 * w) := by
      rw [show 2 * 2 ^ (w / 4) * b = 2 ^ (w / 4) * (2 * b) by ring]
      exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ 2 ^ (w / 4) * 2 ^ (w / 4) := Nat.mul_le_mul_left _ (row_cap hw)
    _ ≤ _ := by rw [← pow_add]; apply Nat.pow_le_pow_right (by decide); omega

/-- Four to the sixth is an upper bound on the number of layers for
height ratios up to eight. -/
theorem sort_service {a : Wire} [LinearOrder (Val a)] (hf : Fast F a) {w j m : ℕ} {C : ℝ} (hw : 64 ≤ w) (hj : w ≤ j) (hj' : j ≤ 2 * w)
    (hb : 1 ≤ wd a) (hb' : wd a ≤ 4 * w) (hC : 1 ≤ C)
    (tag : Net F (Tagged.inputs w (word w)) .unit (Tagged.tag F w (word w)) m)
    (hc : (m : ℝ) ≤ C * (2 : ℝ) ^ w * w) :
    Service F w C (tree j a) (tree j a) (sorter F a j).2.2 (10 ^ 12 * 2 ^ j * w) := by
  have hp (k : ℕ) (hk : k ≤ j) : 2 ^ (j - k) * 2 ^ k = (2 ^ j : ℕ) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  constructor
  · have ht := sort_trivalent F a hf w (j - w) m 2 (by omega) hb' tag (by omega)
    rw [Nat.add_sub_of_le hj] at ht
    obtain ⟨v, hv, hv'⟩ := ht
    refine ⟨v, hv', ?_⟩
    have hp' : (2 : ℝ) ^ (j - w) * 2 ^ w = 2 ^ j := by exact_mod_cast hp w hj
    have hs : (w + 10000 * (wd a + 1) + 1 : ℕ) ≤ C * (50000 * (w : ℝ)) := by
      have : w + 10000 * (wd a + 1) + 1 ≤ 50000 * w := by omega
      exact (show (w + 10000 * (wd a + 1) + 1 : ℕ) ≤ 50000 * (w : ℝ) by exact_mod_cast this).trans
        (le_mul_of_one_le_left (by positivity) hC)
    calc
      _ ≤ (4 : ℝ) ^ 2 * (2 ^ (j - w) * (4 * m + 10000 * 2 ^ w * (w + 10000 * (wd a + 1) + 1 : ℕ))) := by exact_mod_cast hv
      _ ≤ 4 ^ 2 * (2 ^ (j - w) * (4 * (C * 2 ^ w * w) + 10000 * 2 ^ w * (C * (50000 * w)))) := by gcongr
      _ = C * (8000000064 * 2 ^ j * w) := by rw [← hp']; ring
      _ ≤ _ := by push_cast; gcongr; norm_num
  · have hle : w / 4 ≤ j := by omega
    have ht := sort_wide F a hf (w / 4) (j - w / 4) (2 ^ (w / 2)) 6 hb (by omega)
      (cheap_arity hw hb') (by omega)
    rw [Nat.add_sub_of_le hle] at ht
    obtain ⟨v, hv, hv'⟩ := ht
    refine ⟨v, hv.trans ?_, hv'⟩
    have hs : 1 + 2 * 2 ^ (w / 4) * wd a ≤ 9 * 2 ^ (w / 4) * w := by
      have : 0 < 2 ^ (w / 4) := by positivity
      nlinarith
    calc
      _ ≤ 4 ^ 6 * (2 ^ (j - w / 4) * (9 * 2 ^ (w / 4) * w)) := by gcongr
      _ = (4 ^ 6 * 9) * 2 ^ j * w := by rw [← hp _ hle]; ring
      _ ≤ _ := by gcongr; norm_num

theorem frequent_tags (bad : ¬ Tagged.Hard F) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ w : ℕ in atTop, ∃ m, Net F (Tagged.inputs w (word w)) .unit (Tagged.tag F w (word w)) m ∧
      (m : ℝ) ≤ (w : ℝ) ^ ε * (2 : ℝ) ^ w * w := by
  by_contra! h
  refine bad ⟨ε, hε, ?_⟩
  filter_upwards [h] with w hw m hm
  simpa only [mul_comm, mul_left_comm, mul_assoc] using (hw m hm).le

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-! # Substituting short or high-arity sorts on the same graph -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Finset

variable {F : Type} [Field F] {a b : Wire} {w : ℕ} {C : ℝ}

theorem Service.mono {k : Val a → Val b → F} {m n : ℕ}
    (h : Service F w C a b k m) (hmn : m ≤ n) (hc : 0 ≤ C) : Service F w C a b k n := by
  obtain ⟨⟨v, hv, hcost⟩, s, hs, hw⟩ := h
  exact ⟨⟨v, hv, hcost.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmn) hc)⟩, s, hs.trans hmn, hw⟩

def SortTables (F : Type) [Field F] (w : ℕ) : Set (Table F) :=
  {T | ∃ (j : ℕ) (a : Wire) (_ : LinearOrder (Val a)), Fast F a ∧
    w ≤ j ∧ j ≤ 2 * w ∧ w ≤ wd a ∧ wd a ≤ 4 * w ∧ T = sorter F a j}

/-- Short tables have a pointwise trivalent simulation. Long sorts
use a tag verifier at an exceptional height. -/
def Allowed (F : Type) [Field F] (w : ℕ) : Set (Table F) :=
  SortTables F w ∪ {T | T ∈ Processor.Cheap F 50000 2 ∧
    Processor.arity T ≤ 2 ^ ((Nat.clog 2 w) ^ 3) ∧ Processor.arity T ≤ 2 ^ (w / 2)}

theorem sort_allowed : SortTables F w ⊆ Allowed F w := fun _ h => Or.inl h

theorem service_of_diagram (G : Diagram F a b) (cost : G.V → ℕ)
    (h : ∀ v, Service F w C (G.table v).1 (G.table v).2.1 (G.table v).2.2 (cost v)) :
    Service F w C a b G.eval (∑ v, cost v) := by
  classical
  constructor
  · choose v hv hcost using fun i => (h i).1
    refine ⟨∑ i, v i, Diagram.realize (Net F) Net.empty Net.par Net.pre Net.post Net.trace G v hv, ?_⟩
    simp only [Nat.cast_sum, mul_sum]
    exact sum_le_sum fun i _ => hcost i
  · choose s hs hw using fun i => (h i).2
    exact ⟨∑ i, s i, sum_le_sum (fun i _ => hs i),
      Diagram.realize _ Wide.empty Wide.par Wide.pre Wide.post Wide.trace G s hw⟩

/-- The one-time length overhead is avoided by padding full sorting
vertices to at least `2^w` records of at least `w` bits. -/
theorem expand {u v m : ℕ} {k : Val a → Val b → F} (hw : 64 ≤ w) (hC : 1 ≤ C)
    (tag : Net F (Tagged.inputs w (word w)) .unit (Tagged.tag F w (word w)) m)
    (hc : (m : ℝ) ≤ C * (2 : ℝ) ^ w * w)
    (hl : ((2 + (Nat.clog 2 w) ^ 3) ^ 2 : ℕ) ≤ C)
    (h : Wide F u (Allowed F w) a b k v) : Service F w C a b k (10 ^ 12 * v) := by
  have table (T : Table F) (ht : Processor.arity T ≤ 3 ∨ T ∈ Allowed F w) :
      Service F w C T.1 T.2.1 T.2.2 (10 ^ 12 * (1 + Processor.arity T)) := by
    rcases ht with ht | ⟨j, b, _, hf, hj, hj', hb, hb', rfl⟩ | ⟨hcheap, hsmall, hD⟩
    · have hk := Net.table (F := F) T.1 T.2.1 T.2.2 ht
      have hu : 3 ≤ 2 ^ (w / 2) := by
        have := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ w / 2 by omega)
        omega
      obtain ⟨s, hs, h⟩ := hk.includeWide (L := Processor.Cheap F 50000 2) hu
      have h' : Service F w C T.1 T.2.1 T.2.2 4 := ⟨⟨1, hk, by norm_num; linarith⟩, s, hs, h⟩
      exact h'.mono (by omega) (by linarith)
    · refine (sort_service hf hw hj hj' (by omega) hb' hC tag hc).mono ?_ (by linarith)
      rw [arity_sorter, mul_assoc (10 ^ 12)]
      apply Nat.mul_le_mul_left
      have := Nat.mul_le_mul_left (2 ^ j) hb
      rw [mul_assoc 2]
      omega
    · let n := Processor.arity T
      have hlog : Nat.clog 2 (1 + n) ≤ (Nat.clog 2 w) ^ 3 + 1 := by
        apply (Nat.clog_le_iff_le_pow (by decide)).mpr
        rw [pow_succ]
        have := Nat.two_pow_pos ((Nat.clog 2 w) ^ 3)
        omega
      obtain ⟨v, hv, hnet⟩ := show T ∈ Processor.Cheap F 50000 2 from hcheap
      refine ⟨⟨v, hnet, ?_⟩, 1 + n, by omega, Wide.table _ _ _ hD (.inr hcheap)⟩
      have hv' : v ≤ 10 ^ 12 * (1 + n) * ((2 + (Nat.clog 2 w) ^ 3) ^ 2) := calc
        _ ≤ (1 + n) * 50000 * (1 + Nat.clog 2 (1 + n)) ^ 2 := hv
        _ ≤ _ := by
          rw [mul_comm (1 + n) 50000]
          apply Nat.mul_le_mul
          · exact Nat.mul_le_mul_right _ (by norm_num)
          · exact Nat.pow_le_pow_left (by omega) 2
      rw [mul_comm C]
      exact (Nat.cast_le.mpr hv').trans (by rw [Nat.cast_mul]; gcongr)
  obtain ⟨G, he, had, hs⟩ := h.diagram
  have hv := service_of_diagram G (fun i => 10 ^ 12 * (1 + G.arity i)) (fun i => table _ (had i).2)
  rw [he, ← mul_sum] at hv
  rw [← hs]
  exact hv

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-!
# Fixed-length simultaneous dictionary lookup

A length cap on the address permits all table values, even zero. The
only additional gate is one sorting relation in the permitted range.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Lookup

variable {F : Type} [Field F] {w u : ℕ}

theorem lookup (a : Wire) (f : Val a → F) (hbig : w ≤ wd a)
    (hsmall : wd a + 1 ≤ 2 * w)
    (harity : 2 * 2 ^ (wd a + 1) * (2 * wd a + 2) ≤ u) (hu : 3 ≤ u) :
    ∃ s ≤ 10000 * 2 ^ (wd a) * (1 + wd a),
      Wide F u (SortTables F w) (tree (wd a) a) .unit
        (fun x _ => ((flatten (wd a) x).map f).prod) s := by
  let t := wd a
  let L := SortTables F w
  let _ := keyOrder a
  let _ := rowOrder a
  obtain ⟨z, hn, hall, he⟩ := sort_dict a (row_query a) (row_key a)
  have hr : wd (row a) = 2 * t + 2 := by simp [wd, t]; omega
  have cmp : Fast F (row a) := (row_compare F a).mono (by rw [hr]; omega)
  have hd : Processor.arity (sorter F (row a) (t + 1)) = 2 * 2 ^ (t + 1) * (2 * t + 2) := by
    rw [arity_sorter, hr]
  have ok : sorter F (row a) (t + 1) ∈ L :=
    ⟨t + 1, row a, inferInstance, cmp, by omega, hsmall, by omega, by omega, rfl⟩
  have hs : DWide F u L (tree (t + 1) (row a)) (tree (t + 1) (row a))
      (sortTree (t + 1)) (1 + 2 * 2 ^ (t + 1) * (2 * t + 2)) := by
    rw [← hd]
    exact ⟨_, le_rfl, Wide.table _ _ _ (hd.trans_le harity) (.inr ok)⟩
  have prep := (queries_net F a t).par (dict_net F a t z)
  have accept := ((DWide.of_dnet hu prep).comp hs).comp (DWide.of_dnet hu (scan_net F a (t + 1)))
  obtain ⟨v, hv, check⟩ := accept
  have pin := Wide.table (K := F) (labels := L) .bit .unit (fun b _ => if b then 1 else 0)
    (show wd .bit + wd .unit ≤ u by simp only [wd]; omega) (.inl (by decide))
  have valid : Wide F u L (.pair (tree t a) (tree t (count a))) .unit
      (fun y _ => if expected a (flatten t y.1) t z = y.2 then 1 else 0) (v + 2) := by
    convert check.comp pin using 1 <;> try rfl
    funext y _
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have eqn : scan a (t + 1) (sortTree (t + 1) (queries a t y.1, dict a t z y.2)) =
        decide (expected a (flatten t y.1) t z = y.2) := by
      unfold scan
      rw [he, fold_dict a (flatten t y.1) t z y.2 true, Bool.true_and]
    simp only [eqn, decide_eq_true_eq]
  obtain ⟨r, hc, weights⟩ := (weights_net F a f t z).includeWide (L := L) hu
  have out := ((valid.par weights).pre (.unit' _)).trace
  refine ⟨v + 2 + r, ?_, ?_⟩
  · have h2 : 0 < 2 ^ t := pow_pos (by decide) _
    simp only [hr, pow_succ] at hv
    change v + 2 + r ≤ 10000 * 2 ^ t * (1 + wd a)
    dsimp only [t] at *
    nlinarith only [h2, hv, hc]
  · simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      t, weight_lookup a f _ z hn hall] using out

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# A common lookup table for partial batches

Reserve one bit of the address as an enable bit. Inactive rows
contribute one and require no inverse, even when table entries vanish.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Classical Finset Install Transcript

variable {F X I R : Type} [Field F] [Fintype X] [Fintype I] [Fintype R]

omit [Fintype X] in
theorem tap_depends {Y : Type} (read : Y → X ⊕ Bool) :
    Depends (fun x => Sum.elim x id ∘ read) 1 := by
  intro i
  cases h : read i with
  | inl t => exact ⟨{t}, by simp, fun x y he => by simp [h, he t (by simp)]⟩
  | inr v => exact ⟨∅, by simp, fun x y _ => by simp [h]⟩

/-- A batch of at most `2^j` independent, partially hardwired calls. -/
theorem dictionary {w j u : ℕ} (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w)
    (hu : 3 ≤ u) (ha : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ u)
    (hI : Fintype.card I < j) (hR : Fintype.card R ≤ 2 ^ j)
    (k : (I → Bool) → F) (r : R → I → X ⊕ Bool) :
    WideWeight F u (SortTables F w)
      (fun x => ∏ p, k (Sum.elim x id ∘ r p))
      (4 * Fintype.card X + 11000 * 2 ^ j * (1 + j)) := by
  let b := word j
  let names : Option I ↪ slots (word j) :=
    (Function.Embedding.nonempty_of_card_le (by simpa using hI)).some
  let row : R ↪ Fin (2 ^ j) := (Function.Embedding.nonempty_of_card_le (by simpa using hR)).some
  let data (p : R) (i : Option I) : X ⊕ Bool := i.elim (.inr true) (r p)
  let taps := Function.extend row
    (fun p => Function.extend names (data p) (fun _ => .inr false)) (fun _ _ => .inr false)
  let f (x : Val (word j)) := if bits b x (names none) then k (fun i => bits b x (names (some i))) else 1
  have all (x : X → Bool) :
      (∏ i : Fin (2 ^ j), f ((bits b).symm (Sum.elim x id ∘ taps i))) =
        ∏ p, k (Sum.elim x id ∘ r p) := by
    rw [← prod_subset (subset_univ (univ.image row))]
    · rw [prod_image row.injective.injOn]
      refine prod_congr rfl fun p _ => ?_
      simp only [f, taps, Equiv.apply_symm_apply, Function.comp_apply,
        row.injective.extend_apply, names.injective.extend_apply, data, Option.elim_none,
        Option.elim_some, Sum.elim_inr, id_eq, ite_true]
      rfl
    · intro i _ hi
      have hn : ¬∃ p, row p = i := by simpa only [mem_image, mem_univ, true_and] using hi
      simp [taps, Function.extend_apply' _ _ _ hn, f]
  have hlookup := lookup (word j) f (w := w) (u := u)
    (by simpa using hj) (by simpa using hj') (by simpa using ha) hu
  rw [wd_word] at hlookup
  obtain ⟨m, hm, hnet⟩ := hlookup
  obtain ⟨L, hL⟩ := Layout.exists_tree (word j) j
  let read : Fin (2 ^ j) × slots (word j) → X ⊕ Bool := Function.uncurry taps
  intro a ix
  have g := (tap_depends read).bnet F a (tree j (word j)) ix L.positions
  obtain ⟨n, hn, net⟩ := DWide.of_dnet (L := SortTables F w) hu g
  refine ⟨n + m, ?_, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin, MatrixExponent.card_slots, wd_word, localCost] at hn
    change n ≤ 4 * (Fintype.card X + 34 * (2 ^ j * j)) at hn
    nlinarith only [hn, hm, Nat.zero_le (2 ^ j * j), Nat.zero_le (2 ^ j)]
  · have comp := net.comp hnet
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true] at comp
    convert comp using 1
    funext x _
    rw [← hL, List.map_ofFn, List.prod_ofFn]
    refine (all _).symm.trans ?_
    refine prod_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, Layout.read, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    rfl

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Applying any number of beats to the trivalent input

The number of selectors is charged in the smallest bundle units,
independently of how many *bits* each unit carries. Tether names
remain separately recoverable through the preserved fringe.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
open Packing

variable {F : Type} [Field F] {x y : Wire} {u h : ℕ}

def ordinal (h u : ℕ) : Cell h × Fin u ≃ Fin (2 ^ h * u) :=
  Fintype.equivOfCardEq (by simp [Cell])

abbrev start (G : Diagram F x y) (h u : ℕ) := groups G (ordinal h u)

theorem start_seats (G : Diagram F x y) :
    (start G h u).seats = 2 * Fintype.card G.V * 2 ^ h := by
  change Fintype.card (G.V × Bool) * 2 ^ h = _
  rw [Fintype.card_prod, Fintype.card_bool, mul_comm (Fintype.card G.V)]

theorem start_width (G : Diagram F x y) :
    (start G h u).X = 2 ^ h * u * Fintype.card G.E := by
  change Fintype.card (G.E × Cell h) * u = _
  rw [Fintype.card_prod, card_cell]
  ring

theorem start_exact (G : Diagram F x y) :
    (start G h u).diagram.eval = power G.eval (2 ^ h * u) :=
  (eval_gathered G _).trans (G.eval_replicate _)

theorem reduce {b n e K : ℕ} {ρ C : ℝ} (R : Reduction F 8 3 b n e K ρ C) (hρ : ρ ≤ 1)
    (G : Diagram F x y) (hg : G.Trivalent) (M r a z : ℕ)
    (hsize : Fintype.card G.V + wd x + wd y ≤ M) (hz : 0 < z) (hu : u = b * z)
    (hh : a + n * r ≤ h) (hsl : 12 * K ≤ ρ * (2 : ℝ) ^ r) :
    let d := 2 ^ h * u
    (start G h u).Expands (K * (5 * 2 ^ h * M * b)) (fun Q : HostNet F _ a z =>
      Q.seats ≤ K * (2 * M * 2 ^ h) ∧ Q.Bounded 3 (8 ^ e) (K * (6 * (u : ℝ))) ∧
      Q.X ≤ (d : ℝ) * ((3 + C) * ρ * M + C * (wd x + wd y : ℕ)) ∧
      Q.seats ≤ K * (start G h u).seats ∧ Q.mass ≤ 10 * K * d * M ∧
      (∀ p, Q.past p ≤ 6 * u * K * 2 ^ r) ∧ (start G h u).Tracks Q K) := by
  let d := 2 ^ h * u
  let cap := 10 * K * d * M
  let H := (start G h u).reserve cap (r + 1)
  let L := { (fringe (copies x d) (copies y d)) with cap, discount := r + 1 }
  let σ := ρ * d * M / 2
  have hp := R.factor
  have hc := R.loss
  have hσ : 0 ≤ σ := by unfold σ; positivity
  have hV : Fintype.card G.V ≤ M := by omega
  have hE : Fintype.card G.E ≤ 3 * M := by have := G.volume_trivalent hg; omega
  have hS : H.seats ≤ 2 * M * 2 ^ h := by
    change (start G h u).seats ≤ _
    rw [start_seats]
    gcongr
  have hX : (H.X : ℝ) ≤ d * (3 * M : ℕ) := by
    change ((start G h u).X : ℝ) ≤ _
    rw [start_width, Nat.cast_mul]
    gcongr
  -- Active and frozen charges occupy disjoint sites. Half the slack
  -- suffices for the active part, leaving half for eliminated incidences.
  have reserve : L.reserve ≤ σ := by
    change (cap : ℝ) / (2 : ℝ) ^ (r + 1) ≤ ρ * d * M / 2
    rw [div_le_iff₀ (by positivity), pow_succ]
    have he : 10 * (K : ℝ) ≤ ρ * (2 : ℝ) ^ r := by linarith [Nat.cast_nonneg (α := ℝ) K]
    unfold cap
    push_cast
    linarith only [mul_le_mul_of_nonneg_right he (show (0 : ℝ) ≤ d * M by positivity)]
  have hZ : L.Z + σ ≤ d * (wd x + wd y : ℕ) + ρ * d * M := by
    have he : L.Z = (fringe (copies x d) (copies y d)).Z + L.reserve := by
      unfold Fringe.Z
      rw [show (fringe (copies x d) (copies y d)).reserve = 0 by simp [Fringe.reserve, fringe],
        add_zero]
    rw [he, fringe_total, wd_copies, wd_copies]
    push_cast
    unfold σ at reserve ⊢
    linarith only [reserve]
  have hk : K ≤ 2 ^ r := by
    have : (K : ℝ) ≤ (2 : ℝ) ^ r := calc
      _ ≤ (12 : ℝ) * K := by linarith [Nat.cast_nonneg (α := ℝ) K]
      _ ≤ _ := hsl.trans (mul_le_of_le_one_left (by positivity) hρ)
    exact_mod_cast this
  have hslack : (K : ℝ) * (3 * u) * H.seats ≤ σ * (2 : ℝ) ^ r := calc
    _ ≤ (K : ℝ) * (3 * u) * (2 * M * 2 ^ h : ℕ) := by gcongr
    _ = (12 * K) * (d : ℝ) * M / 2 := by unfold d; push_cast; ring
    _ ≤ (ρ * (2 : ℝ) ^ r) * (d : ℝ) * M / 2 := by gcongr
    _ = _ := by unfold σ; ring
  have enough : H.X + (L.Z + σ) ≤ 5 * (d : ℝ) * M := calc
    _ ≤ (d : ℝ) * (3 * M : ℕ) + (d * (wd x + wd y : ℕ) + ρ * d * M) := add_le_add hX hZ
    _ ≤ (d : ℝ) * (3 * M : ℕ) + (d * (M : ℝ) + 1 * d * M) := by
      have hxy : wd x + wd y ≤ M := by omega
      gcongr
    _ = _ := by push_cast; ring
  have budget : H.X + (L.Z + σ) ≤ ((5 * 2 ^ h * M * b : ℕ) : ℝ) * z :=
    enough.trans_eq (by unfold d; rw [hu]; push_cast; ring)
  have empty : (start G h u).mass = 0 := by
    change ∑ _ : (start G h u).V × Cell h, (0 : ℕ) = 0
    simp
  have hb : H.Bounded 8 8 (3 * u) :=
    (bounded G (ordinal h u) hg).start_budget _ empty cap (r + 1)
  obtain ⟨I, _, Q, num, ev, ok⟩ := R.run H z r a 8 (5 * 2 ^ h * M * b) (3 * u) σ hz hu
    (by linarith [Nat.cast_nonneg (α := ℝ) u]) le_rfl hb hσ hh hk hslack budget
  -- Dropping the reserve preserves every weight and address in each diagram.
  refine ⟨I, inferInstance, fun i => (Q i).reserve 0 0, num, ev, fun i => ?_⟩
  obtain ⟨same, hs, hb, hx, hm, tk⟩ := ok i
  have hcap : (Q i).mass ≤ cap := by
    apply (Nat.cast_le (α := ℝ)).mp
    calc
      _ ≤ (H.mass : ℝ) + 2 * (K : ℝ) * (H.X + (L.Z + σ)) := hm
      _ ≤ 0 + 2 * (K : ℝ) * (5 * (d : ℝ) * M) := by
        rw [show H.mass = 0 from empty, Nat.cast_zero]
        gcongr
      _ = (cap : ℝ) := by unfold cap; push_cast; ring
  have hpast (p : (Q i).V × Cell a) : (Q i).past p ≤ 6 * u * K * 2 ^ r := by
    apply (Nat.cast_le (α := ℝ)).mp
    calc
      _ ≤ ((K : ℝ) * (3 * u)) * (2 : ℝ) ^ (r + 1) := hb.past _ hcap p
      _ = _ := by push_cast; ring
  refine ⟨same, hs.trans (Nat.mul_le_mul_left K hS),
    (hb.drop_budget _ 0).mono le_rfl le_rfl (by gcongr; norm_num), hx.trans ?_, hs, hcap, hpast, tk⟩
  calc
    _ ≤ ρ * ((d : ℝ) * (3 * M : ℕ)) + C * (d * (wd x + wd y : ℕ) + ρ * d * M) :=
      add_le_add (mul_le_mul_of_nonneg_left hX hp) (mul_le_mul_of_nonneg_left hZ hc)
    _ = _ := by unfold d; push_cast; ring

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end

/-!
# Addressing the exterior stacks after contraction

All bits of a stack stay together. The block coordinate is common
and linear. Slot numbers may change with the summand, but they are
relative to the *original* exterior station.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
open Finset
open scoped Classical

theorem Preserves.code {F T : Type} {x y : Wire} {L : Fringe x y T} {h a u z K : ℕ}
    {G : HostNet F L h u} {Q : HostNet F L a z}
    (p : G.Preserves Q) (size : Q.seats ≤ K * G.seats) :
    ∃ f : Q.V ↪ G.V × Fin (K * 2 ^ (h - a)), ∀ t, (f (Q.park t).1).1 = (G.park t).1 := by
  obtain ⟨_, _, _, ⟨m, hm, _⟩, B, _, e, he⟩ := p
  by_cases hn : Nonempty G.V
  swap
  · let f : Q.V ↪ G.V × Fin (K * 2 ^ (h - a)) :=
      ⟨fun v => (hn ⟨(e v).1⟩).elim, fun v _ _ => (hn ⟨(e v).1⟩).elim⟩
    exact ⟨f, fun t => (hn ⟨(G.park t).1⟩).elim⟩
  have ha : a ≤ h := by
    have ht := Fintype.card_le_of_surjective m hm
    simpa only [card_cell, Nat.pow_le_pow_iff_right (by decide : 1 < 2)] using ht
  have lim : Fintype.card B ≤ K * 2 ^ (h - a) := by
    unfold seats at size
    rw [Fintype.card_congr e, Fintype.card_prod, show (2 : ℕ) ^ h = 2 ^ (h - a) * 2 ^ a by
      rw [← pow_add, Nat.sub_add_cancel ha]] at size
    have hv : 0 < Fintype.card G.V * 2 ^ a := by
      exact Nat.mul_pos (Fintype.card_pos_iff.mpr hn) (by positivity)
    apply Nat.le_of_mul_le_mul_left _ hv
    simpa only [mul_assoc, mul_left_comm, mul_comm] using size
  obtain ⟨g⟩ : Nonempty (B ↪ Fin (K * 2 ^ (h - a))) := Function.Embedding.nonempty_of_card_le (by simpa)
  exact ⟨e.toEmbedding.trans ((Function.Embedding.refl _).prodMap g), he⟩

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
open Packing Finset
open scoped Classical

def bit (h u : ℕ) (x y : Wire) :
    ((Cell h × Fin u) × Outer x y) ≃ Outer (copies x (2 ^ h * u)) (copies y (2 ^ h * u)) :=
  ((ordinal h u).prodCongr (.refl _)).trans <|
    (Equiv.prodSumDistrib _ _ _).trans ((Diagonal.port x _).symm.sumCongr (Diagonal.port y _).symm)

variable {F : Type} [Field F] {x y : Wire} {h u a z K : ℕ} (G : Diagram F x y)

private theorem start_locate (side : Bool) (i : Outer x y) (s : Cell h) (t : Fin u) :
    locate G (ordinal h u) side (portEnd (start G h u).diagram (bit h u x y ((s, t), i))) = ((portEnd G i, side), s) := by
  cases i with
  | inl i =>
    let q := (Diagonal.port x (2 ^ h * u)) ((Diagonal.port x (2 ^ h * u)).symm ((ordinal h u) (s, t), i))
    change (((G.src.symm (.inl q.2)).1, side), ((ordinal h u).symm q.1).1) = _
    simp [q, portEnd]
  | inr i =>
    let q := (Diagonal.port y (2 ^ h * u)) ((Diagonal.port y (2 ^ h * u)).symm ((ordinal h u) (s, t), i))
    change (((G.dst.symm (.inl q.2)).1, side), ((ordinal h u).symm q.1).1) = _
    simp [q, portEnd]

theorem start_far (i : Outer x y) (s : Cell h) (t : Fin u) :
    (start G h u).units.place (portEnd (start G h u).diagram (bit h u x y ((s, t), i))) =
      ((portEnd G i, false), s) :=
  start_locate G false i s t

theorem start_park (i : Outer x y) (s : Cell h) (t : Fin u) :
    (start G h u).park (bit h u x y ((s, t), i)) = ((portEnd G i, true), s) :=
  start_locate G true i s t

variable (Q : HostNet F (fringe (copies x (2 ^ h * u)) (copies y (2 ^ h * u))) a z)

structure Holders (K : ℕ) where
  block : Cell h →ₗ[ZMod 2] Cell a
  onto : Function.Surjective block
  host : Outer x y → Cell h → Q.V
  core : Outer x y → Cell h → Q.V
  code : Q.V ↪ (G.V × Bool) × Fin (K * 2 ^ (h - a))
  park : ∀ i s t, Q.park (bit h u x y ((s, t), i)) = (host i s, block s)
  tip : ∀ i s t, Q.units.place (portEnd Q.diagram (bit h u x y ((s, t), i))) = (core i s, block s)
  original : ∀ i s, (code (host i s)).1 = (portEnd G i, true)

theorem holders (hu : 0 < u) (same : (start G h u).Preserves Q)
    (size : Q.seats ≤ K * (start G h u).seats) : Nonempty (Holders G Q K) := by
  obtain ⟨code, hcode⟩ := same.code size
  obtain ⟨o, ho, ht, ⟨b, hb, he⟩, _⟩ := same
  let core i s := (o ((portEnd G i, false), s)).1
  let host i s := (o ((portEnd G i, true), s)).1
  have park i s t : Q.park (bit h u x y ((s, t), i)) = (host i s, b s) := by
    rw [ho, Function.comp_apply, start_park]
    exact Prod.ext rfl (he _)
  have tip i s t : Q.units.place (portEnd Q.diagram (bit h u x y ((s, t), i))) = (core i s, b s) := by
    rw [ht, show (start G h u).units.place _ = _ from start_locate G false i s t]
    exact Prod.ext rfl (he _)
  refine ⟨⟨b, hb, host, core, code, park, tip, fun i s => ?_⟩⟩
  have eq := hcode (bit h u x y ((s, ⟨0, hu⟩), i))
  rw [park, start_park] at eq
  exact eq

omit [Field F] in
private theorem original_names (w : G.V) :
    (univ.filter fun i : Outer x y => portEnd G i = w).card ≤ G.arity w := by
  have ha := site_arity G id w
  rw [port_load] at ha
  simp only [Function.id_comp, push, sum_boole, id_eq, sum_ite_eq', mem_univ, ite_true] at ha
  exact_mod_cast le_trans (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) _)) ha.ge

omit [Field F] in
theorem Holders.names (p : Holders G Q K) (ht : G.Trivalent) (v : Q.V) :
    (univ.filter fun i : Outer x y => ∃ s, p.host i s = v).card ≤ 3 := by
  let w := (p.code v).1.1
  have sub : (univ.filter fun i : Outer x y => ∃ s, p.host i s = v) ⊆
      univ.filter (fun i => portEnd G i = w) := by
    intro i hi
    obtain ⟨s, h⟩ := (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ _, congrArg Prod.fst ((p.original i s).symm.trans
      (congrArg (fun v => (p.code v).1) h))⟩
  refine (card_le_card sub).trans (le_trans ?_ (ht w))
  exact original_names G w

variable {G Q} {k : ℕ} (p : Holders G Q K)

private theorem Holders.pair (i : Outer x y) (s : Cell h) (t : Fin u) :
    let e := bit h u x y ((s, t), i)
    (start G h u).tip e = (portEnd G i, false) ∧ Q.tip e = p.core i s :=
  ⟨congrArg Prod.fst (start_locate G false i s t), congrArg Prod.fst (p.tip i s t)⟩

/-- All copies of one original input have a short menu of core sites. -/
theorem Holders.reach (hu : 0 < u) (tk : (start G h u).Tracks Q k) (i : Outer x y) :
    (univ.image (p.core i)).card ≤ k * 2 ^ (h - a) := by
  refine (card_le_card ?_).trans (tk.2 (portEnd G i, false))
  intro v hv
  obtain ⟨s, _, rfl⟩ := mem_image.mp hv
  exact (HostNet.mem_reach _ _).mpr ⟨_, p.pair i s ⟨0, hu⟩⟩

/-- At most three original exterior names can originate at each old site. -/
theorem Holders.origins (hg : G.Trivalent) (hu : 0 < u) (tk : (start G h u).Tracks Q k)
    (v : Q.V) :
    (univ.filter fun i : Outer x y => ∃ s, p.core i s = v).card ≤ 3 * k := by
  let names (w : (start G h u).V) := univ.filter fun i : Outer x y => portEnd G i = w.1
  have bound w : (names w).card ≤ 3 := (original_names G w.1).trans (hg _)
  have sub : (univ.filter fun i : Outer x y => ∃ s, p.core i s = v) ⊆
      (Q.reach (start G h u) v).biUnion names := by
    intro i hi
    obtain ⟨s, hs⟩ := (mem_filter.mp hi).2
    have he := p.pair i s ⟨0, hu⟩
    have hit : (portEnd G i, false) ∈ Q.reach (start G h u) v :=
      (HostNet.mem_reach _ _).mpr ⟨_, he.2.trans hs, he.1⟩
    exact mem_biUnion.mpr ⟨_, hit, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  refine (card_le_card sub).trans (card_biUnion_le.trans ((sum_le_sum (fun q _ => bound q)).trans ?_))
  rw [sum_const, Nat.nsmul_eq_mul, mul_comm]
  exact Nat.mul_le_mul_left _ (tk.1 v)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end
