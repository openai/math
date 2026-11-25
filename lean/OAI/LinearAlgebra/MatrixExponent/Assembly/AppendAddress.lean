import OAI.LinearAlgebra.MatrixExponent.Coloring.Add
import OAI.LinearAlgebra.MatrixExponent.Coloring.Shift
import OAI.LinearAlgebra.MatrixExponent.Coloring.Matching
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Packing.FieldLift
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Packets

section
/-! # An exact binary reduction with one additional carry bit per level -/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Finset

def total (h k : ℕ) (x : B h → B k) : B (k + h) :=
  ⟨∑ i, (x i).val, by
    have H := sum_lt_sum_of_nonempty (s := univ) univ_nonempty (fun i _ => (x i).isLt)
    simpa [pow_add, mul_comm] using H⟩

private def plus (k : ℕ) (x : B k × B k) : B (k + 1) :=
  ⟨x.1.val + x.2.val, by have := x.1.isLt; have := x.2.isLt; rw [pow_succ]; omega⟩

variable (F : Type) [Field F]

private theorem plus_net (k : ℕ) :
    Circuit F (.pair (.addr k) (.addr k)) (.addr (k + 1)) (plus k) (20000 * (k + 2)) := by
  have t := numeric_extend F k
  have s := (t.par t).comp (numeric_add F (k + 1))
  convert s.mono (n := 20000 * (k + 2)) (by omega) using 1
  funext x
  apply Fin.ext
  exact (Nat.mod_eq_of_lt (plus k x).isLt).symm

private def pairs (h k : ℕ) (x : B (h + 1) → B k) (i : B h) :=
  (x (halves h (.inl i)), x (halves h (.inr i)))

private theorem total_net (h k n : ℕ) (hn : n = k + h) :
    ∃ f : (B h → B k) → B n,
      Circuit F (.vec h (.addr k)) (.addr n) f (2 ^ h * 50000 * (k + 3)) ∧
      ∀ x, (f x).val = ∑ i, (x i).val := by
  induction h generalizing k with
  | zero =>
    simp only [add_zero] at hn
    subst n
    have t := Circuit.project (F := F) (A := .vec 0 (.addr k)) (D := .addr k)
      (f := fun x => x 0) (fun i => (0, i)) (fun _ _ => rfl)
    refine ⟨_, t.mono (by simp; omega), fun x => ?_⟩
    exact (Fin.sum_univ_one (fun i => (x i).val)).symm
  | succ h ih =>
    obtain ⟨f, hf, he⟩ := ih (k + 1) (by omega)
    have t := Circuit.project (F := F) (A := .vec (h + 1) (.addr k))
      (D := .vec h (.pair (.addr k) (.addr k))) (f := pairs h k)
      (fun p => p.2.elim (fun j => (halves h (.inl p.1), j)) (fun j => (halves h (.inr p.1), j)))
      (by rintro x ⟨i, j|j⟩ <;> rfl)
    have s := Circuit.map (A := .pair (.addr k) (.addr k)) (D := .addr (k + 1))
      (fun _ : B h => plus k) (fun _ => plus_net F k)
    refine ⟨_, ((t.comp s).comp hf).mono ?_, fun x => ?_⟩
    · simp only [Format.width_vec, Format.width_pair, Format.width_addr, pow_succ]
      ring_nf
      omega
    · simp only [Function.comp_apply, he, pairs, plus, sum_add_distrib]
      rw [← (halves h).sum_comp (fun i => (x i).val), Fintype.sum_sum_type]

/-- The cost grows linearly with the number of entries for fixed input width. -/
theorem cheap_total (h k : ℕ) :
    Cheap F h k (.vec h (.addr k)) (.addr (k + h)) (total h k) 5 := by
  obtain ⟨f, hf, he⟩ := total_net F h k (k + h) rfl
  have eq : f = total h k := funext fun x => Fin.ext (he x)
  rw [eq] at hf
  refine ⟨_, hf, ?_⟩
  simp only [Format.width_vec, Format.width_addr]
  have hpow : h < 2 ^ h := Nat.lt_pow_self (by decide)
  have hk : k ≤ 2 ^ h * k := Nat.le_mul_of_pos_left _ (by positivity)
  ring_nf at hk ⊢
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Electing a common choice from local scores

Rows have short scores even when the number of rows is large.
Accumulate each column along a carry tree before comparing the totals.
Sort with a deterministic tie break by candidate number.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Finset
open scoped Classical

variable {h k d : ℕ}

def rankAt (i : B k) (x : B k → B d) := permutation x (fun _ => true) i

theorem rankAt_le (x : B k → B d) (i j : B k) (hij : i ≤ j) :
    x (rankAt i x) ≤ x (rankAt j x) := by
  have he := Tuple.monotone_sort (fun j => toLex (false, toLex (x j, j))) hij
  change toLex (false, toLex (x (rankAt i x), rankAt i x)) ≤
    toLex (false, toLex (x (rankAt j x), rankAt j x)) at he
  rw [Prod.Lex.toLex_le_toLex] at he
  rcases he with hh | ⟨_, hh⟩
  · exact (lt_irrefl _ hh).elim
  · rw [Prod.Lex.toLex_le_toLex] at hh
    exact hh.elim (fun h => h.le) (fun h => h.1.le)

def elect (i : B k) (x : B k → B h → B d) := rankAt i (fun j => total h d (x j))

theorem elect_min (x : B k → B h → B d) (j : B k) :
    (∑ v, (x (elect ⊥ x) v).val) ≤ ∑ v, (x j v).val := by
  let y i := total h d (x i)
  have hx := rankAt_le y _ ((permutation y (fun _ => true)).symm j) bot_le
  rw [show rankAt _ y = j from (permutation y _).apply_symm_apply j] at hx
  exact hx

theorem elect_max (x : B k → B h → B d) (j : B k) :
    (∑ v, (x j v).val) ≤ ∑ v, (x (elect ⊤ x) v).val := by
  let y i := total h d (x i)
  have hx := rankAt_le y ((permutation y (fun _ => true)).symm j) _ le_top
  rw [show rankAt _ y = j from (permutation y _).apply_symm_apply j] at hx
  exact hx

variable (F : Type) [Field F]

private theorem cheap_rankAt (k d : ℕ) (i : B k) :
    Cheap F k (k + d) (.vec k (.addr d)) (.addr k) (rankAt i) 42 := by
  have addr (m : ℕ) (hm : m ≤ k + d) :
      (Format.vec k (.addr m)).width ≤ 2 ^ k * (100 + (k + d)) ^ 1 := by
    simp only [Format.width_vec, Format.width_addr, pow_one]
    gcongr
    omega
  have hv := addr d (by omega)
  have hf : (Format.vec k .bit).width ≤ 2 ^ k * (100 + (k + d)) ^ 1 := by
    rw [Format.width_vec, Format.width_bit, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have ho : (Format.addr k).width ≤ 2 ^ k * (100 + (k + d)) ^ 1 := by
    rw [Format.width_addr, pow_one]
    exact le_trans (by omega : k ≤ 100 + (k + d)) (Nat.le_mul_of_pos_left _ (by positivity))
  have flags := (Cheap.id F hv).pair (Cheap.const F hv hf (fun _ => true))
  have get := Cheap.project F (A := .vec k (.addr k)) (D := .addr k) (f := fun x => x i) (addr k (by omega)) ho (fun j => (i, j))
    (fun _ _ => rfl)
  exact (flags.comp (cheap_permutation F k d)).comp get

/-- The polynomial in the host address length is incurred just once per
candidate. Per host and candidate the cost only depends on the score width. -/
theorem election (h k d : ℕ) (i : B k) :
    Circuit F (.vec k (.vec h (.addr d))) (.addr k) (elect i)
      (2 ^ k * (2 ^ h * (100 + d) ^ 5 + (100 + (k + (d + h))) ^ 42)) := by
  obtain ⟨m, hm, hm'⟩ := cheap_total F h d
  obtain ⟨n, hn, hn'⟩ := cheap_rankAt F k (d + h) i
  have net := Circuit.map (A := .vec h (.addr d)) (D := .addr (d + h)) (fun _ : B k => total h d)
    (fun _ => hm)
  refine (net.comp hn).mono ?_
  rw [mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (by omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Applying a common weighted table at each occurrence

Carry the graph once per host. A product of the local weights both
rejects invalid choices and withdraws any prescribed scalar factors.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} [Field F] {I : Type*} {A D : Format} {u m d h : ℕ} {L : Set (Table F)}

def Fmt.zip (x : (Fmt.rows m d h A).obj × (Format.vec m (.vec h D)).obj) :
    (Fmt.rows m d h (.pair A D)).obj := fun i => ((x.1 i).1, fun j => ((x.1 i).2 j, x.2 i j))

theorem map_zip (hu : 3 ≤ u) :
    Map F u L (.pair (Fmt.rows m d h A) (.vec m (.vec h D))) (Fmt.rows m d h (.pair A D))
      Fmt.zip (12 * (Fmt.rows m d h (.pair A D)).width) := by
  let X := Format.pair (Fmt.rows m d h A) (.vec m (.vec h D))
  let Y := Fmt.rows m d h (.pair A D)
  let pin : Y.pins → X.pins
    | (i, .inl j) => .inl (i, .inl j)
    | (i, .inr (j, .inl k)) => .inl (i, .inr (j, k))
    | (i, .inr (j, .inr k)) => .inr (i, j, k)
  have hp : Circuit F X Y Fmt.zip (X.width + 2 * Y.width) :=
    Circuit.project pin (by rintro x ⟨i, j|⟨j, k|k⟩⟩ <;> rfl)
  have hw : X.width = Y.width := by simp [X, Y, Fmt.rows, mul_add, add_assoc]
  exact (Map.circuit hu hp).mono (by change _ ≤ 12 * Y.width; omega)

variable (f : A.obj → D.obj) (g : A.obj → F)

def Fmt.update (x : (Fmt.rows m d h A).obj) : (Fmt.rows m d h D).obj :=
  fun i => ((x i).1, fun j => f ((x i).2 j))

def Fmt.weight (x : (Fmt.rows m d h A).obj) := ∏ i, ∏ j, g ((x i).2 j)

def updateCost (m d h : ℕ) (A D : Format) := 2 ^ m * (4 * (2 ^ d * m) + 2 ^ h * (1 + A.width + D.width))

def weightTable := lookup F A D (fun x y => if f x = y then g x else 0)

theorem update (hu : 3 ≤ u) (hw : A.width + D.width ≤ u) (hg : weightTable f g ∈ L) :
    Action F u L (Fmt.rows m d h A) (Fmt.rows m d h D) (Fmt.update f) (Fmt.weight g)
      (updateCost m d h A D) := by
  have hk : Action F u L A D f g (1 + A.width + D.width) := Kernel.lookup hw hg
  let P := Format.vec d (.addr m)
  have hP := Action.of_map (Map.circuit (L := L) hu (Circuit.id F P))
  have hb := Action.vec _ _ (fun _ : B h => hk)
  have hr := Action.vec _ _ (fun _ : B m => hP.par hb)
  have hp : P.width = 2 ^ d * m := by simp [P]
  simp only [one_mul, hp] at hr
  exact hr

theorem computes_update (hu : 3 ≤ u) (hw : A.width + D.width ≤ u) (hg : weightTable f g ∈ L)
    (x : I → (Fmt.rows m d h A).obj) :
    Computes F u L (Fmt.rows m d h A) (Fmt.rows m d h D) x
      (Fmt.update f ∘ x) (Fmt.weight g ∘ x) (updateCost m d h A D) :=
  Computes.of_action (update f g hu hw hg) (fun _ => rfl) (fun _ => rfl)

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Computing a layout from the selected profile tags

Each row presents an activity bit and a short selector. Inactive rows
contribute zero. The comparison is global, but the cost per row depends
only on the size of the profile dictionary.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Side

open Coloring Finset
open scoped Classical

abbrev Entry (a : ℕ) := Format.pair .bit (.addr a)
abbrev Input (n a : ℕ) := Format.vec n (Entry a)

variable {a n t : ℕ} (profile : B a → Fin 8 → ℕ)

def value (col : Bool) (q : (Entry a).obj) :=
  if q.1 then Packing.profileScore col (profile q.2) else 0

def pick (x : (Input n a).obj) : Bool :=
  decide ((∑ i, value profile true (x i)) < ∑ i, value profile false (x i))

/-- Any order and padding of the selected profiles give the same decision. -/
theorem pick_eq_side {I : Type} [Fintype I] (f : I → Fin 8 → ℕ)
    (x : (Input n a).obj) (row : I ↪ B n)
    (active : ∀ i, (x i).1 = true ↔ i ∈ Set.range row)
    (code : ∀ e, profile (x (row e)).2 = f e) :
    pick profile x = Packing.side f := by
  have score (c : Bool) : ∑ i, value profile c (x i) = ∑ e, Packing.profileScore c (f e) := by
    unfold value
    rw [← sum_filter]
    have rows : (univ.filter fun i => (x i).1 = true) = univ.image row := by
      ext i
      simp only [mem_filter_univ, active, mem_image, mem_univ, true_and, Set.mem_range]
    rw [rows, sum_image row.injective.injOn]
    simp only [code]
  simp only [pick, Packing.side, score]

private theorem value_bound (hc : ∀ p, ∑ j, profile p j < 2 ^ t)
    (c : Bool) (q : (Entry a).obj) : value profile c q < 2 ^ t := by
  have he := Packing.score_sum (profile q.2)
  have ht := hc q.2
  unfold value
  split_ifs
  · cases c <;> omega
  · exact Nat.two_pow_pos _

private theorem cheap_row (F : Type) [Field F] (ha : 2 ^ a ≤ t) (f : (Entry a).obj → B t) :
    Cheap F 0 t (Entry a) (.addr t) f 3 := by
  have h : Install.Depends ((Format.addr t).code ∘ f ∘ (Entry a).code.symm) (1 + a) := by
    intro i
    refine ⟨univ, ?_, fun x y he => ?_⟩
    · change (Entry a).width ≤ _
      simp [Entry]
    · rw [funext (fun j => he j (mem_univ _))]
  refine ⟨_, h.bnet F, ?_⟩
  change (Entry a).width + (Format.addr t).width +
    ((Entry a).width + Install.localCost (1 + a) * (Format.addr t).width) ≤ _
  have hat : a ≤ t := (Nat.lt_pow_self (by decide : 1 < 2)).le.trans ha
  have hp : Install.localCost (1 + a) ≤ 2 * (1 + t) + 32 * t := by
    unfold Install.localCost
    rw [show 1 + a + 1 = a + 1 + 1 by omega, pow_succ, pow_succ]
    omega
  have hs := Nat.mul_le_mul_right t hp
  simp only [Entry, Format.width_pair, Format.width_addr, pow_zero, one_mul]
  rw [Format.width_bit]
  ring_nf at hs ⊢
  omega

private theorem cheap_lt (F : Type) [Field F] (n t : ℕ) :
    Cheap F n t (.pair (.addr (t + n)) (.addr (t + n))) .bit (fun x => decide (x.1 < x.2)) 4 := by
  refine ⟨_, numeric_lt F _, ?_⟩
  simp only [Format.width_pair, Format.width_addr]
  have hn := Nat.lt_pow_self (n := n) (by decide : 1 < 2)
  have ht := Nat.le_mul_of_pos_left t (Nat.two_pow_pos n)
  rw [Format.width_bit]
  ring_nf at ht ⊢
  omega

theorem cheap_pick (F : Type) [Field F] (n t : ℕ) (ha : 2 ^ a ≤ t)
    (hc : ∀ p, ∑ j, profile p j < 2 ^ t) :
    Cheap F n t (Input n a) .bit (pick profile) 8 := by
  let score c q : B t := ⟨value profile c q, value_bound profile hc c q⟩
  have sum (c : Bool) : Cheap F n t (Input n a) (.addr (t + n))
      (fun x => total n t (fun i => score c (x i))) 6 :=
    (Cheap.map (A := Entry a) (D := .addr t) (h := n) (fun _ => score c)
      (fun _ => cheap_row F ha (score c))).comp (cheap_total F n t)
  exact ((sum true).pair (sum false)).comp (cheap_lt F n t)

theorem map_pick (F : Type) [Field F] {u : ℕ} (hu : 3 ≤ u) (L : Set (Table F))
    (n t : ℕ) (ha : 2 ^ a ≤ t) (hc : ∀ p, ∑ j, profile p j < 2 ^ t) :
    Map F u L (Input n a) .bit (pick profile) (4 * (2 ^ n * (100 + t) ^ 8)) := by
  obtain ⟨m, hm, hbound⟩ := cheap_pick profile F n t ha hc
  exact (Map.circuit hu hm).mono (by omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Side
end

/-!
# Computing the global layout from short local records

At each host, pair the mask with one selector per row. Inactive
positions can contain arbitrary data and are normalized to zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Side

open Coloring

abbrev Tagged (d h e k ℓ a : ℕ) := Format.pair (Match.Input d h e k ℓ) (.vec (h + e) (.addr a))

variable {m d h e k ℓ n a t : ℕ}

def clean (x : (Entry a).obj) : (Entry a).obj := (x.1, if x.1 then x.2 else 0)

def collect (x : (Tagged d h e k ℓ a).obj) : (Input (h + e) a).obj :=
  fun i => clean ((Match.rows x.1).control.1 i, x.2 i)

def extract (x : B m → (Tagged d h e k ℓ a).obj) : (Input (m + (h + e)) a).obj :=
  fun i => collect (x (Match.rowIndex m (h + e) i).1) (Match.rowIndex m (h + e) i).2

variable (F : Type) [Field F]

private theorem cheap_clean (ha : a ≤ t) : Cheap F 0 t (Entry a) (Entry a) clean 10 := by
  have hw : (Entry a).width ≤ 2 ^ 0 * (100 + t) ^ 1 := by
    rw [Format.width_pair, Format.width_bit, Format.width_addr]
    simp only [pow_zero, one_mul, pow_one]; omega
  have hv : (Format.addr a).width ≤ 2 ^ 0 * (100 + t) ^ 1 := by
    rw [Format.width_addr]; simp only [pow_zero, one_mul, pow_one]; omega
  have x := Cheap.id F hw
  have z := Cheap.const F hw hv (0 : B a)
  have y := ((x.snd.pair z).pair x.fst).comp ((cheap_select F a).widen ha)
  exact (x.fst.pair y).mono (by decide)

private theorem cheap_tag {A D V : Format} {f : A.obj → D.obj} {c : ℕ}
    (hf : Cheap F n t A D f c) (hv : V.width ≤ 2 ^ n * (100 + t)) :
    Cheap F n t (.pair A V) (.pair D V) (fun x => (f x.1, x.2)) (c + 2) := by
  obtain ⟨p, hp, hb⟩ := hf.mono (d := c + 1) (by omega)
  have hh : V.width ≤ 2 ^ n * (100 + t) ^ (c + 1) := by
    apply hv.trans
    rw [pow_succ]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by positivity))
  refine ⟨_, hp.par (Circuit.id F V), ?_⟩
  rw [Format.width_pair, Format.width_pair]
  have ht : 4 * (2 ^ n * (100 + t) ^ (c + 1)) ≤ 2 ^ n * (100 + t) ^ (c + 2) := by
    rw [mul_comm 4, show c + 2 = (c + 1) + 1 by omega, pow_succ (100 + t) (c + 1), ← mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

theorem cheap_collect (ht : Rows.overhead (h + e) (Match.Labels h ℓ d).width ≤ t)
    (hk : k ≤ t) (hd : 2 ^ d ≤ t) (ha : a ≤ t) :
    Cheap F (h + e) t (Tagged d h e k ℓ a) (Input (h + e) a) collect 156 := by
  have mask := (Match.cheap_match F d h e k ℓ t ht hk hd).fst
  have hv : (Format.vec (h + e) (.addr a)).width ≤ 2 ^ (h + e) * (100 + t) := by
    rw [Format.width_vec, Format.width_addr]
    exact Nat.mul_le_mul_left _ (by omega)
  have tag := (cheap_tag F mask hv).zip
  exact (tag.comp (Cheap.map (A := Entry a) (D := Entry a) (h := h + e)
    (fun _ => clean) (fun _ => cheap_clean F ha))).mono (by decide)

private theorem batch {A D : Format} {f : A.obj → D.obj} {c : ℕ}
    (hf : Cheap F n t A D f c) :
    Cheap F (m + n) t (.vec m A) (.vec m D) (fun x i => f (x i)) c := by
  obtain ⟨p, hp, hb⟩ := hf
  refine ⟨_, Circuit.map _ (fun _ : B m => hp), ?_⟩
  simpa only [Format.width_vec, ← mul_add, pow_add, mul_assoc] using Nat.mul_le_mul_left (2 ^ m) hb

private theorem flatten (A : Format) (hw : A.width ≤ 100 + t) :
    Cheap F (m + n) t (.vec m (.vec n A)) (.vec (m + n) A)
      (fun x i => x (Match.rowIndex m n i).1 (Match.rowIndex m n i).2) 2 := by
  have hb : (Format.vec (m + n) A).width ≤ 2 ^ (m + n) * (100 + t) ^ 1 := by
    rw [Format.width_vec, pow_one]
    exact Nat.mul_le_mul_left _ hw
  have he : (Format.vec m (.vec n A)).width = (Format.vec (m + n) A).width := by
    simp only [Format.width_vec, pow_add, mul_assoc]
  exact Cheap.project F (he.le.trans hb) hb
    (fun i => ((Match.rowIndex m n i.1).1, (Match.rowIndex m n i.1).2, i.2)) (fun _ _ => rfl)

theorem cheap_extract (ht : Rows.overhead (h + e) (Match.Labels h ℓ d).width ≤ t)
    (hk : k ≤ t) (hd : 2 ^ d ≤ t) (ha : a ≤ t) :
    Cheap F (m + (h + e)) t (.vec m (Tagged d h e k ℓ a)) (Input (m + (h + e)) a) extract 157 := by
  have hw : (Entry a).width ≤ 100 + t := by
    rw [Format.width_pair, Format.width_bit, Format.width_addr]
    omega
  exact ((batch F (m := m) (cheap_collect F ht hk hd ha)).comp
    (flatten F (Entry a) (m := m) (n := h + e) hw)).mono (by decide)

theorem map_layout {u : ℕ} (hu : 3 ≤ u) (L : Set (Table F)) (profile : B a → Fin 8 → ℕ)
    (ht : Rows.overhead (h + e) (Match.Labels h ℓ d).width ≤ t)
    (hk : k ≤ t) (hd : 2 ^ d ≤ t) (ha : 2 ^ a ≤ t) (hc : ∀ p, ∑ j, profile p j < 2 ^ t) :
    Map F u L (.vec m (Tagged d h e k ℓ a)) .bit (pick profile ∘ extract)
      (4 * (2 ^ (m + (h + e)) * (100 + t) ^ 158)) := by
  have hat : a ≤ t := (Nat.lt_pow_self (by decide : 1 < 2)).le.trans ha
  obtain ⟨s, hs, hb⟩ := (cheap_extract F (m := m) ht hk hd hat).comp
    (cheap_pick profile F _ t ha hc)
  exact (Map.circuit hu hs).mono (Nat.mul_le_mul_left 4 ((Nat.le_add_left _ _).trans hb))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Side
end

section
/-! # Selecting one marked stub at each block -/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring
variable {h e t : ℕ}

private abbrev orderMask (x : B e → Bool) := permutation (fun _ => (0 : B 0)) x

def pick (x : B e → Bool) := orderMask x 0

theorem pick_marked (x : B e → Bool) (h : ∃ i, x i = true) : x (pick x) = true := by
  obtain ⟨i, hi⟩ := h
  let σ := orderMask x
  have he := Tuple.monotone_sort (fun j => toLex (!x j, toLex ((0 : B 0), j)))
    (show 0 ≤ σ.symm i from bot_le)
  change toLex (!x (σ 0), toLex ((0 : B 0), σ 0)) ≤
    toLex (!x (σ (σ.symm i)), toLex ((0 : B 0), σ (σ.symm i))) at he
  rw [Equiv.apply_symm_apply, hi, Prod.Lex.toLex_le_toLex] at he
  change x (σ 0) = true
  cases h : x (σ 0) <;> simp [h] at he ⊢
  exact absurd he (by decide)

variable (F : Type) [Field F]

private theorem bit_width (h t : ℕ) : (Format.vec h .bit).width ≤ 2 ^ h * (100 + t) ^ 1 := by
  rw [Format.width_vec, Format.width_bit, pow_one]
  exact Nat.mul_le_mul_left _ (by omega)

private theorem cheap_orderMask (he : e ≤ t) :
    Cheap F e t (.vec e .bit) (Perm e) (fun x => ⇑(orderMask x)) 42 := by
  have hw := bit_width e t
  have hk := column_width e (Nat.zero_le t)
  have flags := (Cheap.const F hw hk (fun _ => 0)).pair (Cheap.id F hw)
  exact (flags.comp ((cheap_permutation F e 0).widen he)).mono (by decide)

private theorem cheap_pick (he : e ≤ t) (A : Format) (ha : A.width ≤ t) :
    Cheap F e t (.pair (.vec e .bit) (.vec e A)) A (fun x => x.2 (pick x.1)) 47 := by
  have hv : (Format.vec e A).width ≤ 2 ^ e * (100 + t) ^ 1 := by
    rw [Format.width_vec, pow_one]; exact Nat.mul_le_mul_left _ (by omega)
  have hw : (Format.pair (.vec e .bit) (.vec e A)).width ≤ 2 ^ e * (100 + t) ^ 1 := by
    rw [Format.width_pair, Format.width_vec, Format.width_bit, Format.width_vec, ← mul_add, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have h₀ : A.width ≤ 2 ^ e * (100 + t) ^ 1 := by
    rw [Format.width_vec] at hv
    exact (Nat.le_mul_of_pos_left _ (by positivity)).trans hv
  have head : Cheap F e t (.vec e A) A (fun x => x 0) 2 :=
    Cheap.project F hv h₀ (fun i => (0, i)) (fun _ _ => rfl)
  have x := Cheap.id F hw
  have gather := (x.snd.pair (x.fst.comp (cheap_orderMask F he))).comp (Cheap.lookup F e t A he ha)
  exact (gather.comp head).mono (by decide)

private theorem copies {A D : Format} {f : A.obj → D.obj} {n : ℕ}
    (hf : Cheap F e t A D f n) (h : ℕ) :
    Cheap F (h + e) t (.vec h A) (.vec h D) (fun x i => f (x i)) n := by
  obtain ⟨m, hm, hb⟩ := hf
  refine ⟨_, Circuit.map (fun _ => f) (fun _ => hm), ?_⟩
  simpa only [Format.width_vec, ← mul_add, pow_add, mul_assoc] using Nat.mul_le_mul_left (2 ^ h) hb

noncomputable def sampleRow (x : B (h + e) → Bool) (i : B h) :=
  (rowIndex h e).symm (i, pick (fun j => x ((rowIndex h e).symm (i, j))))

theorem sampleRow_block (x : B (h + e) → Bool) (i : B h) : (rowIndex h e (sampleRow x i)).1 = i := by
  simp [sampleRow]

theorem sampleRow_marked (x : B (h + e) → Bool) {i : B (h + e)} (hi : x i = true) :
    x (sampleRow x (rowIndex h e i).1) = true := by
  unfold sampleRow
  apply pick_marked (fun j => x ((rowIndex h e).symm ((rowIndex h e i).1, j)))
  exact ⟨(rowIndex h e i).2, by simpa using hi⟩

theorem cheap_sample (he : e ≤ t) (A : Format) (ha : A.width ≤ t) :
    Cheap F (h + e) t (.pair (.vec (h + e) .bit) (.vec (h + e) A)) (.vec h A)
      (fun x i => x.2 (sampleRow x.1 i)) 48 := by
  let L := Format.pair (.vec (h + e) .bit) (.vec (h + e) A)
  let R := Format.vec h (.pair (.vec e .bit) (.vec e A))
  have hl : L.width ≤ 2 ^ (h + e) * (100 + t) ^ 1 := by
    unfold L
    rw [Format.width_pair, Format.width_vec, Format.width_vec, Format.width_bit, ← mul_add, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have hr : R.width ≤ 2 ^ (h + e) * (100 + t) ^ 1 := by
    refine le_trans ?_ hl
    simp only [L, R, Format.width_vec, Format.width_pair, pow_add, mul_add, mul_assoc]
    exact le_rfl
  have prep : Cheap F (h + e) t L R (fun x i =>
      (fun j => x.1 ((rowIndex h e).symm (i, j)), fun j => x.2 ((rowIndex h e).symm (i, j)))) 2 := by
    apply Cheap.project F hl hr (fun p => Sum.elim
      (fun q => .inl ((rowIndex h e).symm (p.1, q.1), q.2))
      (fun q => .inr ((rowIndex h e).symm (p.1, q.1), q.2)) p.2)
    rintro x ⟨i, j|j⟩ <;> rfl
  exact (prep.comp (copies F (cheap_pick F he A ha) h)).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

section
/-! # Concatenating the high and low parts of a row address -/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match

open Coloring Control Transcript.Messages

private theorem append_value (a b : ℕ) (x : Val (word a)) (y : Val (word b)) :
    Lookup.value (a + b) (appendWord a b y x) = Lookup.value b y + 2 ^ b * Lookup.value a x := by
  induction b with
  | zero => simp [appendWord, Lookup.value]
  | succ b ih =>
    change y.1.toNat + 2 * Lookup.value (a + b) (appendWord a b y.2 x) =
      y.1.toNat + 2 * Lookup.value b y.2 + 2 ^ (b + 1) * Lookup.value a x
    rw [ih]
    ring

private theorem append_wire (a b : ℕ) :
    Rewire (.pair (word b) (word a)) (word (a + b)) (fun x => appendWord a b x.1 x.2) := by
  induction b with
  | zero => exact (Rewire.swap _ _).comp (.unit _)
  | succ b ih => exact (Rewire.assoc _ _ _).comp ((Rewire.id .bit).par ih)

theorem append_address (F : Type) [Field F] (a b : ℕ) :
    Circuit F (.pair (.addr a) (.addr b)) (.addr (a + b)) (rowIndex a b).symm (a + b) := by
  have h := (DNet.id F (word (a + b))).pre ((Rewire.swap _ _).comp (append_wire a b))
  rw [wd_word] at h
  refine Circuit.of_dnet (.refl _) (.refl _) h (fun x => ?_)
  simp only [Equiv.coe_refl, Function.comp_id]
  have he : (Format.pair (.addr a) (.addr b)).code.symm (bits (.pair (word a) (word b)) x) =
      (index a x.1, index b x.2) := Prod.ext (decode_addr a x.1) (decode_addr b x.2)
  rw [he, ← code_addr]
  congr 1
  exact Fin.ext (append_value a b x.1 x.2)

/-- Each bit of the concatenation is a fixed bit of one input address. -/
theorem append_pin (a b : ℕ) (i : slots (word (a + b))) :
    ∃ k : slots (word a) ⊕ slots (word b), ∀ x y,
      (Format.addr (a + b)).code ((rowIndex a b).symm (x, y)) i =
        Sum.elim ((Format.addr a).code x) ((Format.addr b).code y) k := by
  obtain ⟨e, he⟩ := ((Rewire.swap _ _).comp (append_wire a b)).reindex_exists
  refine ⟨e i, fun x y => ?_⟩
  obtain ⟨r, rfl⟩ := (index a).surjective x
  obtain ⟨s, rfl⟩ := (index b).surjective y
  have hp : index (a + b) (appendWord a b s r) = (rowIndex a b).symm (index a r, index b s) :=
    Fin.ext (append_value a b r s)
  rw [← hp, code_addr, code_addr, code_addr,
    show appendWord a b s r = reindex e (r, s) from congrFun he (r, s), bits_reindex]
  cases e i <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

/-!
# Simultaneous expansion of host neighborhoods

For one fixed walk use one batched indirect read per step. Add the
costs before estimating the degree, so the exponent of the overhead
is independent of the walk length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
open Coloring

variable (F : Type) [Field F] {m d q t : ℕ}

theorem width (hm : m ≤ t) (hd : 2 ^ d ≤ t) :
    (Rows m d).width ≤ 2 ^ m * (100 + t) ^ 2 := by
  simp only [Rows, Format.width_vec, Format.width_addr]
  apply Nat.mul_le_mul_left
  nlinarith only [Nat.mul_le_mul hd hm]

private theorem perm_width (hm : m ≤ t) :
    (Perm m).width ≤ 2 ^ m * (100 + t) ^ 2 := by
  simp only [Perm, Format.width_vec, Format.width_addr]
  apply Nat.mul_le_mul_left
  nlinarith

theorem column (hm : m ≤ t) (hd : 2 ^ d ≤ t) (i : B d) :
    Cheap F m t (Rows m d) (Perm m) (fun g x => g x i) 3 := by
  exact Cheap.project F (width hm hd) (perm_width hm) (fun z => (z.1, i, z.2)) fun _ _ => rfl

private theorem walk_cost (hm : m ≤ t) (hd : 2 ^ d ≤ t) (r : ℕ) (hr : r ≤ t) (w : Walk d r) :
    Cheap F m t (Rows m d) (Perm m) (fun g => run g r w) 10 := by
  let c := 2 ^ m * (100 + t) ^ 8
  have col (i : B d) : Cheap F m t (Rows m d) (Perm m) (fun g x => g x i) 8 :=
    (column F hm hd i).mono (by decide)
  obtain ⟨_, _, hc⟩ := col 0
  have hw : (Rows m d).width + (Perm m).width ≤ c := by unfold c; omega
  have bound {A D : Format} {f : A.obj → D.obj} (k : Cheap F m t A D f 8) :
      Circuit F A D f c := by
    obtain ⟨_, hk, hc⟩ := k
    exact hk.mono (by unfold c; omega)
  have get := bound (Cheap.lookup F m t (.addr m) hm (by simpa))
  have aux (a : ℕ) (l : Walk d a) :
      Circuit F (Rows m d) (Perm m) (fun g => run g a l) ((1 + 7 * a) * c) := by
    induction a with
    | zero =>
      rw [Nat.mul_zero, Nat.add_zero, Nat.one_mul]
      exact bound ((Cheap.const F (width hm hd) (perm_width hm) id).mono (by decide))
    | succ a ih =>
      obtain ⟨_|i, l⟩ := l
      · exact (ih l).mono (by gcongr; omega)
      · refine (((ih l).pair (bound (col i))).comp get).mono ?_
        rw [show (1 + 7 * (a + 1)) * c = (1 + 7 * a) * c + 7 * c by ring]
        omega
  refine ⟨_, aux r w, ?_⟩
  calc
    _ ≤ c + (1 + 7 * r) * c := Nat.add_le_add_right hw _
    _ = c * (2 + 7 * r) := by ring
    _ ≤ c * (100 + t) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    _ = _ := by unfold c; rw [mul_assoc, ← pow_add]

private theorem dedup_cheap (ht : q + m ≤ t) (hq : 2 ^ q ≤ t) (x : B m) :
    Cheap F 0 t (Column q m) (Column q m) (dedup x) 120 := by
  have hm : m ≤ t := by omega
  have hj : q ≤ t := by omega
  have a := column_width q hm
  have b := column_width q hj
  have first := (cheap_first F q m).widen ht
  have mask := (first.pair (Cheap.const F a b id)).zip.comp
    (Cheap.map _ (fun _ => cheap_eq F hj))
  have pair := ((Cheap.id F a).pair (Cheap.const F a a (fun _ => x))).zip
  have pick := (pair.pair mask).zip.comp (Cheap.map _ (fun _ => (cheap_select F m).widen hm))
  have h : Cheap F q t (Column q m) (Column q m) (dedup x) 119 := by
    convert pick.mono (d := 119) (by decide) using 1
    funext a i
    simp [dedup]
  obtain ⟨s, hs, hc⟩ := h
  refine ⟨s, hs, hc.trans ?_⟩
  rw [pow_zero, one_mul, show (100 + t) ^ 120 = (100 + t) * (100 + t) ^ 119 from pow_succ' _ _]
  exact Nat.mul_le_mul_right _ (by omega)

theorem cheap_walks (m d r : ℕ) (hr : 0 < r) :
    Cheap F m (m + 2 ^ ((d + 1) * r)) (Rows m d) (Rows m ((d + 1) * r)) (walks r) 20 := by
  let q := (d + 1) * r
  let t := m + 2 ^ q
  have hm : m ≤ t := Nat.le_add_right _ _
  have hq : 2 ^ q ≤ t := Nat.le_add_left _ _
  have hd : 2 ^ d ≤ t := (Nat.pow_le_pow_right (by decide) (show d ≤ q from
    (Nat.le_succ d).trans (Nat.le_mul_of_pos_right _ hr))).trans hq
  have ht : q + m ≤ t := by have := Nat.lt_pow_self (n := q) (by decide : 1 < 2); omega
  have hr' : r ≤ t := (Nat.le_mul_of_pos_left r (by omega : 0 < d + 1)).trans (by omega)
  have all := Cheap.share _ (fun i => walk_cost F hm hd r hr' (path d r i)) hq
  have a : (Format.vec q (Perm m)).width ≤ 2 ^ m * (100 + t) ^ 2 := by
    simpa only [Rows, Perm, Format.width_vec, mul_left_comm (2 ^ q)] using width hm hq
  have transpose : Cheap F m t (.vec q (Perm m)) (Rows m q) (fun g i j => g j i) 3 :=
    Cheap.project F a (width hm hq) (fun z => (z.2.1, z.1, z.2.2)) fun _ _ => rfl
  exact (all.comp transpose).mono (by decide)

theorem cheap (m d r : ℕ) (hr : 0 < r) :
    Cheap F m (m + 2 ^ ((d + 1) * r)) (Rows m d) (Rows m ((d + 1) * r)) (expand r) 200 := by
  let q := (d + 1) * r
  let t := m + 2 ^ q
  have hq : 2 ^ q ≤ t := Nat.le_add_left _ _
  have ht : q + m ≤ t := by have := Nat.lt_pow_self (n := q) (by decide : 1 < 2); omega
  exact ((cheap_walks F m d r hr).comp (Cheap.map _ (dedup_cheap F ht hq))).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
end

/-!
# Neighborhood expansion without replicating long names at each block
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring

variable {F : Type} [Field F] {I : Type*} {A : Format} {u m d h v n : ℕ}
  {L : Set (Table F)} (r : ℕ)

local notation "q" => ((d + 1) * r)
local notation "Data" => (Format.vec h A)
local notation "Old" => (Fmt.rows m d h A)
local notation "New" => (Fmt.rows m d h (Format.vec q A))
local notation "Names" => (Neighborhood.Rows m d)
local notation "Bank" => (Fmt.bank m q Data)
local notation "Views" => (Format.vec m (Format.vec q Data))

def Fmt.expand (x : (Old).obj) : (New).obj :=
  fun i => ((x i).1, fun b j => (x (Neighborhood.expand r (fun k => (x k).1) i j)).2 b)

private def rebank (x : (Old).obj) : (Bank).obj :=
  fun i => (Neighborhood.expand r (fun k => (x k).1) i, (x i).2)

private theorem prepare (hr : 0 < r) :
    Circuit F Old (.pair Names Bank) (fun x => (fun i => (x i).1, rebank r x))
      (40 * ((Old).width + 2 ^ m * (100 + (m + 2 ^ q)) ^ 200)) := by
  let E := Neighborhood.Rows m q
  let D := Format.vec m Data
  have a : Circuit F Old Names (fun x i => (x i).1) ((Old).width + 2 * (Names).width) :=
    Circuit.project (fun x => (x.1, .inl x.2)) (fun _ _ => rfl)
  have b : Circuit F Old D (fun x i => (x i).2) ((Old).width + 2 * D.width) :=
    Circuit.project (fun x => (x.1, .inr x.2)) (fun _ _ => rfl)
  have zip : Circuit F (.pair E D) Bank (fun x i => (x.1 i, x.2 i))
      ((E.pair D).width + 2 * (Bank).width) :=
    Circuit.project (Equiv.prodSumDistrib _ _ _) (by rintro x ⟨i, j|j⟩ <;> rfl)
  obtain ⟨s, hs, h⟩ := Neighborhood.cheap F m d r hr
  have hX : (Old).width = (Names).width + D.width := by
    simp only [Fmt.rows, D, Neighborhood.Rows, Format.width_vec, Format.width_pair, mul_add]
  have hB : (Bank).width = E.width + D.width := by
    simp only [Fmt.bank, E, D, Neighborhood.Rows, Format.width_vec, Format.width_pair, mul_add]
  change (Names).width + E.width + s ≤ _ at h
  refine (a.pair (((a.comp hs).pair b).comp zip)).mono ?_
  rw [Format.width_pair]
  omega

private def receive (x : (Format.pair Names Views).obj) : (New).obj :=
  fun i => (x.1 i, fun b j => x.2 i j b)

private theorem receive_circuit : Circuit F (.pair Names Views) New (receive r)
    ((Format.pair Names Views).width + 2 * (New).width) := by
  let e (i : (New).pins) : (Format.pair Names Views).pins :=
    i.2.elim (fun j => .inl (i.1, j)) (fun j => .inr (i.1, j.2.1, j.1, j.2.2))
  exact Circuit.project e (by rintro x ⟨i, j|j⟩ <;> rfl)

def expandCost (m d h r v n : ℕ) (A : Format) :=
  200 * ((Fmt.rows m d h A).width + (Fmt.rows m d h (.vec ((d + 1) * r) A)).width +
    2 ^ m * (100 + (m + 2 ^ ((d + 1) * r))) ^ 200) + gatherCost m ((d + 1) * r) v n

theorem computes_expand (hu : 3 ≤ u) (hr : 0 < r) (ht : Access F u L (m + q) v n)
    (hv : (Data).width ≤ v) (X : I → (Old).obj) (hx : ∀ i, Fmt.Reciprocal Data (X i)) :
    Computes F u L Old New X (fun i => Fmt.expand r (X i)) (fun _ => 1)
      (expandCost m d h r v n A) := by
  have pre := Computes.of_map (L := L) (x := X) (Map.circuit hu
    (prepare (F := F) (m := m) (d := d) (h := h) (A := A) r hr)) (fun _ => rfl)
  have hget := gather_neighbors (L := L) Data hu ht hv (fun i => rebank r (X i))
    (fun i => Neighborhood.reciprocal (hx i) r (fun j => (X i j).2))
  have keep := Computes.of_map (L := L) (x := fun i j => (X i j).1)
    (Map.circuit hu (Circuit.id F Names)) (fun _ => rfl)
  have xy := pre.comp (keep.par hget)
  have hpost := xy.comp (Computes.of_map (Map.circuit hu (receive_circuit r)) (fun _ => rfl))
  simp only [mul_one] at hpost
  refine hpost.mono ?_
  have hN : (New).width = (Names).width + (Views).width := by
    simp only [Fmt.rows, Neighborhood.Rows, Format.width_vec, Format.width_pair, mul_add]
    rw [mul_left_comm (2 ^ h)]
  unfold expandCost
  rw [Format.width_pair]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Short adjacency masks

Each entry compares a neighbor of a listed host against a second
listed host. Batched reads pay for the long addresses only while
preparing the masks.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
open Coloring

abbrev Mask (m q d : ℕ) := Format.vec m (.vec q (.vec d (.vec q .bit)))

variable {m q d t : ℕ}

def maskRows (u : B m → B q → B m) (g : B m → B d → B m) (x : B m)
    (i : B q) (j : B d) (k : B q) := decide (g (u x i) j = u x k)

def mask (r : ℕ) (g : B m → B d → B m) := maskRows (expand r g) g

variable (F : Type) [Field F]

theorem cheap_maskRows (hm : m ≤ t) (hq : 2 ^ q ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F m t (.pair (Rows m q) (Rows m d)) (Mask m q d)
      (fun x => maskRows x.1 x.2) 24 := by
  let A := Format.pair (Rows m q) (Rows m d)
  have ha : A.width ≤ 2 ^ m * (100 + t) ^ 3 := by
    have h := Nat.add_le_add (width hm hq) (width hm hd)
    rw [← Format.width_pair, ← mul_add] at h
    apply h.trans
    apply Nat.mul_le_mul_left
    ring_nf
    omega
  have base := Cheap.id F ha
  have col (i : B q) := base.fst.comp (column F hm hq i)
  have atHost (j : B d) := base.snd.comp (column F hm hd j)
  have get := Cheap.lookup F m t (.addr m) hm (by simpa)
  have bit (i : B q) (j : B d) (k : B q) :
      Cheap F m t A (.vec m .bit) (fun a x => maskRows a.1 a.2 x i j k) 14 := by
    have name := ((atHost j).pair (col i)).comp get
    exact ((name.pair (col k)).zip.comp (Cheap.map _ (fun _ => cheap_eq F hm))).mono (by decide)
  have all := Cheap.share _ (fun i => Cheap.share _ (fun j => Cheap.share _ (bit i j) hq) hd) hq
  let D := Format.vec q (.vec d (.vec q (.vec m .bit)))
  have hw : (Mask m q d).width ≤ 2 ^ m * (100 + t) ^ 3 := by
    simp only [Mask, Format.width_vec]
    rw [Format.width_bit, mul_one]
    apply Nat.mul_le_mul_left
    calc
      _ ≤ t * (t * t) := Nat.mul_le_mul hq (Nat.mul_le_mul hd hq)
      _ ≤ _ := by ring_nf; omega
  have he : D.width = (Mask m q d).width := by
    simp only [D, Mask, Format.width_vec]
    ring
  have reorder : Cheap F m t D (Mask m q d) (fun a x i j k => a i j k x) 4 :=
    Cheap.project F (he.le.trans hw) hw (fun z => (z.2.1, z.2.2.1, z.2.2.2.1, z.1, z.2.2.2.2))
      fun _ _ => rfl
  exact (all.comp reorder).mono (by decide)

theorem cheap_mask (m d r : ℕ) (hr : 0 < r) :
    Cheap F m (m + 2 ^ ((d + 1) * r)) (Rows m d) (Mask m ((d + 1) * r) d) (mask r) 220 := by
  let q := (d + 1) * r
  let t := m + 2 ^ q
  have hm : m ≤ t := Nat.le_add_right _ _
  have hq : 2 ^ q ≤ t := Nat.le_add_left _ _
  have hd : 2 ^ d ≤ t := (Nat.pow_le_pow_right (by decide) (show d ≤ q from
    (Nat.le_succ d).trans (Nat.le_mul_of_pos_right _ hr))).trans hq
  have args := (cheap F m d r hr).pair (Cheap.id F (width hm hd))
  exact (args.comp (cheap_maskRows F hm hq hd)).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
end

/-!
# Weighted updates on two nested neighborhoods

Use one lookup table shared at every occurrence. Expanded views
are temporary; only the output records and original host graph
are carried across the stage boundary.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} [Field F] {I : Type*} {A C D : Format} {m d h u r t v n v' n' : ℕ}
  {L : Set (Table F)}

abbrev Fmt.view (d r : ℕ) (A : Format) := Format.vec ((d + 1) * r) A
abbrev Fmt.wave (d r t : ℕ) (A C : Format) := view d t (view d r (A.pair C))
abbrev Fmt.waveIn (m d h : ℕ) (A C : Format) := (rows m d h A).pair (.vec m (.vec h C))

def Fmt.around (r t : ℕ) (x : (waveIn m d h A C).obj) :
    (rows m d h (wave d r t A C)).obj := expand t (expand r (zip x))

def waveCost (m d h r t v n v' n' : ℕ) (A C D : Format) :=
  12 * (Fmt.rows m d h (A.pair C)).width + expandCost m d h r v n (A.pair C) +
    expandCost m d h t v' n' (Fmt.view d r (A.pair C)) + updateCost m d h (Fmt.wave d r t A C) D

theorem computes_wave (hu : 3 ≤ u) (hr : 0 < r) (ht : 0 < t)
    (h₁ : Access F u L (m + (d + 1) * r) v n) (h₂ : Access F u L (m + (d + 1) * t) v' n')
    (hv : (Format.vec h (A.pair C)).width ≤ v)
    (hv' : (Format.vec h (Fmt.view d r (A.pair C))).width ≤ v')
    (f : (Fmt.wave d r t A C).obj → D.obj) (g : (Fmt.wave d r t A C).obj → F)
    (hw : (Fmt.wave d r t A C).width + D.width ≤ u) (hg : weightTable f g ∈ L)
    (X : I → (Fmt.waveIn m d h A C).obj) (hx : ∀ i, Fmt.Reciprocal (.vec h A) (X i).1) :
    Computes F u L (Fmt.waveIn m d h A C) (Fmt.rows m d h D)
      X (fun i => Fmt.update f (Fmt.around r t (X i))) (fun i => Fmt.weight g (Fmt.around r t (X i)))
      (waveCost m d h r t v n v' n' A C D) := by
  have p := Computes.of_map (L := L) (x := X)
    (map_zip (m := m) (d := d) (h := h) (A := A) (D := C) hu) (fun _ => rfl)
  have q := computes_expand (L := L) r hu hr h₁ hv (fun i => Fmt.zip (X i)) hx
  have w := computes_expand (L := L) t hu ht h₂ hv' (fun i => Fmt.expand r (Fmt.zip (X i))) hx
  have a := computes_update f g hu hw hg (fun i => Fmt.around r t (X i))
  have out := ((p.comp q).comp w).comp a
  simp only [one_mul, Function.comp_def] at out
  exact out

end OAI.LinearAlgebra.MatrixExponent.Assembly
end
