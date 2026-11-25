import OAI.LinearAlgebra.MatrixExponent.AdjacentDuplicates
import Mathlib.Data.Prod.Lex
import OAI.LinearAlgebra.MatrixExponent.BitonicMerge
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute
import OAI.LinearAlgebra.MatrixExponent.Diagram.Wide
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.LinearAlgebra.MatrixExponent.Diagram.Substitute
import OAI.LinearAlgebra.MatrixExponent.Tagged.Tags
import OAI.LinearAlgebra.MatrixExponent.CompareExchange

section
/-!
# Checking sorted order with linear overhead

Each subtree reports its first and last rows and a bit saying whether
it is sorted. A join compares just the two adjacent endpoints.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {F : Type} [Field F] {a : Wire} [LinearOrder (Val a)]

private abbrev Frame (a : Wire) := Wire.pair (.pair a a) .bit

private def join (x : Val (.pair (Frame a) (Frame a))) : Val (Frame a) :=
  ((x.1.1.1, x.2.1.2), (x.1.2 && x.2.2) && !decide (x.2.1.1 < x.1.1.2))

private def frame : (w : ℕ) → Val (tree w a) → Val (Frame a)
  | 0, x => ((x, x), true)
  | w + 1, x => join (frame w x.1, frame w x.2)

private theorem frame_correct (w : ℕ) (x : Val (tree w a)) :
    let q := frame w x
    let L := flatten w x
    q.1.1 ∈ L ∧ q.1.2 ∈ L ∧ (q.2 = true ↔ L.Pairwise (· ≤ ·)) ∧
      (q.2 = true → ∀ z ∈ L, q.1.1 ≤ z ∧ z ≤ q.1.2) := by
  induction w with
  | zero => simp [frame, flatten]
  | succ w ih =>
    obtain ⟨h₁, h₂, hl, bl⟩ := ih x.1
    obtain ⟨h₃, h₄, hr, br⟩ := ih x.2
    simp only [frame, join, flatten, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      not_lt, List.pairwise_append]
    refine ⟨List.mem_append_left _ h₁, List.mem_append_right _ h₄, ?_, ?_⟩
    · constructor
      · rintro ⟨⟨l, r⟩, q⟩
        exact ⟨hl.mp l, hr.mp r, fun y hy z hz => ((bl l y hy).2.trans q).trans (br r z hz).1⟩
      · rintro ⟨l, r, q⟩
        exact ⟨⟨hl.mpr l, hr.mpr r⟩, q _ h₂ _ h₃⟩
    · rintro ⟨⟨l, r⟩, q⟩ z hz
      rcases List.mem_append.mp hz with h | h
      · exact ⟨(bl l z h).1, ((bl l z h).2.trans q).trans (br r _ h₃).2⟩
      · exact ⟨((bl l _ h₂).1.trans q).trans (br r z h).1, (br r z h).2⟩

variable {k : ℕ} (p : DNet F (.pair a a) .bit (fun x => decide (x.1 < x.2)) k)

include p in
private theorem join_net : DNet F (.pair (Frame a) (Frame a)) (Frame a) join (2 * wd a + k + 2) := by
  let e := Wire.pair a a
  let b := Wire.pair .bit .bit
  have ends := (((Rewire.id e).par (.swap a a)).comp (.middle a a a a)).comp
    ((Rewire.id e).par (.swap a a))
  have r := ((Rewire.middle e .bit e .bit).comp (ends.par (.id b))).comp (.assoc e e b)
  have both := DNet.table F b .bit (fun x => x.1 && x.2) (by decide)
  have ok := DNet.table F b .bit (fun x => x.2 && !x.1) (by decide)
  exact (((DNet.id F e).par ((p.par both).comp ok)).pre r).mono (by simp [e, wd]; omega)

include p in
private theorem frame_net (w : ℕ) :
    ∃ m, DNet F (tree w a) (Frame a) (frame w) m ∧
      m + (2 * wd a + k + 2) ≤ 2 ^ w * (3 * wd a + k + 3) := by
  induction w with
  | zero =>
    have yes := DNet.table F .unit .bit (fun _ => true) (by decide)
    exact ⟨_, ((DNet.dup F a).par yes).pre (.unit' a), by simp; omega⟩
  | succ w ih =>
    obtain ⟨m, h, hm⟩ := ih
    refine ⟨_, (h.par h).comp (join_net p), ?_⟩
    rw [pow_succ, mul_two, add_mul]
    omega

include p in
theorem check_order (w : ℕ) :
    DNet F (tree w a) .bit (fun x => decide ((flatten w x).Pairwise (· ≤ ·)))
      (2 ^ w * (3 * wd a + k + 3)) := by
  obtain ⟨m, h, hm⟩ := frame_net p w
  have net := h.comp (DNet.snd F (.pair a a) .bit)
  have eq (x : Val (tree w a)) : (frame w x).2 = decide ((flatten w x).Pairwise (· ≤ ·)) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    exact (frame_correct w x).2.2.1
  simpa only [eq] using net.mono (n := 2 ^ w * (3 * wd a + k + 3)) (by simp only [wd]; omega)

include p in
/-- Two comparisons of the first component and one of the second suffice. -/
theorem lex_compare {b : Wire} [LinearOrder (Val b)] {l : ℕ}
    (q : DNet F (.pair b b) .bit (fun x => decide (x.1 < x.2)) l) :
    DNet F (.pair (.pair a b) (.pair a b)) .bit (fun x => decide (toLex x.1 < toLex x.2))
      (2 * wd a + 2 * k + l + 3) := by
  have cmp := ((p.pair (p.pre (.swap a a))).par q).pre (.middle a b a b)
  have h := DNet.table F (.pair .bit .bit) .bit (fun x => !x.1 && x.2) (by decide)
  have g := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 || x.2) (by decide)
  have net := (cmp.post (.assoc .bit .bit .bit)).comp (((DNet.id F .bit).par h).comp g)
  convert net.mono (n := 2 * wd a + 2 * k + l + 3) (by simp only [wd]; omega) using 1
  funext ⟨x, y⟩
  clear cmp h g net p q
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, Prod.Lex.toLex_lt_toLex]
  grind

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-!
# Array layouts on bundles of bits

A layout partitions the exterior positions into disjoint copies of a
record. Any permutation of records induces a free bit permutation.
-/

namespace OAI.LinearAlgebra.MatrixExponent

structure Layout (a b : Wire) (I : Type) where
  positions : I × slots a ≃ slots b

namespace Layout

variable {a b c : Wire} {I J : Type} {m n : ℕ}

def read (L : Layout a b I) (x : Val b) (i : I) : Val a :=
  (bits a).symm (fun k => bits b x (L.positions (i, k)))

theorem injective (L : Layout a b I) : Function.Injective L.read := by
  intro x y h
  apply (bits b).injective
  funext j
  obtain ⟨⟨i, k⟩, rfl⟩ := L.positions.surjective j
  exact congrFun ((bits a).symm.injective (congrFun h i)) k

theorem rewire (L : Layout a b I) (M : Layout a c J) (e : J ≃ I) :
    ∃ f, Rewire b c f ∧ ∀ x, M.read (f x) = L.read x ∘ e := by
  let p := M.positions.symm.trans ((e.prodCongr (.refl _)).trans L.positions)
  refine ⟨reindex p, rewire_reindex p, fun x => ?_⟩
  funext i
  simp [read, p]

def nest (L : Layout b c I) (M : Layout a b J) : Layout a c (I × J) :=
  ⟨(Equiv.prodAssoc _ _ _).trans (((Equiv.refl I).prodCongr M.positions).trans L.positions)⟩

theorem read_nest (L : Layout b c I) (M : Layout a b J) (x : Val c) (i : I) (j : J) :
    (L.nest M).read x (i, j) = M.read (L.read x i) j := by
  simp [read, nest]

private def one (a : Wire) : Layout a a (Fin 1) := ⟨Equiv.uniqueProd _ _⟩

private theorem read_one (x : Val a) (i : Fin 1) : (one a).read x i = x :=
  (bits a).symm_apply_apply x

private def pair (L : Layout a b (Fin m)) (M : Layout a c (Fin n)) :
    Layout a (.pair b c) (Fin (m + n)) :=
  ⟨(finSumFinEquiv.symm.prodCongr (.refl _)).trans
    ((Equiv.sumProdDistrib _ _ _).trans (L.positions.sumCongr M.positions))⟩

private theorem read_pair_left (L : Layout a b (Fin m)) (M : Layout a c (Fin n))
    (x : Val (.pair b c)) (i : Fin m) :
    (L.pair M).read x (i.castAdd n) = L.read x.1 i := by
  unfold read
  apply congrArg
  funext k
  change bits (.pair b c) x ((L.pair M).positions (finSumFinEquiv (.inl i), k)) = _
  simp only [pair, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.symm_apply_apply]
  rfl

private theorem read_pair_right (L : Layout a b (Fin m)) (M : Layout a c (Fin n))
    (x : Val (.pair b c)) (i : Fin n) :
    (L.pair M).read x (i.natAdd m) = M.read x.2 i := by
  unfold read
  apply congrArg
  funext k
  change bits (.pair b c) x ((L.pair M).positions (finSumFinEquiv (.inr i), k)) = _
  simp only [pair, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.symm_apply_apply]
  rfl

theorem exists_tree (a : Wire) (w : ℕ) :
    ∃ L : Layout a (tree w a) (Fin (2 ^ w)), ∀ x, List.ofFn (L.read x) = flatten w x := by
  induction w with
  | zero =>
    refine ⟨one a, fun x => ?_⟩
    change List.ofFn ((one a).read x) = [x]
    simp [read_one]
  | succ w ih =>
    obtain ⟨L, hL⟩ := ih
    rw [pow_succ, mul_two]
    refine ⟨L.pair L, fun x => ?_⟩
    rw [List.ofFn_add]
    change List.ofFn (fun i => (L.pair L).read x (Fin.castAdd _ i)) ++
      List.ofFn (fun i => (L.pair L).read x (Fin.natAdd _ i)) = _
    simp only [read_pair_left, read_pair_right, hL, flatten]

theorem read_sort [LinearOrder (Val a)] {w : ℕ} (L : Layout a (tree w a) (Fin n))
    (hL : ∀ x, List.ofFn (L.read x) = flatten w x) (x : Val (tree w a)) :
    L.read (sortTree w x) = L.read x ∘ Tuple.sort (L.read x) := by
  apply List.ofFn_injective
  rw [hL]
  apply List.Perm.eq_of_pairwise' (sortTree_sorted ..)
    (Tuple.monotone_sort _).sortedLE_ofFn.pairwise
  exact (sortTree_perm ..).trans (by rw [← hL]; exact (Equiv.Perm.ofFn_comp_perm ..).symm)

theorem exists_copies (a : Wire) (n : ℕ) :
    ∃ L : Layout a (copies a n) (Fin n),
      ∀ (f : Val a → Val a) x, L.read (mapCopies f n x) = f ∘ L.read x := by
  induction n with
  | zero => exact ⟨⟨Equiv.equivEmpty _⟩, fun _ _ => funext fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨L, hL⟩ := ih
    have h : ∃ K : Layout a (copies a (n + 1)) (Fin (1 + n)),
        ∀ (f : Val a → Val a) x, K.read (mapCopies f (n + 1) x) = f ∘ K.read x := by
      refine ⟨(one a).pair L, fun f x => ?_⟩
      funext i
      induction i using Fin.addCases with
      | left i => simp only [Function.comp_apply, mapCopies, read_pair_left, read_one]
      | right i => simp only [Function.comp_apply, mapCopies, read_pair_right, hL]
    rwa [Nat.add_comm 1 n] at h

end Layout
end OAI.LinearAlgebra.MatrixExponent
end

section
/-! # Substituting a batch of independent queries -/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {F : Type} [Field F] {a b c d : Wire}

/-- Batch size counts vertices only. Powers have disjoint exterior bits. -/
def Batch (k : Val a → Val b → F) (t m : ℕ) : Prop :=
  ∃ v ≤ m, Net F (copies a t) (copies b t) (power k t) v

namespace Batch

variable {k : Val a → Val b → F} {m n t : ℕ}

theorem mono (h : Batch k t m) (hm : m ≤ n) : Batch k t n := by
  obtain ⟨v, hv, h⟩ := h
  exact ⟨v, hv.trans hm, h⟩

theorem of_net (h : Net F a b k m) (t : ℕ) : Batch k t (t * m) :=
  ⟨_, le_rfl, h.power t⟩

theorem comp {l : Val b → Val c → F} (h : Batch k t m) (g : Batch l t n) :
    Batch (fun x z => ∑ y, k x y * l y z) t (m + n) := by
  obtain ⟨v, hv, h⟩ := h
  obtain ⟨u, hu, g⟩ := g
  exact ⟨v + u, Nat.add_le_add hv hu, by simpa only [← power_comp] using h.comp g⟩

theorem par {l : Val c → Val d → F} (h : Batch k t m) (g : Batch l t n) :
    Batch (a := .pair a c) (b := .pair b d) (fun x y => k x.1 y.1 * l x.2 y.2) t (m + n) := by
  obtain ⟨v, hv, h⟩ := h
  obtain ⟨u, hu, g⟩ := g
  exact ⟨v + u, Nat.add_le_add hv hu,
    (h.par g).rewire (.zipCopies _ _ _) (.zipCopies _ _ _) (power_zip k l t)⟩

theorem pullback {f : Val c → Val a} (h : Batch k t m) (g : DNet F c a f n) :
    Batch (fun x y => k (f x) y) t (t * n + m) := by
  obtain ⟨u, hu, g⟩ := g
  have h' := ((of_net g t).mono (Nat.mul_le_mul_left t hu)).comp h
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h'

theorem par_pred {k : Val a → Val .unit → F} {l : Val b → Val .unit → F}
    (h : Batch k t m) (g : Batch l t n) :
    Batch (a := .pair a b) (b := .unit) (fun x y => k x.1 y * l x.2 y) t (m + n) := by
  obtain ⟨v, hv, h⟩ := h.par g
  exact ⟨v, hv, h.rewire ((Rewire.id _).mapCopies t) ((Rewire.unit .unit).mapCopies t)
    (power_map (fun _ _ => rfl) t)⟩

end Batch
end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-!
# Preparing distinctness queries

The input and proposed output each occupy half a list. A real record has
flag zero. When excluded from the signed subset, a record changes only
its flag. Its position tag still distinguishes it from every other dummy.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {F : Type} [Field F] {a b c : Wire} {m : ℕ}

theorem literal_net (F : Type) [Field F] (a : Wire) (x : Val a) :
    DNet F .unit a (fun _ => x) (wd a) := by
  induction a with
  | bit => exact .table F .unit .bit _ (by decide)
  | unit => exact DNet.id F .unit
  | pair a b ha hb => exact ((ha x.1).par (hb x.2)).pre (.unit' _)

theorem mapRows_net {f : Val a → Val b} (h : DNet F a b f m) (w : ℕ) :
    DNet F (tree w a) (tree w b) (mapRows f w) (2 ^ w * m) := by
  induction w with
  | zero => rw [pow_zero, one_mul]; exact h
  | succ w ih =>
    rw [pow_succ, mul_two, add_mul]
    exact ih.par ih

theorem zipRows_net {f : Val a → Val b → Val c} (h : DNet F (.pair a b) c (Function.uncurry f) m)
    (w : ℕ) : DNet F (.pair (tree w a) (tree w b)) (tree w c)
      (fun x => zipRows f w x.1 x.2) (2 ^ w * m) := by
  induction w with
  | zero => rw [pow_zero, one_mul]; exact h
  | succ w ih =>
    rw [pow_succ, mul_two, add_mul]
    exact (ih.par ih).pre (.middle _ _ _ _)

theorem label_net (F : Type) [Field F] (w : ℕ) (a : Wire) :
    DNet F (tree w a) (tree w (row w a)) (label w) (2 ^ w * (2 * (w + wd a))) := by
  have h := ((DNet.id F (tree w a)).par (literal_net F _ (indices w))).pre (.unit' _)
  have k := (DNet.id F (.pair a (word w))).post (.swap _ _)
  refine (h.comp (zipRows_net (c := row w a) (f := fun y i => (i, y)) k w)).mono ?_
  simp only [wd_tree, wd_word, wd]
  exact le_of_eq (by ring)

theorem sign_net (F : Type) [Field F] (w : ℕ) :
    Net F .unit (tree w .bit) (fun _ z => sign F w z) (2 ^ w) := by
  induction w with
  | zero => exact .table _ _ _ (by decide)
  | succ w ih =>
    rw [pow_succ, mul_two]
    exact (ih.par ih).pre (.unit' _)

variable {w : ℕ} (E : Val .bit → Val (row w a) → Val b)

private theorem test_net (h : Rewire (.pair .bit (row w a)) b (Function.uncurry E)) :
    DNet F (.pair (tree w .bit) (inputs w a)) (tree (w + 1) b)
      (fun y => tested E w (label w y.2.1) y.2.2 y.1)
      (2 ^ w * (4 * (w + wd a) + 3)) := by
  have mark := (DNet.id F _).post h
  have zero := (literal_net F .bit false).par (DNet.id F (row w a))
  have real := (zero.pre ((Rewire.unit' _).comp (.swap _ _))).post h
  have left := mapRows_net real w
  have right := ((DNet.id F (tree w .bit)).par (label_net F w a)).comp (zipRows_net mark w)
  refine ((left.par right).pre ((Rewire.assoc' _ _ _).comp (.swap _ _))).mono ?_
  simp only [wd_tree, wd, wd_word]
  exact le_of_eq (by ring)

/-- A linear map inserting the signed choice of flags. -/
def prepare (F : Type) [Field F] (x : Val (inputs w a)) (y : Val (tree (w + 1) b)) : F :=
  ∑ z : Val (tree w .bit), sign F w z * if tested E w (label w x.1) x.2 z = y then 1 else 0

theorem prepare_net (h : Rewire (.pair .bit (row w a)) b (Function.uncurry E)) :
    ∃ v ≤ 2 ^ w * (5 * w + 6 * wd a + 4), Net F (inputs w a) (tree (w + 1) b) (prepare E F) v := by
  obtain ⟨m, hm, ht⟩ := test_net (F := F) E h
  obtain ⟨v, hv, hid⟩ := DNet.id F (inputs w a)
  have k := ((sign_net F w).par hid).pre ((Rewire.unit' _).comp (.swap _ _))
  refine ⟨2 ^ w + v + m, ?_, ?_⟩
  · refine (Nat.add_le_add (Nat.add_le_add_left hv (2 ^ w)) hm).trans ?_
    simp only [wd, wd_tree, row, wd_word]
    exact le_of_eq (by ring)
  · convert k.comp ht using 1
    funext x y
    rw [Fintype.sum_prod_type]
    unfold prepare
    apply Finset.sum_congr rfl
    intro z _
    rw [Fintype.sum_eq_single x]
    · simp
    · intro x2 hne; simp [hne.symm]

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-!
# Sorting with a permutation verifier

Sum over proposed tagged outputs, retaining their payloads. Checking
order by payload and then by tag leaves exactly one witness, even when
some payloads coincide.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {F : Type} [Field F] {a b : Wire} {t m w k : ℕ}

private theorem cup (b : Wire) :
    Net F .unit (.pair b b) (fun _ y => if y.1 = y.2 then 1 else 0) (wd b) := by
  induction b with
  | bit => exact .table _ _ _ (by decide)
  | unit => exact Net.empty.post (.unit _)
  | pair b c ih ij =>
    have h := ((ih.par ij).pre (.unit' _)).post (.middle b c b c)
    simpa only [wd, Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul] using h

/-- Move the second block of exterior inputs to the output side. -/
theorem Batch.openInput {l : Val (.pair a b) → Val .unit → F} (h : Batch l t m) :
    Batch (a := a) (b := b) (fun x y => l (x, y) ()) t (m + t * wd b) := by
  obtain ⟨v, hv, h⟩ := h
  have e (d : ℕ) (x : Val (copies a d)) (y : Val (copies b d)) :
      power l d (zipCopies a b d (x, y)) (unitCopies d) =
        power (a := a) (b := b) (fun u z => l (u, z) ()) d x y := by
    induction d with
    | zero => rfl
    | succ d ih => simp only [power, zipCopies, unitCopies, ih]
  have h₁ := (h.pre (.zipCopies a b t)).post (.unitCopies t)
  have h₂ := (h₁.par (cup (F := F) (copies b t))).pre (.unit' _)
  have h₃ := (h₂.post ((Rewire.unit' _).comp (.swap _ _))).trace
  refine ⟨v + wd (copies b t), by rw [wd_copies]; omega, ?_⟩
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, e] using h₃

private theorem Batch.graph {f : Val a → Val b}
    (h : Batch (fun x y => if f x = y then (1 : F) else 0) t m) :
    DNet F (copies a t) (copies b t) (mapCopies f t) m := by
  obtain ⟨v, hv, h⟩ := h
  have e (d : ℕ) (x : Val (copies a d)) (y : Val (copies b d)) :
      power (fun s u => if f s = u then (1 : F) else 0) d x y =
        if mapCopies f d x = y then 1 else 0 := by
    induction d with
    | zero => rfl
    | succ d ih => simp only [power, mapCopies, Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul, ih]
  exact ⟨v, hv, by convert h using 1; funext x y; exact (e ..).symm⟩

theorem flatten_inj (w : ℕ) : Function.Injective (flatten (a := a) w) := by
  induction w with
  | zero => intro x y h; simpa [flatten] using h
  | succ w ih =>
    intro x y h
    obtain ⟨hl, hr⟩ := List.append_inj h (by rw [length_flatten, length_flatten])
    exact Prod.ext (ih hl) (ih hr)

variable [LinearOrder (Val a)]

theorem unique_sort (w : ℕ) (x y : Val (tree w a))
    (h : (flatten w y).Perm (flatten w x)) (hs : (flatten w y).Pairwise (· ≤ ·)) :
    y = sortTree w x :=
  flatten_inj w (List.Perm.eq_of_pairwise' hs (sortTree_sorted ..) (h.trans (sortTree_perm ..).symm))

private local instance rowOrder (w : ℕ) : LinearOrder (Val (row w a)) :=
  LinearOrder.lift' (fun z => toLex (z.2, z.1)) Prod.swap_injective

private local instance rowLT (w : ℕ) : LT (Val (row w a)) := (rowOrder w).toLT
private local instance rowLE (w : ℕ) : LE (Val (row w a)) := (rowOrder w).toLE

private theorem payload_le (x y : Val (row w a)) (h : x ≤ y) : x.2 ≤ y.2 := by
  rcases (Prod.Lex.toLex_le_toLex (x := x.swap) (y := y.swap)).mp h with h | h
  · exact h.le
  · exact h.1.le

private theorem row_compare (p : DNet F (.pair a a) .bit (fun x => decide (x.1 < x.2)) k)
    (w : ℕ) : DNet F (.pair (row w a) (row w a)) .bit (fun x => decide (x.1 < x.2))
      (2 * wd a + 2 * k + 100 * (w + 1) + 3) := by
  exact (lex_compare p (compare_lt F w)).pre ((Rewire.swap _ _).par (.swap _ _))

def payloads (w : ℕ) : Val (tree w (row w a)) → Val (tree w a) :=
  mapRows (a := row w a) Prod.snd w

omit [LinearOrder (Val a)] in
theorem label_payloads (w : ℕ) (x : Val (tree w a)) : payloads w (label w x) = x := by
  have aux (n : ℕ) (y : Val (tree n a)) (i : Val (tree n (word w))) :
      mapRows (a := row w a) (b := a) Prod.snd n
        (zipRows (c := row w a) (fun u v => (v, u)) n y i) = y := by
    induction n with
    | zero => rfl
    | succ n ih => exact Prod.ext (ih _ _) (ih _ _)
  exact aux w x (indices w)

private theorem sorted_payloads (w : ℕ) (x : Val (tree w a)) :
    payloads w (sortTree w (label w x)) = sortTree w x := by
  apply unique_sort
  · have h := (sortTree_perm w (label w x)).map Prod.snd
    simp only [payloads, flatten_mapRows]
    have he := congrArg (flatten w) (label_payloads w x)
    simp only [payloads, flatten_mapRows] at he
    rwa [he] at h
  · simp only [payloads, flatten_mapRows]
    exact (sortTree_sorted w (label w x)).map Prod.snd payload_le

private def keep (F : Type) [Field F] (w : ℕ) (a : Wire) [LinearOrder (Val a)]
    (x : Val (tree w (row w a))) (y : Val (tree w a)) : F :=
  if (flatten w x).Pairwise (· ≤ ·) ∧ payloads w x = y then 1 else 0

private theorem sort_sum (x y : Val (tree w a)) :
    (∑ z, tag F w a (x, z) () * keep F w a z y) = if sortTree w x = y then 1 else 0 := by
  rw [Fintype.sum_eq_single (sortTree w (label w x))]
  · simp only [tag, permuted, sortTree_perm w (label w x), ite_true, one_mul, keep,
      sortTree_sorted w (label w x), true_and,
      sorted_payloads]
  · intro z hz
    by_cases hp : (flatten w z).Perm (flatten w (label w x))
    · have hs : ¬ (flatten w z).Pairwise (· ≤ ·) :=
        fun hs => hz (unique_sort w _ z hp hs)
      simp [keep, hs]
    · simp [tag, permuted, hp]

private theorem keep_net (p : DNet F (.pair a a) .bit (fun x => decide (x.1 < x.2)) k)
    (w : ℕ) :
    ∃ v ≤ 500 * 2 ^ w * (wd a + w + k + 1), Net F (tree w (row w a)) (tree w a) (keep F w a) v := by
  have test := check_order (row_compare p w) w
  have proj := mapRows_net (DNet.snd F (word w) a) w
  obtain ⟨v, hv, h⟩ := proj.pair test
  have pin := Net.table (F := F) .bit .unit (fun x _ => if x = true then 1 else 0) (by decide)
  obtain ⟨u, hu, hid⟩ := DNet.id F (tree w a)
  have net := h.comp ((hid.par pin).post (.unit' _))
  refine ⟨v + (u + 1), ?_, ?_⟩
  · simp only [wd_tree, wd, wd_word] at hv hu
    have hp := Nat.one_le_pow w 2 (by decide)
    nlinarith
  · convert net using 1
    funext x y
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [decide_eq_true_eq, keep, payloads, ← ite_and, and_comm]
    rfl

/-- A batch of tagged permutation verifiers supplies the same number
of independent sorts with linear overhead in the cost of a comparison. -/
theorem sort_of_tag (h : Batch (tag F w a) t m)
    (p : DNet F (.pair a a) .bit (fun x => decide (x.1 < x.2)) k) :
    DNet F (copies (tree w a) t) (copies (tree w a) t) (mapCopies (sortTree w) t)
      (m + 1000 * t * 2 ^ w * (wd a + w + k + 1)) := by
  obtain ⟨v, hv, hkeep⟩ := keep_net p w
  have hh := h.openInput.comp (Batch.of_net hkeep t)
  simp only [sort_sum] at hh
  apply hh.graph.mono
  simp only [wd_tree, wd, wd_word]
  calc
    _ = m + t * (2 ^ w * (w + wd a) + v) := by ring
    _ ≤ m + t * (2 ^ w * (w + wd a) + 500 * 2 ^ w * (wd a + w + k + 1)) := by gcongr
    _ = m + t * 2 ^ w * ((w + wd a) + 500 * (wd a + w + k + 1)) := by ring
    _ ≤ m + t * 2 ^ w * (1000 * (wd a + w + k + 1)) := by gcongr; omega
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-!
# Verifying a permutation in payload slices

The positional tags are distinct, so two checks that agree on the tag
necessarily refer to the same input row.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {a b : Wire}

/-- Apply a function to both sets of payloads, preserving all tags. -/
def project (w : ℕ) (f : Val a → Val b) (x : Val (inputs w a)) : Val (inputs w b) :=
  (mapRows f w x.1,
   mapRows (a := row w a) (b := row w b) (Prod.map id f) w x.2)

private theorem flatten_label_map (w : ℕ) (f : Val a → Val b) (x : Val (tree w a)) :
    flatten w (label w (mapRows f w x)) =
      (flatten w (label w x)).map (Prod.map id f) := by
  have aux (n : ℕ) (y : Val (tree n a)) (i : Val (tree n (word w))) :
      flatten n (zipRows (c := row w b) (fun u v => (v, u)) n (mapRows f n y) i) =
        (flatten n (zipRows (c := row w a) (fun u v => (v, u)) n y i)).map (Prod.map id f) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [flatten, zipRows, mapRows, List.map_append, ih]
  exact aux w x (indices w)

theorem label_tags (w : ℕ) (x : Val (tree w a)) :
    (flatten w (label w x)).map Prod.fst = flatten w (indices w) := by
  have aux (n : ℕ) (y : Val (tree n a)) (i : Val (tree n (word w))) :
      (flatten n (zipRows (c := row w a) (fun u v => (v, u)) n y i)).map Prod.fst =
        flatten n i := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [flatten, zipRows, List.map_append, ih]
  exact aux w x (indices w)

private theorem perm_slices {ι α β : Type} (A B : List (ι × α × β))
    (hA : (A.map Prod.fst).Nodup) :
    B.Perm A ↔
      (B.map (Prod.map id Prod.fst)).Perm (A.map (Prod.map id Prod.fst)) ∧
      (B.map (Prod.map id Prod.snd)).Perm (A.map (Prod.map id Prod.snd)) := by
  constructor
  · exact fun h => ⟨h.map _, h.map _⟩
  rintro ⟨hl, hr⟩
  have hp : (B.map Prod.fst).Perm (A.map Prod.fst) := by
    simpa [List.map_map, Function.comp_def] using hl.map Prod.fst
  have hb := List.Nodup.of_map Prod.fst (hp.symm.nodup hA)
  have hi := (List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.fst hA)).mp hA
  have sub : B ⊆ A := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp (hl.subset (List.mem_map_of_mem hx))
    obtain ⟨z, hz, hxz⟩ := List.mem_map.mp (hr.subset (List.mem_map_of_mem hx))
    simp only [Prod.map, id_eq, Prod.mk.injEq] at hxy hxz
    have h : y = z := hi y hy z hz (hxy.1.trans hxz.1.symm)
    subst z
    have h : y = x := Prod.ext hxy.1 (Prod.ext hxy.2 hxz.2)
    exact h ▸ hy
  exact (hb.subperm sub).perm_of_length_le (by simpa using hl.length_eq.ge)

variable (F : Type) [Field F] (w : ℕ)

theorem tag_project (f : Val a → Val b) (hf : Function.Injective f)
    (x : Val (inputs w a)) (u : Val .unit) :
    tag F w b (project w f x) u = tag F w a x u := by
  have h : Function.Injective (Prod.map (id : Val (word w) → _) f) := by
    intro p q he
    simp only [Prod.map, id_eq, Prod.mk.injEq] at he
    exact Prod.ext he.1 (hf he.2)
  simp only [tag, permuted, project, flatten_mapRows, flatten_label_map, List.map_perm_map_iff h]

theorem tag_pair (a b : Wire) (x : Val (inputs w (.pair a b))) (u : Val .unit) :
    tag F w (.pair a b) x u =
      tag F w a (project (a := .pair a b) w Prod.fst x) u *
      tag F w b (project (a := .pair a b) w Prod.snd x) u := by
  have h := perm_slices (flatten w (label w x.1)) (flatten w x.2)
    (by rw [label_tags w x.1]; exact indices_nodup w)
  simp only [tag, permuted, project, flatten_mapRows, flatten_label_map, h, ite_and,
    ite_mul, one_mul, zero_mul]

end OAI.LinearAlgebra.MatrixExponent.Tagged
end
