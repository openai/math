import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Coloring.Add
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Assembly.Matching
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute

section
/-!
# Gathering pointers for packed intervals

Each record gives an inclusive start, exclusive end, and translation
modulo the address space. Empty or reversed intervals are inactive.
After sorting the starts, all queries run a parallel binary search.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Intervals
open Coloring
noncomputable section
variable {h j k : ℕ}

abbrev span (k : ℕ) := Format.pair (.addr k) (.pair (.addr k) (.addr k))

def contains (v : (span k).obj) (b : B k) : Prop := v.1 ≤ b ∧ b < v.2.1

def key (v : (span k).obj) : B k := if v.1 < v.2.1 then v.1 else ⊤

def get (q pad : B k) (v : (span k).obj) : B k :=
  if q < v.1 then pad else if q < v.2.1 then q + v.2.2 else pad

def jump (d : ℕ) (i : B h) : B h :=
  if e : i.val + 2 ^ d < 2 ^ h then ⟨i.val + 2 ^ d, e⟩ else i

def seek (a : B h → B k) (q : B k) : ℕ → B h → B h
  | 0, i => i
  | d + 1, i => seek a q d (if q < a (jump d i) then i else jump d i)

private theorem seek_ok (a : B h → B k) (ha : Monotone a) (q : B k) (i : B h) (hi : a i ≤ q)
    (hb : ∀ t, a t ≤ q → t ≤ i) (d : ℕ) (l : B h) (hl : l ≤ i) (hu : i.val < l.val + 2 ^ d) :
    seek a q d l = i := by
  induction d generalizing l with
  | zero =>
    change l.val ≤ i.val at hl
    change l = i
    exact Fin.ext (by rw [pow_zero] at hu; omega)
  | succ d ih =>
    rw [seek]
    by_cases hlow : i.val < l.val + 2 ^ d
    · by_cases hj : l.val + 2 ^ d < 2 ^ h
      · have e : q < a (jump d l) := lt_of_not_ge fun h => by
          have := hb _ h
          simp only [jump, dite_eq_left hj, Fin.le_def] at this
          omega
        rw [ite_eq_left e]
        exact ih l hl hlow
      · simpa [jump, hj] using ih l hl hlow
    · have hj : l.val + 2 ^ d < 2 ^ h := (le_of_not_gt hlow).trans_lt i.isLt
      have hj' : jump d l ≤ i := by simpa [jump, hj, Fin.le_def] using le_of_not_gt hlow
      rw [ite_eq_right ((ha hj').trans hi).not_gt]
      refine ih _ hj' ?_
      rw [pow_succ] at hu
      simp only [jump, dite_eq_left hj]
      omega

def order (x : B h → (span k).obj) : Equiv.Perm (B h) :=
  permutation (key ∘ x) (fun _ => true)

def packed (q : B h → B k) (pad : B k) (x : B h → (span k).obj) : B h → B k :=
  let y := x ∘ order x
  fun b => get (q b) pad (y (seek (key ∘ y) (q b) h 0))

private theorem packed_at (q : B h → B k) (pad : B k) (x : B h → (span k).obj)
    (b i : B h) (hc : contains (x i) (q b))
    (unique : ∀ u, (x i).1 ≤ (x u).1 → (x u).1 ≤ q b → (x u).1 < (x u).2.1 → x u = x i) :
    packed q pad x b = q b + (x i).2.2 := by
  let y := x ∘ order x
  let a := key ∘ y
  have ha : Monotone a := fun _ _ h => rankAt_le (key ∘ x) _ _ h
  let s := Finset.univ.filter fun t => a t ≤ q b
  let i' := (order x).symm i
  have hei : a i' = (x i).1 := by simp [a, y, key, i', lt_of_le_of_lt hc.1 hc.2]
  have hi : i' ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hei.le.trans hc.1⟩
  let m := s.max' ⟨_, hi⟩
  have hm : a m ≤ q b := (Finset.mem_filter.mp (s.max'_mem _)).2
  have hmax (t : B h) (h : a t ≤ q b) : t ≤ m :=
    s.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have he : seek a (q b) h 0 = m := seek_ok a ha _ m hm hmax h 0 (Fin.zero_le _) (by simp)
  have hvalid : (y m).1 < (y m).2.1 := by
    by_contra h
    have e : a m = ⊤ := ite_eq_right h
    exact (hc.2.trans_le le_top).not_ge (e ▸ hm)
  have e : a m = (y m).1 := ite_eq_left hvalid
  have eq : y m = x i :=
    unique _ (hei.ge.trans ((ha (s.le_max' _ hi)).trans_eq e)) (e.ge.trans hm) hvalid
  change get (q b) pad (y (seek a (q b) h 0)) = _
  rw [he, eq, get, ite_eq_right hc.1.not_gt, ite_eq_left hc.2]

def extend {j t : ℕ} (h : j ≤ t) : B j → B t := Fin.castLE (Nat.pow_le_pow_right (by decide) h)

def shrink (j : ℕ) (i : B h) : B j := ⟨i.val % 2 ^ j, Nat.mod_lt _ (by positivity)⟩

@[simp] theorem shrink_extend {t : ℕ} (h : j ≤ t) (a : B j) : shrink j (extend h a) = a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

def eval (query : B h → B k) (pad : B k) (x : B j → (span k).obj) (b : B h) : B k :=
  packed (query ∘ shrink h) pad (x ∘ shrink j) (extend (le_max_right j h) b)

theorem eval_at (query : B h → B k) (pad : B k) (x : B j → (span k).obj) (b : B h) (i : B j)
    (hc : contains (x i) (query b))
    (hu : ∀ u v, contains (x i) v → contains (x u) v → x u = x i) :
    eval query pad x b = query b + (x i).2.2 := by
  have he := packed_at (query ∘ shrink h) pad (x ∘ shrink j)
    (extend (le_max_right j h) b) (extend (le_max_left j h) i)
  simp only [Function.comp_apply, shrink_extend] at he
  exact he hc (fun u h₁ h₂ h₃ => hu _ _ ⟨h₁, h₂.trans_lt hc.2⟩ ⟨le_rfl, h₃⟩)

theorem eval_pad (query : B h → B k) (pad : B k) (x : B j → (span k).obj) (b : B h)
    (hc : ∀ i, ¬ contains (x i) (query b)) : eval query pad x b = pad := by
  have hg (i) : get (query b) pad (x i) = pad := by
    by_cases hi : query b < (x i).1
    · exact ite_eq_left hi
    · rw [get, ite_eq_right hi, ite_eq_right (fun h => hc i ⟨le_of_not_gt hi, h⟩)]
  simp only [eval, packed, Function.comp_apply, shrink_extend, hg]

end
end OAI.LinearAlgebra.MatrixExponent.Assembly.Intervals
end

/-!
# Carrying a public tape across the entire computation

Some protocols transport the physical payload only at termination.
Compose the control kernels first, and add a *single* identity on
the public tape. Its cost is independent of the number of stages.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

universe v
variable {F : Type} [Field F] {x y : Wire}
  {X Y : Snapshot.{v} F x y} {u s : ℕ} {L : Set (Table F)}

def Snapshot.hold (X : Snapshot.{v} F x y) (D : Format) (f : Val x → Val y → D.obj) :
    Snapshot.{v} F x y where
  state := X.state
  eval := X.eval
  port := X.port.pair D
  encode i a b := (X.encode i a b, f a b)

abbrev Snapshot.public (X : Snapshot.{v} F x y) : Snapshot.{v} F x y :=
  X.hold (.wire (.pair x y)) (fun a b => (a, b))

theorem Transforms.hold (h : Transforms F u L X Y s) (hu : 3 ≤ u) (D : Format)
    (f : Val x → Val y → D.obj) :
    Transforms F u L (X.hold D f) (Y.hold D f) (s + 4 * D.width) := by
  obtain ⟨k, hk, he⟩ := h
  have hid := Map.circuit (L := L) hu (Circuit.id F D)
  refine ⟨_, hk.par hid, fun i => ?_⟩
  change X.state at i
  obtain ⟨I, _, q, c, hq, hs⟩ := he i
  refine ⟨I, inferInstance, q, c, hq, ?_⟩
  rintro a b ⟨t, v⟩
  change k (X.encode i a b) t * (if f a b = v then 1 else 0) =
    ∑ j, @ite F ((Y.encode (q j) a b, f a b) = (t, v)) (Classical.propDecidable _) (c j) 0
  rw [hs]
  by_cases h : f a b = v <;> simp [h, Prod.mk.injEq]

/-- There is no extra identity charge at each step of the iteration. -/
theorem Transforms.stages (X : ℕ → Snapshot.{v} F x y) (cost : ℕ → ℕ)
    (j : ℕ) (hj : 0 < j)
    (steps : ∀ i < j, Transforms F u L (X i) (X (i + 1)) (cost i)) :
    Transforms F u L (X 0) (X j) (∑ i ∈ Finset.range j, cost i) := by
  induction j, hj using Nat.le_induction with
  | base => simpa using steps 0 (by decide)
  | succ j hj ih =>
    rw [Finset.sum_range_succ]
    exact (ih fun i hi => steps i (Nat.lt_succ_of_lt hi)).comp (steps j (by omega))

theorem Finishes.widen (h : Finishes F u L X s) {v : ℕ} {T : Set (Table F)}
    (hu : u ≤ v) (hL : L ⊆ T) : Finishes F v T X s :=
  let ⟨f, hf, he⟩ := h
  ⟨f, hf.widen hu hL, he⟩

theorem Snapshot.public_start (X : Snapshot.{v} F x y) (i : X.state)
    (c : X.port.obj) (hc : ∀ a b, X.encode i a b = c) (hu : 3 ≤ u) :
    Map F u L (.wire (.pair x y)) X.public.port (fun z => X.public.encode i z.1 z.2)
      (4 * (wd x + wd y + 34 * X.public.port.width)) := by
  have h : Install.Depends (X.public.port.code ∘ (fun z => X.public.encode i z.1 z.2) ∘
      (bits (.pair x y)).symm) 1 := by
    rintro (j|j)
    · refine ⟨∅, by simp, fun a b _ => ?_⟩
      change X.port.code (X.encode i _ _) j = X.port.code (X.encode i _ _) j
      rw [hc, hc]
    · refine ⟨{j}, by simp, fun a b he => ?_⟩
      change bits (.pair x y) ((bits (.pair x y)).symm a) j = bits (.pair x y) ((bits (.pair x y)).symm b) j
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact he _ (by simp)
  apply Map.circuit hu
  have hk := h.bnet F
  rw [card_slots] at hk
  exact hk

theorem Transforms.public_end (h : Transforms F u L X Y s) {m : ℕ} (hu : 3 ≤ u)
    (stop : Finishes F u L Y.public m) (i : X.state) (c : X.port.obj)
    (hc : ∀ a b, X.encode i a b = c) :
    ∃ n ≤ 150 * (X.port.width + wd x + wd y) + s + m, Wide F u L x y (X.eval i) n := by
  have held := h.hold hu (.wire (.pair x y)) fun a b => (a, b)
  obtain ⟨n, hn, hnet⟩ := Finishes.start (X := X.public) hu i (X.public_start i c hc hu) (held.finish stop)
  refine ⟨n, hn.trans ?_, hnet⟩
  change 4 * (wd x + wd y + 34 * (X.port.pair (.wire (.pair x y))).width) +
    (s + 4 * (Format.wire (.pair x y)).width + m) + 4 * wd y ≤ _
  rw [Format.width_pair]
  rw [show (Format.wire (.pair x y)).width = wd x + wd y from card_slots (.pair x y)]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

section
/-! Parallel binary search on a vector of sorted addresses. -/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Intervals
open Coloring
noncomputable section
variable (F : Type) [Field F] {h k t : ℕ}

theorem cheap_compare (hk : k ≤ t) :
    Cheap F 0 t (.pair (.addr k) (.addr k)) .bit (fun z => decide (z.1 < z.2)) 3 := by
  refine ⟨_, numeric_lt F k, ?_⟩
  simp only [Format.width_pair, Format.width_addr]
  rw [Format.width_bit]
  ring_nf
  omega

abbrev Col (h k : ℕ) := Format.vec h (.addr k)

theorem vec_bound (h : ℕ) {A : Format} (hw : A.width ≤ 100 + t) :
    (Format.vec h A).width ≤ 2 ^ h * (100 + t) ^ 1 := by
  rw [Format.width_vec, pow_one]
  exact Nat.mul_le_mul_left _ hw

private theorem col_bound (h : ℕ) (hk : k ≤ t) : (Col h k).width ≤ 2 ^ h * (100 + t) ^ 1 :=
  vec_bound _ (by rw [Format.width_addr]; omega)

private abbrev State (h k : ℕ) := Format.pair (Col h k) (Col h h)

private def step (q : B h → B k) (d : ℕ) (x : (State h k).obj) : (State h k).obj :=
  (x.1, fun i => if q i < x.1 (jump d (x.2 i)) then x.2 i else jump d (x.2 i))

private def steps (q : B h → B k) (d : ℕ) (x : (State h k).obj) : (State h k).obj :=
  (x.1, fun i => seek x.1 (q i) d (x.2 i))

private theorem cheap_step (q : B h → B k) (d : ℕ) (hk : h + k ≤ t) :
    Cheap F h t (State h k) (State h k) (step q d) 20 := by
  have hl : (State h k).width ≤ 2 ^ h * (100 + t) ^ 1 := by
    simp only [State, Col, Format.width_pair, Format.width_vec, Format.width_addr, ← mul_add, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have ha : k ≤ t := by omega
  have hb : h ≤ t := by omega
  have x := Cheap.id F hl
  have trial := ((Cheap.const F hl (col_bound h hb) (jump d)).pair x.snd).comp
    (Cheap.lookup F h t (.addr h) hb (by simp [hb]))
  have val := (x.fst.pair trial).comp (Cheap.lookup F h t (.addr k) hb (by simp [ha]))
  have query := Cheap.const F hl (col_bound h ha) q
  have lt := (query.pair val).zip.comp (Cheap.map _ fun _ : B h => cheap_compare F ha)
  have sel := ((x.snd.pair trial).zip.pair lt).zip.comp
    (Cheap.map _ fun _ : B h => (cheap_select F h).widen hb)
  convert (x.fst.pair sel).mono (d := 20) (by decide) using 1
  funext x
  apply Prod.ext
  · rfl
  · funext i
    by_cases he : q i < x.1 (jump d (x.2 i)) <;> simp [step, he]

private theorem cheap_steps (q : B h → B k) (hk : h + k ≤ t) :
    Cheap F h t (State h k) (State h k) (steps q h) 21 := by
  let A := State h k
  let C := 2 ^ h * (100 + t) ^ 20
  have run (d) : Circuit F A A (steps q d) (A.width + d * C) := by
    induction d with
    | zero =>
      rw [Nat.zero_mul, Nat.add_zero]
      exact Circuit.id F A
    | succ d ih =>
      obtain ⟨m, h₁, h₂⟩ := cheap_step F q d hk
      have he : steps q (d + 1) = steps q d ∘ step q d := rfl
      rw [he, Nat.succ_mul]
      exact (h₁.comp ih).mono (by omega)
  obtain ⟨m, _, hm⟩ := cheap_step F q 0 hk
  refine ⟨_, run h, ?_⟩
  rw [pow_succ, ← mul_assoc (2 ^ h)]
  have ht := Nat.mul_le_mul_right C (show h ≤ t by omega)
  change A.width + A.width + (A.width + h * C) ≤ C * (100 + t)
  rw [mul_add, mul_comm C 100, mul_comm C t]
  change A.width + A.width + m ≤ C at hm
  omega

theorem cheap_seek (q : B h → B k) (hk : h + k ≤ t) :
    Cheap F h t (Col h k) (Perm h) (fun a b => seek a (q b) h 0) 23 := by
  have hb := col_bound h (show k ≤ t by omega)
  have hz := Cheap.const F hb (col_bound h (show h ≤ t by omega)) (fun _ => 0)
  exact (((Cheap.id F hb).pair hz).comp (cheap_steps F q hk)).snd

end
end OAI.LinearAlgebra.MatrixExponent.Assembly.Intervals
end

/-!
# Computing the status masks for a frozen core

Read the status of each neighbor once, then duplicate the short
mask at each block. The label serialization only permutes bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
open Coloring

variable {F : Type} [Field F] (S : Scheme F)

private theorem serial_bits (A : Format) :
    ∃ e : (Format.addr A.width).pins → A.pins,
      ∀ x i, (Format.addr A.width).code (A.serial x) i = A.code x (e i) := by
  have h (k : slots (word A.width) ≃ A.pins) :
      ∃ e : (Format.addr A.width).pins → A.pins,
        ∀ x i, (Format.addr A.width).code
          (((A.code.trans (k.symm.arrowCongr (.refl _))).trans (Format.addr A.width).code.symm) x) i =
            A.code x (e i) := by
    refine ⟨k, fun x i => ?_⟩
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  exact h _

abbrev cutInput := S.format.pair (.vec S.m .bit)
private abbrev query := Format.pair (.vec S.m .bit) (.vec S.d (Perm S.m))
private abbrev statuses := Format.vec S.m (.vec S.d .bit)

private def labels (x : S.cutInput.obj) : (query S).obj :=
  (x.2, fun j i => (x.1 i).1 j)

private def emit (x : (S.cutInput.pair (statuses S)).obj) : S.cut.format.obj :=
  fun v => ((x.1.1 v).1, fun i => S.cutCode.serial ((x.1.1 v).2 i, x.1.2 v, x.2 v))

private theorem emit_net :
    Circuit F (S.cutInput.pair (statuses S)) S.cut.format (emit S)
      ((S.cutInput.pair (statuses S)).width + 2 * S.cut.format.width) := by
  obtain ⟨k, hk⟩ := serial_bits S.cutCode
  let pins (i : B S.m) (j : B S.h) : S.cutCode.pins → (S.cutInput.pair (statuses S)).pins
    | .inl a => .inl (.inl (i, .inr (j, a)))
    | .inr (.inl a) => .inl (.inr (i, a))
    | .inr (.inr a) => .inr (i, a)
  let read : S.cut.format.pins → (S.cutInput.pair (statuses S)).pins
    | (i, .inl j) => .inl (.inl (i, .inl j))
    | (i, .inr (j, a)) => pins i j (k a)
  refine Circuit.project read ?_
  rintro x ⟨i, j|⟨j, a⟩⟩
  · rfl
  · refine (hk ((x.1.1 i).2 j, x.1.2 i, x.2 i) a).trans ?_
    change _ = (S.cutInput.pair (statuses S)).code x (pins i j (k a))
    rcases k a with a | (a|a) <;> rfl

def cutCost := 4 * (10 * S.cutInput.width + 2 * S.cut.format.width + 3 * 2 ^ S.m * (100 + (S.m + 2 ^ S.d)) ^ 12)

theorem map_remove {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) :
    Map F u L S.cutInput S.cut.format (fun x => S.remove x.1 x.2) S.cutCost := by
  have a : Circuit F S.cutInput (query S) (labels S) (S.cutInput.width + 2 * (query S).width) :=
    Circuit.project (Sum.elim Sum.inr (fun z => Sum.inl (z.2.1, .inl (z.1, z.2.2))))
      (by rintro _ (i|j) <;> rfl)
  obtain ⟨m, h, hb⟩ := Cheap.neighbors F .bit S.m (S.m + 2 ^ S.d) S.d (Nat.le_add_right _ _)
    (Format.width_bit.le.trans ((Nat.two_pow_pos S.d).trans_le (Nat.le_add_left _ _))) (Nat.le_add_left _ _)
  let x := Circuit.id F S.cutInput
  have out := (x.pair (a.comp h)).comp (S.emit_net)
  simp only [Function.comp_def, id_eq] at out
  refine (Map.circuit hu out).mono ?_
  change (query S).width + (statuses S).width + m ≤ _ at hb
  rw [Format.width_pair S.cutInput (statuses S)]
  unfold cutCost
  rw [mul_assoc 3]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-!
# Deterministic grouping and coloring

The chosen mixer minimizes the number of splits. The affine coloring
maximizes the number of matched units for this grouping. Unused
host positions have score zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Packing Coloring Finset
open scoped Classical

variable {X : Type} [Fintype X] {b k d : ℕ}

def ballots (f : X ↪ B b) (s : B k → X → B d) (i : B k) (j : B b) :=
  Function.extend f (s i) (fun _ => 0) j

theorem ballots_total (f : X ↪ B b) (s : B k → X → B d) (i : B k) :
    (∑ j, (ballots f s i j).val) = ∑ x, (s i x).val := by
  rw [← sum_subset (subset_univ (univ.map f)), sum_map]
  · simp [ballots, f.injective.extend_apply]
  · intro z _ hz
    have h : z ∉ Set.range f := by simpa using hz
    simp only [ballots, Function.extend_apply' _ _ _ h, Fin.val_zero]

def splitScore (N : X → Finset X) (delay : X → X → ℕ) (l : X → Cell k → ℝ)
    (i : B k) (x : X) : B k := ⟨splits N delay l i x, splits_le _ _ _ _ _⟩

theorem elected_best (N : X → Finset X) (delay : X → X → ℕ) (l : X → Cell k → ℝ)
    (f : X ↪ B b) :
    best N delay l (elect ⊥ (ballots f (splitScore N delay l))) := by
  intro q
  simpa only [ballots_total, splitScore] using elect_min (ballots f (splitScore N delay l)) q

def colorIndex (k : ℕ) : B (k + 1) ≃ Color k :=
  Fintype.equivOfCardEq (by simp [Color, Cell, pow_succ])

namespace Scheme.Posting

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u h : ℕ}
  {S : Scheme F} {r : S.format.obj} {G : HostNet F L h u}
  (p : S.Posting r G) (hu : 0 < u) (a : ℕ) (ha : a ≤ h) {Δ D k : ℕ} {B' : ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' (G.regroup a ha).load)

def colorScore (c : B (h - a + 1)) (v : G.V × Cell a) : B (h - a + S.e + 1) :=
  let row := Match.rows (p.records a ha g (colorIndex _ c) v)
  ⟨(univ.filter fun i => row.control.1 i).card, by
    refine (card_filter_le _ _).trans_lt ?_
    rw [card_univ, Fintype.card_fin, pow_succ]
    have : 0 < (2 : ℕ) ^ (h - a + S.e) := by positivity
    omega⟩

def color (f : G.V × Cell a ↪ B b) :=
  colorIndex (h - a) (elect ⊤ (ballots f (p.colorScore a ha g)))

theorem score_optimal (f : G.V × Cell a ↪ B b) (c : Color (h - a)) :
    p.score a ha g c ≤ p.score a ha g (p.color a ha g f) := by
  have he := elect_max (ballots f (p.colorScore a ha g)) ((colorIndex (h - a)).symm c)
  rw [ballots_total, ballots_total] at he
  change p.score a ha g ((colorIndex (h - a)) ((colorIndex (h - a)).symm c)) ≤ _ at he
  rw [Equiv.apply_symm_apply] at he
  exact he

theorem elected_matching (f : G.V × Cell a ↪ B b) (σ : ℝ) (hB : 0 < B')
    (bounds : G.Bounded Δ D B') (hbins : 256 * (coreBins Δ + 1) ≤ 2 ^ k)
    (slack : (2 : ℝ) ^ k * B' * (Fintype.card G.V * 2 ^ a : ℕ) ≤ σ) :
    ∃ m : Matchings a ha g, m.color = p.color a ha g f ∧ p.Controls hu a ha g m ∧
      (G.X : ℝ) / 4 - (L.Z + σ) ≤ u * (m.count : ℝ) := by
  obtain ⟨m, hm, hc⟩ := p.matching hu a ha g σ hB bounds hbins slack
  obtain ⟨t, ht, ctl⟩ := p.all_colors hu a ha g (p.color a ha g f)
  refine ⟨t, ht, ctl, hc.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))⟩
  rw [Nat.cast_le, ← p.match_score hu a ha g m hm, ← p.match_score hu a ha g t ctl, ht]
  exact p.score_optimal a ha g f _

end Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! The bucket ordinal is the occurrence rank in the vector of dyadic levels. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.PackRank

open Coloring
variable {h k V l : ℕ}

def code (x : B k) : B k :=
  ⟨Nat.clog 2 x.val, (Nat.clog_le_of_le_pow x.isLt.le).trans_lt Nat.lt_two_pow_self⟩

def assign (x : B h → B k) (i : B h) := (code (x i), groupRank (code ∘ x) i)

private theorem ranked {n : ℕ} (z : B h → Fin n) (i : B h) :
    ((Fintype.orderIsoFinOfCardEq {u // z u = z i} rfl).symm ⟨i, rfl⟩).val =
      Control.rank z i := by
  let S := {u // z u = z i}
  let f (x : S) : Fin (Fintype.card S) := ⟨Control.rank z x.val, by
    rw [show Fintype.card S = Control.histogram z (z i) none by
      unfold S; rw [Fintype.card_subtype, Control.histogram_none]]
    exact (Control.rank_lt z x.val).trans_eq (congrArg (fun w => Control.histogram z w none) x.2)⟩
  have hf : StrictMono f := fun u v h => Control.rank_mono z (u.2.trans v.2.symm) h
  let e := Fintype.orderIsoFinOfCardEq S rfl
  have he := congrFun (hf.comp e.strictMono).eq_id (e.symm ⟨i, rfl⟩)
  simp only [Function.comp_apply, OrderIso.apply_symm_apply, id_eq] at he
  exact (congrArg Fin.val he).symm

theorem correct (p : Payload h V l) (x : B h → B k) (hx : ∀ i, (x i).val = p.length i)
    (i : B h) :
    (assign x i).1.val = (p.seat.write i).1.val ∧
      (assign x i).2.val = (p.seat.write i).2.val := by
  let z (j : B h) := (p.seat.write j).1
  have hz (j : B h) : (code (x j)).val = (z j).val := by
    change Nat.clog 2 (x j).val = Nat.clog 2 (max 1 (p.length j))
    rw [hx]
    rcases le_total 1 (p.length j) with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, Nat.clog_of_right_le_one h, Nat.clog_of_right_le_one le_rfl]
  refine ⟨hz i, ?_⟩
  change (groupRank (code ∘ x) i).val =
    ((Fintype.orderIsoFinOfCardEq {u // z u = z i} rfl).symm ⟨i, rfl⟩).val
  rw [ranked, groupRank_val, Control.rank, Control.rank, Control.histogram_some, Control.histogram_some]
  congr 1
  ext j
  simp [Fin.ext_iff, hz]

end OAI.LinearAlgebra.MatrixExponent.Assembly.PackRank
end

/-! Near-linear circuit for assigning the ordered slots of a payload bank. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.PackRank
open Coloring

variable {k : ℕ}

private def scan (x : B k) : ℕ → B k
  | 0 => 0
  | m + 1 => if h : m < k then
      if 2 ^ m < x.val then ⟨m + 1, (Nat.succ_le_of_lt h).trans_lt Nat.lt_two_pow_self⟩ else scan x m
    else scan x m

private theorem scan_eq (x : B k) (n : ℕ) (hn : n ≤ k) (hx : x.val ≤ 2 ^ n) :
    (scan x n).val = Nat.clog 2 x.val := by
  have h := Nat.clog_le_of_le_pow hx
  induction n with
  | zero => simp only [scan, Fin.val_zero]; omega
  | succ m ih =>
    rw [scan, dite_eq_left (by omega)]
    by_cases hm : 2 ^ m < x.val
    · rw [ite_eq_left hm]
      have := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr hm
      change m + 1 = _
      omega
    · rw [ite_eq_right hm]
      exact ih (by omega) (le_of_not_gt hm) (Nat.clog_le_of_le_pow (le_of_not_gt hm))

variable (F : Type) [Field F]

private abbrev Cell (k : ℕ) := Format.pair (.addr k) (.addr k)

private theorem step (key level : B k) : Cheap F 0 k (Cell k) (Cell k)
    (fun y => (y.1, if key < y.1 then level else y.2)) 12 := by
  have hi : (Cell k).width ≤ 2 ^ 0 * (100 + k) ^ 2 := by simp [Cell]; ring_nf; omega
  have hw : (Format.addr k).width ≤ 2 ^ 0 * (100 + k) ^ 2 := by simp; ring_nf; omega
  have x := Cheap.id F hi
  have lt := ((Cheap.const F hi hw key).pair x.fst).comp (Intervals.cheap_compare F le_rfl)
  have sel := (((Cheap.const F hi hw level).pair x.snd).pair lt).comp (cheap_select F k)
  convert (x.fst.pair sel).mono (d := 12) (by decide) using 1
  funext y
  by_cases h : key < y.1 <;> simp [h]

theorem cheap_code (k : ℕ) : Cheap F 0 k (.addr k) (.addr k) code 16 := by
  let C := 2 ^ 0 * (100 + k) ^ 12
  have hw : (Format.addr k).width ≤ 2 ^ 0 * (100 + k) ^ 1 := by simp
  have net (n : ℕ) (hn : n ≤ k) :
      Circuit F (.addr k) (Cell k) (fun x => (x, scan x n)) ((n + 1) * C) := by
    induction n with
    | zero =>
      obtain ⟨m, hm, hb⟩ := ((Cheap.id F hw).pair (Cheap.const F hw hw 0)).mono (d := 12) (by decide)
      change Circuit F (.addr k) (Cell k) (fun x => (x, 0)) (1 * C)
      exact hm.mono (by unfold C; omega)
    | succ n ih =>
      have hh : n < k := hn
      let a : B k := ⟨2 ^ n, Nat.pow_lt_pow_right (by decide) hh⟩
      let b : B k := ⟨n + 1, hn.trans_lt Nat.lt_two_pow_self⟩
      obtain ⟨m, hm, hb⟩ := step F a b
      have he : (fun x : B k => (x, scan x (n + 1))) =
          (fun y : (Cell k).obj => (y.1, if a < y.1 then b else y.2)) ∘ (fun x => (x, scan x n)) := by
        funext x
        rw [scan, dite_eq_left hh]
        rfl
      rw [he, Nat.succ_mul]
      exact ((ih hh.le).comp hm).mono (Nat.add_le_add_left (by unfold C; omega) _)
  have he : (fun x : B k => (x, scan x k)) = fun x => (x, code x) :=
    funext fun x => Prod.ext rfl (Fin.ext (scan_eq x k le_rfl x.isLt.le))
  have hn := net k le_rfl
  rw [he] at hn
  have hc : Cheap F 0 k (.addr k) (Cell k) (fun x => (x, code x)) 13 := by
    refine ⟨_, hn, ?_⟩
    simp only [Cell, Format.width_pair, Format.width_addr]
    have hk : k ≤ C := by
      unfold C
      simpa using (show k ≤ 100 + k by omega).trans (Nat.le_pow (by decide : 0 < 12))
    rw [pow_succ, ← mul_assoc (2 ^ 0)]
    change k + (k + k) + (k + 1) * C ≤ C * (100 + k)
    nlinarith
  exact hc.snd.mono (by decide)

theorem cheap (h k : ℕ) :
    Cheap F h (h + k) (.vec h (.addr k)) (.vec h (.pair (.addr k) (.addr h))) assign 110 := by
  have levels := Cheap.map _ (fun _ : B h => (cheap_code F k).widen (show k ≤ h + k by omega))
  have rank := levels.comp (cheap_groupRank F h k)
  exact (levels.pair rank).zip.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.PackRank
end

/-!
# Distributing host records to dyadic slots

At each level, sort a one-bit key stably. The hosts of that level
come first, in increasing input order. Replace all inactive rows
by the padding value and retain the physical bucket's prefix.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Redistribute

open Coloring Transcript

variable {m w V k : ℕ}

abbrev input (m w : ℕ) (A : Format) := Format.pair (.vec m (.addr w)) (.vec m A)
abbrev output (m V k : ℕ) (A : Format) := Fmt.pi (fun _ : Slot (2 ^ m) V k => A)

def flag (l : ℕ) (x : B w) : B 1 := if (PackRank.code x).val = l then 0 else 1

def index (s : Slot (2 ^ m) V k) : B m := s.2.castLE (min_le_left _ _)

def mask (A : Format) (pad : A.obj) (x : (input m 1 A).obj) (i : B m) : A.obj :=
  if x.1 i = 0 then x.2 i else pad

def bucket (l : ℕ) (A : Format) (pad : A.obj) (x : (input m w A).obj) :=
  let f := flag l ∘ x.1
  mask A pad (f, x.2) ∘ Coloring.order f

def eval (A : Format) (pad : A.obj) (x : (input m w A).obj) : (output m V k A).obj :=
  fun s => bucket s.1.val A pad x (index s)

private theorem zero_rank (f : B m → B 1) (i : B m) (h : f i = 0) :
    ((Coloring.order f).symm i).val = Control.rank f i := by
  let a := f ∘ Coloring.order f
  let j := (Coloring.order f).symm i
  have hj : a j = 0 := by simp [a, j, h]
  have hz : a 0 = a j := le_antisymm (order_mono f (Fin.zero_le _)) (by rw [hj]; exact Fin.zero_le _)
  have hl : leader a j = 0 :=
    le_antisymm ((leader_spec a (order_mono f) j).2 0 hz) (Fin.zero_le _)
  rw [← groupRank_val]
  change j.val = (j - leader a j).val
  rw [hl, sub_zero]

private theorem position (p : Payload m V k) (x : B m → B w) (hx : ∀ i, (x i).val = p.length i)
    (s : Slot (2 ^ m) V k) (i : B m) :
    p.seat.write i = s ↔ (flag s.1.val ∘ x) i = 0 ∧ Coloring.order (flag s.1.val ∘ x) (index s) = i := by
  let f := flag s.1.val ∘ x
  have hk (j : B m) : f j = 0 ↔ (PackRank.code (x j)).val = s.1.val := by
    simp [f, flag]
  obtain ⟨hl, hr⟩ := PackRank.correct p x hx i
  change (PackRank.code (x i)).val = _ at hl
  have he : f i = 0 ↔ (p.seat.write i).1 = s.1 := by rw [hk, hl, Fin.ext_iff]
  have hpos (h : f i = 0) : ((Coloring.order f).symm i).val = (p.seat.write i).2.val := by
    rw [zero_rank f i h, ← hr]
    change _ = (groupRank (PackRank.code ∘ x) i).val
    rw [groupRank_val, Control.rank, Control.rank, Control.histogram_some, Control.histogram_some]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, h, hk, Fin.ext_iff,
      (hk i).mp h]
  change p.seat.write i = s ↔ f i = 0 ∧ Coloring.order f (index s) = i
  constructor
  · intro h
    have hf := he.mpr (congrArg Sigma.fst h)
    refine ⟨hf, (Coloring.order f).eq_symm_apply.mp (Fin.ext ?_)⟩
    rw [hpos hf, h]
    rfl
  · rintro ⟨hf, hi⟩
    have hr' := (hpos hf).symm.trans (congrArg Fin.val ((Coloring.order f).eq_symm_apply.mpr hi).symm)
    have he' := he.mp hf
    change (p.seat.write i).2.val = s.2.val at hr'
    generalize p.seat.write i = u at *
    obtain ⟨l, a⟩ := u
    obtain ⟨r, b⟩ := s
    change l = r at he'
    subst r
    exact congrArg (Sigma.mk l) (Fin.ext hr')

theorem correct (p : Payload m V k) (A : Format) (pad : A.obj) (x : (input m w A).obj)
    (hx : ∀ i, (x.1 i).val = p.length i) :
    eval A pad x = fun s => (p.seat.read s).elim pad x.2 := by
  funext s
  let f := flag s.1.val ∘ x.1
  let i := Coloring.order f (index s)
  change (if f i = 0 then x.2 i else pad) = _
  cases hr : p.seat.read s with
  | none =>
    have hf : f i ≠ 0 := by
      intro h
      have he := (p.seat.valid s i).mpr ((position p x.1 hx s i).mpr ⟨h, rfl⟩).symm
      rw [hr] at he
      contradiction
    simp [hf]
  | some j =>
    obtain ⟨hj, hi⟩ := (position p x.1 hx s j).mp ((p.seat.valid s j).mp hr).symm
    change i = j at hi
    rw [hi, ite_eq_left hj]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Redistribute
end

/-! Only the address metadata passes through comparison sorting. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Redistribute
open Coloring
open scoped Classical

variable (F : Type) [Field F] {m w : ℕ}

private theorem cheap_flag (l w : ℕ) : Cheap F 0 (w + 1) (.addr w) (.addr 1) (flag l) 24 := by
  have hw : (Format.addr w).width ≤ 2 ^ 0 * (100 + (w + 1)) ^ 1 := by simp; omega
  have hb : (Format.addr 1).width ≤ 2 ^ 0 * (100 + (w + 1)) ^ 1 := by rw [Format.width_addr]; simp; omega
  by_cases h : l < 2 ^ w
  · let y : B w := ⟨l, h⟩
    have lev := (PackRank.cheap_code F w).widen (show w ≤ w + 1 by omega)
    have eq := (lev.pair (Cheap.const F hw hw y)).comp (cheap_eq F (show w ≤ w + 1 by omega))
    have choices := (Cheap.const F hw hb 0).pair (Cheap.const F hw hb 1)
    have send := (choices.pair eq).comp ((cheap_select F 1).widen (show 1 ≤ w + 1 by omega))
    convert send.mono (d := 24) (by decide) using 1
    funext x
    by_cases h : (PackRank.code x).val = l <;> simp [flag, Fin.ext_iff, y, h]
  · convert (Cheap.const F hw hb 1).mono (d := 24) (by decide) using 1
    funext x
    exact ite_eq_right (ne_of_lt ((PackRank.code x).isLt.trans_le (le_of_not_gt h)))

private theorem mask_cost (A : Format) (pad : A.obj) (m : ℕ) :
    Circuit F (input m 1 A) (.vec m A) (mask A pad) (2 ^ m * (1 + 69 * A.width)) := by
  let R := input m 1 A
  let D := Format.vec m A
  have h : Install.Depends (D.code ∘ mask A pad ∘ R.code.symm) 2 := by
    rintro ⟨i, j⟩
    let fromKey (k : (Format.addr 1).pins) : R.pins := .inl (i, k)
    let out : R.pins := .inr (i, j)
    let S := Finset.univ.image fromKey
    have hS : S.card ≤ 1 := Finset.card_image_le.trans_eq (Format.width_addr 1)
    refine ⟨insert out S, (Finset.card_insert_le _ _).trans (by omega), fun x y he => ?_⟩
    let a := R.code.symm x
    let b := R.code.symm y
    have hk : a.1 i = b.1 i := by
      apply (Format.addr 1).code.injective
      funext k
      change R.code a (fromKey k) = R.code b (fromKey k)
      simpa only [a, b, Equiv.apply_symm_apply] using he (fromKey k)
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem fromKey (Finset.mem_univ _)))
    have hb : A.code (a.2 i) j = A.code (b.2 i) j := by
      change R.code a out = R.code b out
      simpa only [a, b, Equiv.apply_symm_apply] using he out (Finset.mem_insert_self _ _)
    change A.code (mask A pad a i) j = A.code (mask A pad b i) j
    unfold mask
    rw [hk]
    split <;> first | exact hb | rfl
  refine (h.bnet F).mono ?_
  change R.width + 68 * D.width ≤ _
  simp only [R, D, input, Format.width_pair, Format.width_vec]
  rw [Format.width_addr]
  exact le_of_eq (by ring)

def budget (m w v : ℕ) := 2 ^ m * (v + (101 + m + w) ^ 60)

theorem bound_width {v : ℕ} (A : Format) (ha : A.width ≤ v) (m w : ℕ) :
    (input m w A).width ≤ budget m w v := by
  simp only [input, Format.width_pair, Format.width_vec, Format.width_addr, ← mul_add, budget]
  have h := Nat.le_pow (a := 101 + m + w) (by decide : 0 < 60)
  exact Nat.mul_le_mul_left _ (by omega)

def prepare (A : Format) (l : ℕ) (pad : A.obj) (x : (input m w A).obj) : (exchangeIn A m).obj :=
  (Coloring.order (flag l ∘ x.1), mask A pad (flag l ∘ x.1, x.2))

theorem prepare_cost {v : ℕ} (A : Format) (ha : A.width ≤ v) (l : ℕ) (pad : A.obj) :
    Circuit F (input m w A) (exchangeIn A m) (prepare A l pad) (100 * budget m w v) := by
  let B := budget m w v
  have hC := Nat.le_pow (a := 101 + m + w) (by decide : 0 < 60)
  have hb (k c) (hk : k ≤ m + w + 1) (hc : c ≤ 60) : 2 ^ m * (100 + k) ^ c ≤ B := by
    unfold B budget
    exact Nat.mul_le_mul_left _ (((Nat.pow_le_pow_left (by omega : 100 + k ≤ 101 + m + w) _).trans
      (Nat.pow_le_pow_right (by omega) hc)).trans (Nat.le_add_left _ _))
  have h₀ : (input m 1 A).width ≤ B := by
    simp only [input, Format.width_pair, Format.width_vec, ← mul_add]
    exact Nat.mul_le_mul_left _ (by omega : 1 + A.width ≤ v + (101 + m + w) ^ 60)
  have h₁ : (Format.vec m A).width ≤ B := (by rw [Format.width_pair] at h₀; omega)
  have h₂ : (Column m 1).width ≤ B := (by rw [Format.width_pair] at h₀; exact (Nat.le_add_right _ _).trans h₀)
  obtain ⟨r, hr, hr'⟩ := Cheap.map _ (fun _ : Coloring.B m => cheap_flag F l w)
  obtain ⟨s, hs, hs'⟩ := cheap_order F m 1
  have pre := hr.par (Circuit.id F (.vec m A))
  have take := Circuit.project (F := F) (A := input m 1 A) (D := Column m 1) (f := Prod.fst)
    Sum.inl (fun _ _ => rfl)
  have ord := take.comp hs
  have hmask : 2 ^ m * (1 + 69 * A.width) ≤ 69 * B := by
    unfold B budget
    rw [mul_left_comm 69]
    exact Nat.mul_le_mul_left _ (by omega)
  have h := pre.comp (ord.pair (mask_cost F A pad m))
  have hr'' := hr'.trans (hb _ _ (by omega) (by decide))
  have hs'' := hs'.trans (hb _ _ (by omega) (by decide))
  exact h.mono (by omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Redistribute
end

/-! Each level uses a single controlled exchange of whole records. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Redistribute
open Coloring Transcript
open scoped Classical

variable {F : Type} [Field F] {m w V k u v c : ℕ} {L : Set (Table F)}

def cost (m k w v c : ℕ) := 10000 * (k + 1) * (c + budget m w v)

private theorem one (hu : 3 ≤ u) (ht : Radix.Tag F m v c) (A : Format) (ha : A.width ≤ v)
    (pad : A.obj) (l : ℕ) :
    Map F u L (input m w A) (.vec m A) (bucket l A pad) (4 * c + 1400 * budget m w v) := by
  have p := Map.circuit (L := L) hu (prepare_cost F A ha l pad (m := m) (w := w))
  have h := p.then_kernel (permutation_kernel A hu ht ha)
  have he (x : (input m w A).obj) (y : (Format.vec m A).obj) :
      exchange A F (prepare A l pad x) y = if bucket l A pad x = y then 1 else 0 := by
    change (if Function.Bijective (Coloring.order (flag l ∘ x.1)) ∧ y = bucket l A pad x
      then (1 : F) else 0) = _
    simp [eq_comm]
  simp only [he] at h
  have hb : 2 ^ m * (m + v + 1) ≤ budget m w v := by
    have := Nat.le_pow (a := 101 + m + w) (by decide : 0 < 60)
    exact Nat.mul_le_mul_left _ (by omega)
  have hg := h.mono (n := 4 * c + 1400 * budget m w v) (by linarith only [hb])
  unfold Map
  convert hg using 1
  funext x y
  split_ifs <;> rfl

private theorem output_width (A : Format) :
    (output m V k A).width ≤ (k + 1) * (2 ^ m * A.width) := by
  have hc : Fintype.card (Slot (2 ^ m) V k) ≤ (k + 1) * 2 ^ m := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : Fin (k + 1), 2 ^ m := Finset.sum_le_sum fun i _ => by
        rw [Fintype.card_fin]; exact min_le_left _ _
      _ = _ := by simp
  simp only [output, Fmt.width_pi, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← mul_assoc]
  exact Nat.mul_le_mul_right _ hc

/-- Total redistribution, including when a bucket has too many entries.
In that case only the entries in its physical seats are retained. -/
theorem realize (hu : 3 ≤ u) (ht : Radix.Tag F m v c) (A : Format) (ha : A.width ≤ v)
    (pad : A.obj) :
    Map F u L (input m w A) (output m V k A) (eval A pad) (cost m k w v c) := by
  let I := input m w A
  let J := Fmt.pi (fun _ : Fin (k + 1) => I)
  let K := Fmt.pi (fun _ : Fin (k + 1) => Format.vec m A)
  let D := output m V k A
  have copy : Circuit F I J (fun x _ => x) (I.width + 2 * J.width) :=
    Circuit.project (fun a => a.2) (fun _ _ => rfl)
  have p := Map.family (fun i : Fin (k + 1) => one (L := L) (w := w) hu ht A ha pad i.val)
  have cut : Circuit F K D (fun x s => x s.1 (index s)) (K.width + 2 * D.width) :=
    Circuit.project (fun j => ⟨j.1.1, index j.1, j.2⟩) (fun _ _ => rfl)
  have h := ((Map.circuit hu copy).comp p).comp (Map.circuit hu cut)
  let b := budget m w v
  have hi : I.width ≤ b := bound_width A ha m w
  have hv : 2 ^ m * A.width ≤ b := Nat.mul_le_mul_left _ (ha.trans (Nat.le_add_right _ _))
  have hj : J.width ≤ (k + 1) * b := by simpa [J] using Nat.mul_le_mul_left (k + 1) hi
  have hk : K.width ≤ (k + 1) * b := by simpa [K] using Nat.mul_le_mul_left (k + 1) hv
  have hd : D.width ≤ (k + 1) * b := (output_width A).trans (Nat.mul_le_mul_left _ hv)
  refine h.mono ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  change 4 * (I.width + 2 * J.width) + (k + 1) * (4 * c + 1400 * b) + 4 * (K.width + 2 * D.width) ≤
    10000 * (k + 1) * (c + b)
  linarith only [hi, hj, hk, hd, Nat.zero_le b, Nat.zero_le c, Nat.zero_le (k * b), Nat.zero_le (k * c)]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Redistribute
end
