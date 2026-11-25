import OAI.Optimization.LinearProgramming.PriceGame.StatesOracle
import Mathlib.Data.List.OfFn

/-! Count the work of constructing the designated query in §§4.3 and 7.4. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace States
namespace Cost

universe u

/-- Equality and the number of digit comparisons used, taking the low bit first. -/
def digitEq : ℕ → ℕ → ℕ → Bool × ℕ
  | 0, _, _ => (true, 0)
  | n + 1, a, b =>
    if a % 2 = b % 2 then
      let v := digitEq n (a / 2) (b / 2)
      (v.1, v.2 + 1)
    else (false, 1)

theorem digitEq_bound (n a b : ℕ) : (digitEq n a b).2 ≤ n := by
  induction n generalizing a b with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [digitEq]
    split
    · exact Nat.add_le_add_right (ih _ _) _
    · omega

theorem digitEq_spec {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (digitEq n a b).1 = true ↔ a = b := by
  induction n generalizing a b with
  | zero =>
    simp only [pow_zero] at ha hb
    have hab : a = b := by omega
    simp [digitEq, hab]
  | succ n ih =>
    rw [pow_succ] at ha hb
    simp only [digitEq]
    split
    · rename_i hbit
      rw [ih (show a / 2 < 2 ^ n by omega) (show b / 2 < 2 ^ n by omega)]
      omega
    · rename_i hbit
      simp only [Bool.false_eq_true, false_iff]
      exact fun hab => hbit (hab ▸ rfl)

def depth {I : Type u} : {J : Type u} → Path I J → ℕ
  | _, .root => 0
  | _, .extend p _ _ => depth p + 1

/-- Compare the signs along the address, then compare the finite root indices. -/
def addressEq {N : ℕ} : {J : Type} → (p : Path (Fin N) J) → J → J → Bool × ℕ
  | _, .root, i, j => digitEq (N.log2 + 1) i j
  | _, .extend p _ _, i, j =>
    if i.2 = j.2 then
      let v := addressEq p i.1 j.1
      (v.1, v.2 + 1)
    else (false, 1)

theorem addressEq_bound {N : ℕ} {J : Type} (p : Path (Fin N) J) (i j : J) :
    (addressEq p i j).2 ≤ N.log2 + 1 + depth p := by
  induction p with
  | root => exact digitEq_bound _ _ _
  | extend p _ _ ih =>
    simp only [addressEq, depth]
    split
    · have h := ih i.1 j.1
      omega
    · omega

theorem addressEq_spec {N : ℕ} {J : Type} (p : Path (Fin N) J) (i j : J) :
    (addressEq p i j).1 = true ↔ i = j := by
  induction p with
  | root =>
    have hn : N ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)
    have hN : N < 2 ^ (N.log2 + 1) := (Nat.log2_lt hn).mp (Nat.lt_succ_self _)
    exact (digitEq_spec (lt_trans i.isLt hN) (lt_trans j.isLt hN)).trans Fin.val_inj
  | extend p _ _ ih =>
    simp only [addressEq]
    split
    · rename_i h₂
      rw [ih]
      exact ⟨fun h₁ => Prod.ext h₁ h₂, fun h => h ▸ rfl⟩
    · rename_i h₂
      simp only [Bool.false_eq_true, false_iff]
      exact fun h => h₂ (h ▸ rfl)

/-- Counts for evaluating one root price. A median reads one public baseline and
uses four rational min/max comparisons. Index comparisons include all digits inspected. -/
structure Sample where
  value : ℚ
  leafReads : ℕ
  medians : ℕ
  indexTests : ℕ
  addressDigits : ℕ

def source (v : ℚ) : Sample := ⟨v, 1, 0, 0, 0⟩

/-- Evaluate the same override as the public query algorithm, with metered address equality. -/
def liftSample {N : ℕ} {J : Type} (p : Path (Fin N) J) (y : J → ℚ)
    (read : J × Bool → Sample) (q : J × Bool) (i : J) : Sample :=
  let equal := addressEq p i q.1
  if equal.1 then
    let v := read q
    {v with indexTests := v.indexTests + 1, addressDigits := v.addressDigits + equal.2}
  else
    let l := read (i, false)
    let r := read (i, true)
    ⟨median₃ (y i) l.value r.value, l.leafReads + r.leafReads,
      l.medians + r.medians + 1, l.indexTests + r.indexTests + 1,
      l.addressDigits + r.addressDigits + equal.2⟩

theorem liftSample_value {N : ℕ} {J : Type} (p : Path (Fin N) J) (dec : DecidableEq J)
    (y : J → ℚ) (read : J × Bool → Sample) (q : J × Bool) (i : J) :
    (liftSample p y read q i).value = @override J dec y (fun j => (read j).value) q i := by
  by_cases he : i = q.1
  · subst i
    simp [liftSample, override, (addressEq_spec p q.1 q.1).2 rfl]
  · have hn : (addressEq p i q.1).1 ≠ true := fun v => he ((addressEq_spec p _ _).1 v)
    simp [liftSample, override, he, hn, parentPrices]

/-- Prepared root query. Each stored parent link is followed once during construction. -/
structure Prepared (N : ℕ) where
  price : Fin N → Sample
  designation : Fin N
  ascents : ℕ

def prepare {N : ℕ} : {J : Type} → (p : Path (Fin N) J) → (J → Sample) → J → Prepared N
  | _, .root, read, i => ⟨read, i, 0⟩
  | _, .extend p y _, read, q =>
    let v := prepare p (liftSample p y read q) q.1
    {v with ascents := v.ascents + 1}

theorem prepare_values {N : ℕ} {J : Type} (p : Path (Fin N) J) (read : J → Sample) (i : J) :
    (fun j => ((prepare p read i).price j).value, (prepare p read i).designation) =
        p.rootQuery (fun j => (read j).value) i := by
  induction p with
  | root => rfl
  | extend p y dec ih =>
    have step : (fun j => (liftSample p y read i j).value) =
        @override _ dec y (fun j => (read j).value) i := funext (liftSample_value p dec y read i)
    simpa only [prepare, Path.rootQuery, step] using ih (liftSample p y read i) i.1

theorem prepare_ascents {N : ℕ} {J : Type} (p : Path (Fin N) J) (read : J → Sample) (i : J) :
    (prepare p read i).ascents = depth p := by
  induction p with
  | root => rfl
  | extend p y dec ih => exact congrArg (· + 1) (ih _ _)

/-- Bounds for an arbitrary subtree; the index test can inspect `width` address digits. -/
def Bounded (cells width : ℕ) (v : Sample) : Prop :=
  v.leafReads ≤ cells ∧ v.medians + 1 ≤ cells ∧ v.indexTests + 1 ≤ cells ∧
    v.addressDigits ≤ width * v.indexTests

theorem liftSample_bounded {N : ℕ} {J : Type} (p : Path (Fin N) J) (y : J → ℚ)
    (read : J × Bool → Sample) (q : J × Bool) (i : J) {cells width : ℕ}
    (hwidth : N.log2 + 1 + depth p ≤ width) (hread : ∀ j, Bounded cells width (read j)) :
    Bounded (2 * cells) width (liftSample p y read q i) := by
  have hcmp := (addressEq_bound p i q.1).trans hwidth
  unfold liftSample
  dsimp only
  split
  · obtain ⟨hr, hm, ht, hd⟩ := hread q
    simp only [Bounded, Nat.mul_add, Nat.mul_one]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · obtain ⟨lr, lm, lt, ld⟩ := hread (i, false)
    obtain ⟨rr, rm, rt, rd⟩ := hread (i, true)
    simp only [Bounded, Nat.mul_add, Nat.mul_one]
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem prepare_bounded {N : ℕ} {J : Type} (p : Path (Fin N) J) (read : J → Sample)
    (i : J) {cells width : ℕ} (hwidth : N.log2 + 1 + depth p ≤ width)
    (hread : ∀ j, Bounded cells width (read j)) (j : Fin N) :
    Bounded (2 ^ depth p * cells) width ((prepare p read i).price j) := by
  induction p generalizing cells with
  | root => simpa only [prepare, depth, pow_zero, one_mul] using hread j
  | extend p y dec ih =>
    have hp : N.log2 + 1 + depth p ≤ width := by simp only [depth] at hwidth; omega
    have h := ih (liftSample p y read i) i.1 hp (fun a => liftSample_bounded p y read i a hp hread)
    simpa only [prepare, depth, pow_succ, Nat.mul_assoc] using h

/-- The complete written query stores its `N` prices in increasing root-coordinate order. -/
def written {N : ℕ} {J : Type} (p : Path (Fin N) J) (x : J → ℚ) (q : J) :
    List Sample × Fin N :=
  let v := prepare p (fun j => source (x j)) q
  (List.ofFn v.price, v.designation)

theorem written_values {N : ℕ} {J : Type} (p : Path (Fin N) J) (x : J → ℚ) (q : J) :
    ((written p x q).1.map Sample.value, (written p x q).2) =
      (List.ofFn (p.rootQuery x q).1, (p.rootQuery x q).2) := by
  have h := prepare_values p (fun j => source (x j)) q
  simpa only [written, List.map_ofFn, Function.comp_def, source] using
    congrArg (fun v : (Fin N → ℚ) × Fin N => (List.ofFn v.1, v.2)) h

theorem written_cells_bounded {N : ℕ} {J : Type} (p : Path (Fin N) J)
    (x : J → ℚ) (q : J) (v : Sample) (hv : v ∈ (written p x q).1) :
    Bounded (2 ^ depth p) (N.log2 + 1 + depth p) v := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
  simpa only [Nat.mul_one] using prepare_bounded p (fun j => source (x j)) q
    (cells := 1) le_rfl (fun _ => by simp [Bounded, source]) j

private theorem list_work_bound {l : List Sample} {B : ℕ} (f : Sample → ℕ)
    (bound : ∀ v ∈ l, f v ≤ B) : (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have h := ih (fun v hv => bound v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have hx := bound x List.mem_cons_self
    omega

/-- Total source reads, rational comparisons, and binary address comparisons when explicitly
writing the vector. There are also exactly `N` output cells and `depth p` parent projections. -/
theorem written_work {N : ℕ} {J : Type} (p : Path (Fin N) J)
    (x : J → ℚ) (q : J) :
    let rows := (written p x q).1
    rows.length = N ∧
      (rows.map Sample.leafReads).sum ≤ N * 2 ^ depth p ∧
      (rows.map (fun v => 4 * v.medians)).sum ≤ N * (4 * (2 ^ depth p - 1)) ∧
      (rows.map Sample.addressDigits).sum ≤
        N * ((N.log2 + 1 + depth p) * (2 ^ depth p - 1)) := by
  dsimp only
  have hlen : (written p x q).1.length = N := List.length_ofFn
  refine ⟨hlen, ?_, ?_, ?_⟩
  · have hh := list_work_bound Sample.leafReads (fun v hv => (written_cells_bounded p x q v hv).1)
    simpa only [hlen] using hh
  · have hh := list_work_bound (l := (written p x q).1) (B := 4 * (2 ^ depth p - 1))
        (fun v => 4 * v.medians) (by
          intro v hv
          have hm := (written_cells_bounded p x q v hv).2.1
          omega)
    simpa only [hlen] using hh
  · have hh := list_work_bound (l := (written p x q).1)
        (B := (N.log2 + 1 + depth p) * (2 ^ depth p - 1)) Sample.addressDigits (by
          intro v hv
          obtain ⟨_, _, ht, hd⟩ := written_cells_bounded p x q v hv
          exact hd.trans (Nat.mul_le_mul_left _ (by omega)))
    simpa only [hlen] using hh

/-- At every depth of the algorithm the exponential in path depth is bounded linearly in N. -/
theorem power_depth_le {N : ℕ} (hN : 0 < N) {J : Type} (p : Path (Fin N) J)
    (hd : depth p ≤ Mass.depth N) : 2 ^ depth p ≤ 2 * N := by
  calc
    2 ^ depth p ≤ 2 ^ Mass.depth N := Nat.pow_le_pow_right (by decide) hd
    _ ≤ 2 * N := by
      rw [Mass.depth, pow_succ, Nat.mul_comm]
      exact Nat.mul_le_mul_left 2 (Nat.log2_self_le hN.ne')

/-- After substituting the actual tree-depth cutoff, these are polynomial bounds for
source reads, scalar comparisons, and address-digit comparisons, respectively. -/
theorem written_polynomial_work {N : ℕ} (hN : 0 < N) {J : Type} (p : Path (Fin N) J)
    (hd : depth p ≤ Mass.depth N) (x : J → ℚ) (q : J) :
    let rows := (written p x q).1
    (rows.map Sample.leafReads).sum ≤ N * (2 * N) ∧
      (rows.map (fun v => 4 * v.medians)).sum ≤ N * (4 * (2 * N)) ∧
      (rows.map Sample.addressDigits).sum ≤ N * ((2 * Mass.depth N) * (2 * N)) := by
  obtain ⟨_, hr, hm, ha⟩ := written_work p x q
  have hpow := power_depth_le hN p hd
  have hsub : 2 ^ depth p - 1 ≤ 2 * N := (Nat.sub_le _ _).trans hpow
  have hw : N.log2 + 1 + depth p ≤ 2 * Mass.depth N := by
    change Mass.depth N + depth p ≤ 2 * Mass.depth N
    omega
  exact ⟨hr.trans (Nat.mul_le_mul_left _ hpow),
    hm.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsub)),
    ha.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul hw hsub))⟩

/-- A self-delimiting field consists of the unary bit count, a zero, and its bits. -/
def frame (bits : List Bool) : List Bool := List.replicate bits.length true ++ false :: bits

/-- Write every price using the supplied rational encoding, followed by the root designation
in exactly `N.log2 + 1` low-to-high bits. Framing makes the price boundaries recoverable. -/
def serialize {N : ℕ} {J : Type} (encode : ℚ → List Bool) (p : Path (Fin N) J)
    (x : J → ℚ) (q : J) : List Bool :=
  let result := written p x q
  result.1.flatMap (fun v => frame (encode v.value)) ++
    List.ofFn (fun bit : Fin (N.log2 + 1) => result.2.val.testBit bit.val)

private theorem flat_length_bound {l : List Sample} (f : Sample → List Bool) {B : ℕ}
    (h : ∀ v ∈ l, (f v).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons v vs ih =>
    have hs := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have hv := h v List.mem_cons_self
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- Selections preserve the supplied price-encoding bound, including on all intermediate
baselines. The bound counts the complete serialized output, including delimiters and address. -/
theorem serialize_length {N : ℕ} {J : Type} (encode : ℚ → List Bool) (p : Path (Fin N) J)
    (x : J → ℚ) (q : J) (B : ℕ) (bases : p.pricesSatisfy (fun v => (encode v).length ≤ B))
    (hx : ∀ j, (encode (x j)).length ≤ B) :
    (serialize encode p x q).length ≤ N * (2 * B + 1) + (N.log2 + 1) := by
  have hs := flat_length_bound (l := (written p x q).1)
    (fun v => frame (encode v.value)) (B := 2 * B + 1) (by
      intro v hv
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      have val := congrFun (congrArg Prod.fst (prepare_values p (fun z => source (x z)) q)) j
      have h := rootQuery_pricesSatisfy (fun t => (encode t).length ≤ B) p bases x hx q j
      change (frame (encode ((prepare p (fun z => source (x z)) q).price j).value)).length ≤ _
      change ((prepare p (fun z => source (x z)) q).price j).value = _ at val
      rw [val]
      simp only [frame, List.length_append, List.length_replicate, List.length_cons]
      change (encode ((p.rootQuery x q).1 j)).length + ((encode ((p.rootQuery x q).1 j)).length + 1) ≤ _
      omega)
  have hlen : (written p x q).1.length = N := List.length_ofFn
  rw [hlen] at hs
  simpa only [serialize, List.length_append, List.length_ofFn] using Nat.add_le_add_right hs (N.log2 + 1)

end Cost
end States
end PriceGame
end LinearProgramming
end Optimization
end OAI
