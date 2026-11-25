import OAI.Hierarchy.TaggedData
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.SplitLengths
import Mathlib.Order.Hom.Set

namespace OAI
/-! # Stable digit transport for tagged payloads -/

namespace Hierarchy.Tagged.Radix

variable {n : ℕ} {α κ : Type*}

/-- The two flagged records of a final address pair come from different input arrays. -/
def pairedScan (source : Fin n → α) (tag : Fin n → Fin n) (target : Fin n → α)
    (order : Equiv.Perm (Fin n)) : Prop :=
  ∀ a, tag (order a) = a ∧ target (order a) = source a

theorem valid_iff_unique_scan (source : Fin n → α) (tag : Fin n → Fin n)
    (target : Fin n → α) :
    Valid source tag target ↔ ∃! order : Equiv.Perm (Fin n), pairedScan source tag target order := by
  constructor
  · rintro ⟨bij, payload⟩
    let t := Equiv.ofBijective tag bij
    have cancel (a : Fin n) : tag (t.symm a) = a := t.apply_symm_apply a
    refine ⟨t.symm, fun a => ⟨cancel a, (payload _).trans (congrArg source (cancel a))⟩, ?_⟩
    intro other h
    apply Equiv.ext
    intro a
    exact bij.1 ((h a).1.trans (cancel a).symm)
  · rintro ⟨order, h, _⟩
    have tagged : tag = order.symm := by
      funext i
      simpa only [Equiv.apply_symm_apply] using (h (order.symm i)).1
    refine ⟨tagged ▸ order.symm.bijective, ?_⟩
    intro i
    simpa only [tagged, Equiv.apply_symm_apply] using (h (order.symm i)).2

/-- The stable order puts equal keys in increasing input-position order. -/
theorem unique_stable_sort [LinearOrder κ] (key : Fin n → κ) :
    ∃! order : Equiv.Perm (Fin n), Monotone (key ∘ order) ∧
      ∀ i j, i < j → key (order i) = key (order j) → order i < order j := by
  exact ⟨Tuple.sort key, Tuple.eq_sort_iff.mp rfl, fun _ h => Tuple.eq_sort_iff.mpr h⟩

/-- An output proposes an input address at every position. The tagged call
checks payloads, and ties must have increasing proposed addresses. -/
def StableGuess [LinearOrder κ] (key : α → κ) (xs ys : Fin n → α) (guess : Fin n → Fin n) : Prop :=
  Valid xs guess ys ∧ Monotone (key ∘ ys) ∧
    ∀ i j, i < j → key (ys i) = key (ys j) → guess i < guess j

theorem stableGuess_iff [LinearOrder κ] (key : α → κ) (xs ys : Fin n → α)
    (guess : Fin n → Fin n) :
    StableGuess key xs ys guess ↔ guess = ⇑(Tuple.sort (key ∘ xs)) ∧ ys = xs ∘ guess := by
  constructor
  · rintro ⟨⟨bij, payload⟩, sorted, ties⟩
    have data : ys = xs ∘ guess := funext payload
    subst ys
    let perm := Equiv.ofBijective guess bij
    have uniq : perm = Tuple.sort (key ∘ xs) := Tuple.eq_sort_iff.mpr ⟨sorted, ties⟩
    exact ⟨congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) uniq, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨(Tuple.sort _).bijective, fun _ => rfl⟩,
      Tuple.eq_sort_iff.mp (rfl : Tuple.sort (key ∘ xs) = _)⟩

/-- The only order checks required by a stable sort are the adjacent ones. -/
theorem stableGuess_iff_adjacent [LinearOrder κ] (key : α → κ) (xs ys : Fin (n+1) → α)
    (guess : Fin (n+1) → Fin (n+1)) :
    StableGuess key xs ys guess ↔ Valid xs guess ys ∧ ∀ i : Fin n,
      toLex (key (ys i.castSucc), guess i.castSucc) < toLex (key (ys i.succ), guess i.succ) := by
  let rank := fun i => toLex (key (ys i), guess i)
  change StableGuess key xs ys guess ↔ Valid xs guess ys ∧ ∀ i : Fin n, rank i.castSucc < rank i.succ
  rw [← Fin.strictMono_iff_lt_succ]
  constructor
  · rintro ⟨v, sorted, ties⟩
    refine ⟨v, fun i j ij => Prod.Lex.toLex_lt_toLex.mpr ?_⟩
    rcases (sorted ij.le).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, ties i j ij h⟩
  · rintro ⟨v, sorted⟩
    refine ⟨v, monotone_iff_forall_lt.mpr ?_, ?_⟩
    · intro i j ij
      rcases Prod.Lex.toLex_lt_toLex.mp (sorted ij) with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    · intro i j ij h
      exact ((Prod.Lex.toLex_lt_toLex.mp (sorted ij)).resolve_left h.not_lt).2

open scoped BigOperators Classical in
/-- Summing the hidden address guesses contracts one tagged test with the
adjacent checks. Every stable input/output pair contributes the field unit once. -/
theorem stable_sort_contraction {F : Type*} [CommSemiring F] [LinearOrder κ]
    (key : α → κ) (xs ys : Fin (n+1) → α) :
    (∑ g : Fin (n+1) → Fin (n+1),
      (if Valid xs g ys then (1:F) else 0) * (if ∀ i : Fin n,
        toLex (key (ys i.castSucc), g i.castSucc) < toLex (key (ys i.succ), g i.succ)
        then 1 else 0)) =
      if ys = xs ∘ Tuple.sort (key ∘ xs) then 1 else 0 := by
  classical
  let canon : Fin (n+1) → Fin (n+1) := Tuple.sort (key ∘ xs)
  have bit (P Q : Prop) [Decidable P] [Decidable Q] :
      (if P then (1:F) else 0)*(if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
    by_cases h : P <;> by_cases j : Q <;> simp [h,j]
  simp_rw [bit, ← stableGuess_iff_adjacent, stableGuess_iff]
  change (∑ g, if g = canon ∧ ys = xs ∘ g then (1:F) else 0) = if ys = xs ∘ canon then 1 else 0
  by_cases good : ys = xs ∘ canon
  · rw [ite_eq_left good]
    calc
      _ = ∑ g, if g = canon then (1:F) else 0 := by
        apply Finset.sum_congr rfl
        intro g _
        by_cases hit : g = canon <;> simp [hit, good]
      _ = _ := by simp
  · rw [ite_eq_right good]
    apply Finset.sum_eq_zero
    intro g _
    have absent : ¬(g = canon ∧ ys = xs ∘ g) := by
      rintro ⟨rfl, same⟩
      exact good same
    simp [absent]

/-- A stable pass on the next digit refines the order already obtained on the
lower digits. Iterating this identity gives least-significant-digit radix sort. -/
theorem stable_radix_step {δ : Type*} [LinearOrder κ] [LinearOrder δ]
    (hi : Fin n → κ) (lo : Fin n → δ) :
    (Tuple.sort (hi ∘ Tuple.sort lo)).trans (Tuple.sort lo) =
      Tuple.sort (fun i => toLex (hi i, lo i)) := by
  let l := Tuple.sort lo
  let h := Tuple.sort (hi ∘ l)
  have sl := Tuple.eq_sort_iff.mp (rfl : l = Tuple.sort lo)
  have sh := Tuple.eq_sort_iff.mp (rfl : h = Tuple.sort (hi ∘ l))
  apply Tuple.eq_sort_iff.mpr
  constructor
  · apply monotone_iff_forall_lt.mpr
    intro i j ij
    change toLex (hi (l (h i)), lo (l (h i))) ≤ toLex (hi (l (h j)), lo (l (h j)))
    apply Prod.Lex.toLex_le_toLex.mpr
    have hh : hi (l (h i)) ≤ hi (l (h j)) := sh.1 ij.le
    rcases hh.lt_or_eq with strict | tie
    · exact Or.inl strict
    · exact Or.inr ⟨tie, sl.1 (sh.2 i j ij tie).le⟩
  · intro i j ij eq
    have pair : (hi (l (h i)), lo (l (h i))) = (hi (l (h j)), lo (l (h j))) :=
      congrArg ofLex eq
    exact sl.2 _ _ (sh.2 i j ij (congrArg Prod.fst pair)) (congrArg Prod.snd pair)

theorem valid_iff_sorted_scan (source : Fin n → α) (tag : Fin n → Fin n)
    (target : Fin n → α) :
    Valid source tag target ↔ pairedScan source tag target (Tuple.sort tag) := by
  constructor
  · intro valid
    obtain ⟨order, h, _⟩ := (valid_iff_unique_scan ..).mp valid
    have sorted : order = Tuple.sort tag := by
      apply Tuple.eq_sort_iff.mpr
      constructor
      · intro i j hij
        change tag (order i) ≤ tag (order j)
        rw [(h i).1, (h j).1]
        exact hij
      · intro i j hij eq
        exact (hij.ne ((h i).1.symm.trans (eq.trans (h j).1))).elim
    exact sorted ▸ h
  · intro h
    let order := Tuple.sort tag
    change pairedScan source tag target order at h
    have inv (i : Fin n) : tag i = order.symm i := by
      simpa only [Equiv.apply_symm_apply] using (h (order.symm i)).1
    refine ⟨(funext inv) ▸ order.symm.bijective, ?_⟩
    intro i
    simpa only [inv i, Equiv.apply_symm_apply] using (h (order.symm i)).2

/-- A source precedes the targets in the combined input list, so it is the first
record among ties. The second slot of each pair retains the stable target order. -/
def flagged (source : Fin n → α) (tag : Fin n → Fin n) (target : Fin n → α) :
    Fin n ⊕ Fin n → Fin n × Bool × α
  | .inl a => (a, false, source a)
  | .inr i => (tag i, true, target i)

def pairTransport (order : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n ⊕ Fin n) :=
  Equiv.sumCongr (Equiv.refl _) order

theorem valid_iff_flagged_pairs (source : Fin n → α) (tag : Fin n → Fin n) (target : Fin n → α) :
    Valid source tag target ↔ ∀ a,
      let order := pairTransport (Tuple.sort tag)
      [flagged source tag target (order (.inl a)), flagged source tag target (order (.inr a))] =
        [(a, false, source a), (a, true, source a)] := by
  rw [valid_iff_sorted_scan]
  simp [pairedScan, pairTransport, flagged]

/-- Excess entries of a padded tag call have matching fixed input and output addresses. -/
def padTag (d : ℕ) (tag : Fin n → Fin n) (i : Fin (n+d)) : Fin (n+d) :=
  Fin.addCases (motive := fun _ => Fin (n+d)) (fun j => (tag j).castAdd d) (Fin.natAdd n) i

def padPayload (d : ℕ) (zero : α) (x : Fin n → α) (i : Fin (n+d)) : α :=
  Fin.addCases (motive := fun _ => α) x (fun _ => zero) i

/-- Requiring increasing order leaves exactly one way to send dummy sources
to the unoccupied positions of an aligned block. -/
theorem unique_residual_matching {m : ℕ} (source : Finset (Fin n)) (destination : Finset (Fin m))
    (same : source.card = destination.card) :
    ∃! _ : source ≃o destination, True := by
  let a := source.orderIsoOfFin rfl
  let b := destination.orderIsoOfFin same.symm
  exact ⟨a.symm.trans b, trivial, fun _ _ => Subsingleton.elim ..⟩

theorem valid_padded_iff (d : ℕ) (z : α) (x y : Fin n → α) (t : Fin n → Fin n) :
    Valid (padPayload d z x) (padTag d t) (padPayload d z y) ↔ Valid x t y := by
  have left (i : Fin n) : padTag d t (i.castAdd d) = (t i).castAdd d := Fin.addCases_left ..
  have right (j : Fin d) : padTag d t (Fin.natAdd n j) = Fin.natAdd n j := Fin.addCases_right ..
  constructor
  · rintro ⟨bij, data⟩
    have inj : Function.Injective t := by
      intro i j eq
      apply Fin.castAdd_injective n d
      exact bij.1 ((left i).trans ((congrArg (Fin.castAdd d) eq).trans (left j).symm))
    exact ⟨(Finite.injective_iff_bijective).mp inj, fun i => by
      simpa only [left, padPayload, Fin.addCases_left] using data (i.castAdd d)⟩
  · rintro ⟨bij, data⟩
    have surj : Function.Surjective (padTag d t) := by
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        obtain ⟨a, rfl⟩ := bij.2 j
        exact ⟨a.castAdd d, left a⟩
      · intro j
        exact ⟨Fin.natAdd n j, right j⟩
    refine ⟨Finite.surjective_iff_bijective.mp surj, ?_⟩
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [left, padPayload, Fin.addCases_left] using data j
    · intro j
      simp only [right, padPayload, Fin.addCases_right]

/-- The exact number of packs needed for a run. The empty run needs none. -/
def packCount (p r : ℕ) := r / p + if r % p = 0 then 0 else 1

theorem pack_capacity (p r : ℕ) (hp : 0 < p) :
    r ≤ p * packCount p r ∧ p * packCount p r < r + p := by
  have rem := Nat.mod_lt r hp
  have eq := Nat.div_add_mod r p
  by_cases zero : r % p = 0 <;> simp only [packCount, zero, ite_true, ite_false,
    Nat.mul_add, Nat.mul_one, Nat.add_zero] <;> omega

/-- Chunks hold the real prefix of a fixed-width pack. -/
def chunks (p : ℕ) (xs : List α) :=
  (List.replicate (packCount p xs.length) p).splitLengths xs

theorem chunks_read {p : ℕ} (hp : 0 < p) (xs : List α) : (chunks p xs).flatten = xs := by
  apply List.flatten_splitLengths
  simpa [Nat.mul_comm] using (pack_capacity p xs.length hp).1

theorem chunks_width (p : ℕ) (xs : List α) {r : List α} (hr : r ∈ chunks p xs) :
    r.length ≤ p :=
  List.length_mem_splitLengths xs _ p (by simp) r hr

def slots (p : ℕ) (real : List α) : List (Option α) :=
  real.map some ++ List.replicate (p-real.length) none

theorem slots_length {p : ℕ} {real : List α} (h : real.length ≤ p) :
    (slots p real).length = p := by simp [slots]; omega

theorem slots_read (p : ℕ) (real : List α) : (slots p real).filterMap id = real := by
  simp [slots]

section
variable [DecidableEq κ]

/-- Scanning a list in order extracts all real records of a single digit. -/
def bucket (key : α → κ) (a : κ) (xs : List α) := xs.filter fun x => decide (key x = a)

/-- Reading a single digit run after a tagged stable sort gives exactly the
original subsequence, in its original order, even for repeated payloads. -/
theorem stable_sort_bucket {δ : Type*} [LinearOrder δ] (key : Fin n → δ) (a : δ) :
    bucket key a (List.ofFn (Tuple.sort key)) = bucket key a (List.ofFn id) := by
  let order := Tuple.sort key
  have perm : (List.ofFn order).Perm (List.ofFn id) := by
    simpa only [Function.id_comp] using order.ofFn_comp_perm (id : Fin n → Fin n)
  apply List.Perm.eq_of_pairwise' (r := (· ≤ · : Fin n → Fin n → Prop))
  · apply List.pairwise_filter.mpr
    apply List.pairwise_ofFn.mpr
    intro i j ij hi hj
    have equal : key (order i) = key (order j) :=
      (of_decide_eq_true hi).trans (of_decide_eq_true hj).symm
    exact ((Tuple.eq_sort_iff.mp (rfl : order = Tuple.sort key)).2 i j ij equal).le
  · apply List.pairwise_filter.mpr
    apply List.pairwise_ofFn.mpr
    exact fun _ _ ij _ _ => ij.le
  · exact perm.filter _

def digitSort (digits : List κ) (key : α → κ) (xs : List α) :=
  digits.flatMap fun a => bucket key a xs

private theorem length_insert (digits : List κ) (nd : digits.Nodup) (key : α → κ)
    (x : α) (xs : List α) :
    (digitSort digits key (x :: xs)).length =
      (digitSort digits key xs).length + if key x ∈ digits then 1 else 0 := by
  induction digits with
  | nil => simp [digitSort]
  | cons d ds ih =>
    have fresh := (List.nodup_cons.mp nd).1
    change (bucket key d (x :: xs) ++ digitSort ds key (x :: xs)).length =
      (bucket key d xs ++ digitSort ds key xs).length + _
    rw [List.length_append, List.length_append, ih (List.nodup_cons.mp nd).2]
    by_cases eq : key x = d
    · simp [bucket, eq, fresh, Nat.add_comm, Nat.add_left_comm]
    · simp [bucket, eq, Nat.add_assoc]

theorem digitSort_length (digits : List κ) (nd : digits.Nodup) (key : α → κ) (xs : List α)
    (covered : ∀ x ∈ xs, key x ∈ digits) : (digitSort digits key xs).length = xs.length := by
  induction xs with
  | nil => simp [digitSort, bucket]
  | cons x xs ih =>
    rw [length_insert digits nd, ite_eq_left (covered x (by simp)),
      ih (fun y hy => covered y (List.mem_cons_of_mem _ hy))]
    rfl

def blockPacks (p : ℕ) (digits : List κ) (key : α → κ) (xs : List α) :
    List (κ × List α) :=
  digits.flatMap fun a => (chunks p (bucket key a xs)).map fun chunk => (a, chunk)

theorem physical_pack {p : ℕ} (hp : 0 < p) (digits : List κ) (key : α → κ) (xs : List α)
    {pack : κ × List α} (member : pack ∈ blockPacks p digits key xs) :
    (slots p pack.2).length = p ∧ (slots p pack.2).filterMap id = pack.2 ∧
      ∀ x ∈ pack.2, key x = pack.1 := by
  obtain ⟨d, _, hm⟩ := List.mem_flatMap.mp member
  obtain ⟨chunk, hc, rfl⟩ := List.mem_map.mp hm
  refine ⟨slots_length (chunks_width _ _ hc), slots_read .., ?_⟩
  intro x hx
  have present : x ∈ (chunks p (bucket key d xs)).flatten := List.mem_flatten.mpr ⟨_, hc, hx⟩
  rw [chunks_read hp] at present
  exact of_decide_eq_true (List.mem_filter.mp present).2

def unpackKey (a : κ) (packs : List (κ × List α)) :=
  packs.flatMap fun q => if q.1 = a then q.2 else []

private theorem unpack_run {p : ℕ} (hp : 0 < p) (a b : κ) (xs : List α) :
    unpackKey a ((chunks p xs).map fun c => (b,c)) = if b = a then xs else [] := by
  simp only [unpackKey, List.flatMap_map]
  by_cases h : b = a <;> simp [h, chunks_read hp]

theorem unpack_block {p : ℕ} (hp : 0 < p) (a : κ) (digits : List κ) (nd : digits.Nodup)
    (key : α → κ) (xs : List α) :
    unpackKey a (blockPacks p digits key xs) = if a ∈ digits then bucket key a xs else [] := by
  induction digits with
  | nil => simp [blockPacks, unpackKey]
  | cons b ds ih =>
    have fresh := (List.nodup_cons.mp nd).1
    have sub := ih (List.nodup_cons.mp nd).2
    change unpackKey a (((chunks p (bucket key b xs)).map fun c => (b,c)) ++
      blockPacks p ds key xs) = _
    rw [show ∀ u v : List (κ × List α), unpackKey a (u ++ v) = unpackKey a u ++ unpackKey a v
      from fun u v => List.flatMap_append .., unpack_run hp, sub]
    by_cases eq : b = a
    · subst b
      simp [fresh]
    · simp [eq, Ne.symm eq]

theorem block_slots_le {p : ℕ} (hp : 0 < p) (digits : List κ)
    (key : α → κ) (xs : List α) :
    p * (blockPacks p digits key xs).length ≤ (digitSort digits key xs).length + digits.length * p := by
  induction digits with
  | nil => simp [blockPacks, digitSort]
  | cons d ds ih =>
    let r := bucket key d xs
    have cap := (pack_capacity p r.length hp).2.le
    change p * (((chunks p r).map fun c => (d,c)) ++ blockPacks p ds key xs).length ≤
      (r ++ digitSort ds key xs).length + (ds.length + 1) * p
    simp only [List.length_append, List.length_map, chunks, List.length_splitLengths,
      List.length_replicate, Nat.mul_add, Nat.add_mul, Nat.one_mul]
    omega

/-- One block needs fewer than one extra pack per possible digit. This upper
bound can be fixed before the input is supplied. -/
theorem block_padding_budget {p : ℕ} (hp : 0 < p) (digits : List κ)
    (nd : digits.Nodup) (key : α → κ) (xs : List α)
    (covered : ∀ x ∈ xs, key x ∈ digits) :
    p * (blockPacks p digits key xs).length ≤ xs.length + digits.length * p := by
  simpa only [digitSort_length digits nd key xs covered] using block_slots_le hp digits key xs

/-- Stable sorting the emitted packs by their common digit preserves the input order
within every digit, including across block boundaries. -/
theorem packed_digit_correct {p : ℕ} (hp : 0 < p) (digits : List κ) (nd : digits.Nodup)
    (key : α → κ) (blocks : List (List α)) :
    digits.flatMap (fun a => unpackKey a (blocks.flatMap (blockPacks p digits key))) =
      digitSort digits key blocks.flatten := by
  apply List.flatMap_congr
  intro a ha
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.flatten_cons]
    change unpackKey a (blockPacks p digits key b ++ bs.flatMap (blockPacks p digits key)) =
      bucket key a (b ++ bs.flatten)
    rw [show ∀ u v : List (κ × List α), unpackKey a (u ++ v) = unpackKey a u ++ unpackKey a v
      from fun u v => List.flatMap_append .., unpack_block hp _ _ nd, ite_eq_left ha, ih]
    simp only [bucket, List.filter_append]

end

/-- A pass reserves whole blocks and one run-alignment allowance per digit
in each block, including the last partial block. -/
def passSlots (b digits p input : ℕ) := packCount b input * (b + digits * p)

theorem passSlots_le (b digits p input : ℕ) (hb : 0 < b) :
    passSlots b digits p input ≤ input + b + (input / b + 1) * (digits * p) := by
  have packed := (pack_capacity b input hb).2.le
  have count : packCount b input ≤ input / b + 1 := by
    unfold packCount
    split <;> omega
  have used := Nat.mul_le_mul_right (digits * p) count
  unfold passSlots
  rw [Nat.mul_add, Nat.mul_comm (packCount b input) b]
  omega

/-- Finite form of the repeated-pass length estimate. Addressing and digit
width fix every slot budget before any payload is supplied. -/
theorem passes_stay_linear (b digits p n t : ℕ) (hb : 0 < b) (width : ℕ → ℕ)
    (start : width 0 ≤ n)
    (step : ∀ i < t, width (i+1) ≤ passSlots b digits p (width i))
    (room : t * (b + (2*n/b+1)*(digits*p)) ≤ n) :
    ∀ i ≤ t, width i ≤ 2*n := by
  let e := b + (2*n/b+1)*(digits*p)
  have bounds (i : ℕ) (hit : i ≤ t) : width i ≤ n + i*e := by
    induction i with
    | zero => simpa using start
    | succ i ih =>
      have hi : i < t := by omega
      have prev := ih hi.le
      have small := (Nat.mul_le_mul_right e hi.le).trans room
      have cap : width i ≤ 2*n := by omega
      have divs := Nat.div_le_div_right (c := b) cap
      have extra := Nat.mul_le_mul_right (digits*p) (Nat.add_le_add_right divs 1)
      have one := (step i hi).trans (passSlots_le b digits p (width i) hb)
      rw [Nat.succ_mul]
      dsimp [e] at *
      omega
  intro i hi
  have front := bounds i hi
  have total := (Nat.mul_le_mul_right e hi).trans room
  omega

/-- Explicit sufficient conditions for a fixed partial block and all repeated
run alignment to fit in one extra input length. -/
theorem packing_room (b digits p n t : ℕ) (runs : 4*t*(digits*p) ≤ b)
    (last : 2*t*(b+digits*p) ≤ n) :
    t * (b + (2*n/b+1)*(digits*p)) ≤ n := by
  let q := 2*n/b
  have full : 4*(q*(t*(digits*p))) ≤ 2*n := calc
    _ = q*(4*t*(digits*p)) := by ring
    _ ≤ q*b := Nat.mul_le_mul_left _ runs
    _ ≤ 2*n := Nat.div_mul_le_self ..
  have edge : 2*(t*(b+digits*p)) ≤ n := by simpa only [Nat.mul_assoc] using last
  change t*(b+(q+1)*(digits*p)) ≤ n
  rw [show t*(b+(q+1)*(digits*p)) = t*(b+digits*p)+q*(t*(digits*p)) by ring]
  omega

/-- The paper's dyadic budget in bits. The first inequality pays for all
aligned runs, and the second pays for the partially filled final block. -/
theorem dyadic_room (h k j q passes : ℕ) (passBound : passes ≤ 2^q)
    (digitRoom : q+j+3 ≤ k) (lastRoom : q+2*k+2 ≤ h) :
    passes * (2^(2*k) + (2*(2^h)/2^(2*k)+1)*((2^k+1)*2^j)) ≤ 2^h := by
  let a := (2^k+1)*2^j
  let block := 2^(2*k)
  have digit : 2^k+1 ≤ 2^k*2 := by have := Nat.two_pow_pos k; omega
  have run : 4*2^q*a ≤ block := calc
    _ ≤ 4*2^q*((2^k*2)*2^j) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ digit)
    _ = 2^(q+k+j+3) := by simp only [pow_add]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have nonzero := Nat.two_pow_pos q
  have small : a ≤ block := (Nat.le_mul_of_pos_left a (by omega : 0 < 4*2^q)).trans run
  apply packing_room
  · exact (Nat.mul_le_mul_right a (Nat.mul_le_mul_left 4 passBound)).trans run
  · change 2*passes*(block+a) ≤ 2^h
    calc
      _ ≤ 2*2^q*(block+block) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ passBound) (Nat.add_le_add_left small _)
      _ = 2^(q+2*k+2) := by dsimp [block]; simp only [pow_add]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) lastRoom

end Hierarchy.Tagged.Radix

end OAI
