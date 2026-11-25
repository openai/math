import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Transform

/-!
# Matching active rows with multiplicity

An inactive row contributes no condition. Active rows can have
repeated identifiers, so compare the complete records as multisets.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Finset Transcript
open scoped Classical

variable {A I J : Type} [Fintype I] [Fintype J]

def count (x : I → Option A) (a : A) : ℕ := ∑ i, if x i = some a then 1 else 0

def Match (x : I → Option A) (y : J → Option A) : Prop := ∀ a, count x a = count y a

theorem count_ofFn [DecidableEq A] [BEq A] [LawfulBEq A] {n : ℕ} (x : Fin n → A) (a : A) :
    (List.ofFn x).count a = ∑ i, if x i = a then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp [add_comm]

private theorem count_pad {k : ℕ} (e : I ↪ Fin k) (f : Fin k → ℕ)
    (zero : ∀ i, i ∉ Set.range e → f i = 0) :
    ∑ i, f i = ∑ i, f (e i) := by
  rw [← sum_subset (subset_univ (univ.image e)), sum_image e.injective.injOn]
  exact fun i _ h => zero i (by simpa using h)

private theorem paired_iff {h n : ℕ} (rec : Fin n → Val (Messages.row h 0)) :
    paired (List.ofFn rec) ↔
      ∀ z : Val (word h), (∑ i, if rec i = (true, false, z) then 1 else 0) =
        ∑ i, if rec i = (true, true, z) then 1 else 0 := by
  have eq (x y : Val (Messages.row h 0)) :
      Messages.reverse h 0 x = y ↔ x = Messages.reverse h 0 y :=
    (Messages.reverse_involutive h 0).eq_iff
  simp only [paired, List.map_ofFn, List.perm_iff_count, count_ofFn, Function.comp_apply, eq]
  constructor
  · intro H z
    exact H (true, true, z)
  · rintro H ⟨_|_, _|_, z⟩
    · rfl
    · rfl
    · exact (H z).symm
    · exact H z

def flag {A : Type} (v : Bool) (a : A) := if v then some a else none

private theorem pair_iff {h n : ℕ} (rec : Fin n → Val (Messages.row h 0))
    (e : I ⊕ J ↪ Fin n) (a : I → Bool) (b : J → Bool) (f : I → Val (word h))
    (g : J → Val (word h)) (hl : ∀ i, rec (e (.inl i)) = (a i, false, f i))
    (hr : ∀ i, rec (e (.inr i)) = (b i, true, g i))
    (off : ∀ i, i ∉ Set.range e → (rec i).1 = false) :
    paired (List.ofFn rec) ↔ Match (fun i => flag (a i) (f i)) (fun j => flag (b j) (g j)) := by
  rw [paired_iff]
  have sub (t : Bool) (z : Val (word h)) :
      (∑ i, if rec i = (true, t, z) then 1 else 0) =
        ∑ i, if rec (e i) = (true, t, z) then 1 else 0 := by
    refine count_pad e _ fun i hi => ite_eq_right ?_
    intro he
    exact Bool.false_ne_true ((off i hi).symm.trans (congrArg Prod.fst he))
  unfold Match count
  simp only [sub, Fintype.sum_sum_type, hl, hr]
  have hf (v : Bool) (x y : Val (word h)) : flag v x = some y ↔ v = true ∧ x = y := by
    cases v <;> simp [flag]
  simp only [Prod.mk.injEq, true_and, and_false, false_and, Bool.true_eq_false,
    Bool.false_eq_true, ite_false, sum_const_zero, zero_add, add_zero, hf]

variable {X : Type} [Fintype X]

/-- Each row has one activity bit followed by an arbitrary set of
named data bits. Taps may specify constants. -/
abbrev RowTap (X B : Type) := Option B → X ⊕ Bool

def RowTap.read {B : Type} (a : RowTap X B) (x : X → Bool) : Option (B → Bool) :=
  flag (Sum.elim x id (a none)) (fun b => Sum.elim x id (a (some b)))

/-- Two sorts check equality of multisets without any promise that the
active addresses provide a permutation. -/
theorem match_rows {F B : Type} [Field F] [Fintype B] {w j u : ℕ} {L : Set (Table F)}
    (ok : ∀ (_ : LinearOrder (Val (Messages.row (Fintype.card B) 0))),
      Fast F (Messages.row (Fintype.card B) 0) → sorter F (Messages.row (Fintype.card B) 0) j ∈ L)
    (hu : 3 ≤ u) (room : 2 * 2 ^ j * (Fintype.card B + 2) ≤ u) (width : Fintype.card B + 2 ≤ 4 * w)
    (n : Fintype.card I + Fintype.card J ≤ 2 ^ j)
    (f : I → RowTap X B) (g : J → RowTap X B) :
    WideWeight F u L (fun x => if Match (fun i => (f i).read x) (fun i => (g i).read x) then 1 else 0)
      (4 * Fintype.card X + 1000 * 2 ^ j * (1 + w)) := by
  let h := Fintype.card B
  let e : I ⊕ J ↪ Fin (2 ^ j) := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using n))
  let p : slots (word h) ≃ B := Fintype.equivOfCardEq (by simp [h])
  let code : (B → Bool) ≃ Val (word h) := (p.symm.arrowCongr (.refl _)).trans (bits (word h)).symm
  let row (t : Bool) (r : RowTap X B) : slots (Messages.row h 0) → X ⊕ Bool :=
    Sum.elim (fun _ => r none) (Sum.elim (fun _ => .inr t) (fun j => r (some (p j))))
  let tap := Function.extend e (Sum.elim (row false ∘ f) (row true ∘ g)) (fun _ _ => .inr false)
  have H := packet_with F (H := h) (z := 0) ok hu room width tap
  convert H using 1
  funext x
  let recd (i : Fin (2 ^ j)) := (bits (Messages.row h 0)).symm (Sum.elim x id ∘ tap i)
  let a (t : RowTap X B) := Sum.elim x id (t none)
  let b (t : RowTap X B) := code (fun i => Sum.elim x id (t (some i)))
  have hl (i : I) : recd (e (.inl i)) = (a (f i), false, b (f i)) := by
    unfold recd tap
    rw [e.injective.extend_apply]
    rfl
  have hr (i : J) : recd (e (.inr i)) = (a (g i), true, b (g i)) := by
    unfold recd tap
    rw [e.injective.extend_apply]
    rfl
  have off i (hi : i ∉ Set.range e) : (recd i).1 = false := by
    unfold recd tap
    rw [Function.extend_apply' _ _ _ hi]
    rfl
  have he := pair_iff recd e _ _ _ _ hl hr off
  have hv (t : RowTap X B) (z : B → Bool) :
      flag (a t) (b t) = some (code z) ↔ t.read x = some z := by
    unfold RowTap.read flag a b
    split_ifs <;> simp
  have eq : paired (packetRows tap x) ↔ Match (fun i => (f i).read x) (fun i => (g i).read x) := by
    change paired (List.ofFn recd) ↔ _
    rw [he]
    unfold Match count
    constructor
    · intro hm z
      have hx := hm (code z)
      simp only [hv] at hx
      convert! hx using 1 <;> congr! 2
    · intro hm z
      obtain ⟨z, rfl⟩ := code.surjective z
      simp only [hv]
      convert! hm z using 1 <;> congr! 2
  simp only [eq]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end

/-!
# Canonical allocation to bands

A band has a fixed number of rows for one exterior name. Sort the
active data together with empty rows. The multiset fixes the entire
sorted band, so guessing it adds no multiplicity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Finset
open scoped Classical

variable {I J A B : Type} [Fintype I] [Fintype J]

theorem match_map (f : I → Option A) (g : J → Option A) (e : A ↪ B) :
    Match (fun i => (f i).map e) (fun j => (g j).map e) ↔ Match f g := by
  have same (x : Option A) (a : A) : x.map e = some (e a) ↔ x = some a := by
    cases x <;> simp
  unfold Match count
  constructor
  · intro h a
    simpa only [same] using h (e a)
  · intro h b
    by_cases hb : ∃ a, e a = b
    · obtain ⟨a, rfl⟩ := hb
      simpa only [same] using h a
    · have hn (x : Option A) : x.map e ≠ some b := by
        cases x with
        | none => simp
        | some a => exact fun h => hb ⟨a, Option.some.inj h⟩
      simp [hn]

theorem count_pos (f : I → Option A) (a : A) : 0 < count f a ↔ ∃ i, f i = some a := by
  simp only [count, sum_boole, Nat.cast_id, card_pos, filter_nonempty_iff, mem_univ, true_and]

/-- Match transfers any condition on the active records. -/
theorem Match.all {f : I → Option A} {g : J → Option A} (h : Match f g) (P : A → Prop) :
    (∀ i a, f i = some a → P a) ↔ (∀ j a, g j = some a → P a) := by
  have hh a : (∃ i, f i = some a) ↔ ∃ j, g j = some a := by rw [← count_pos, ← count_pos, h a]
  constructor
  · intro h j a he
    obtain ⟨i, hi⟩ := (hh a).mpr ⟨j, he⟩
    exact h i a hi
  · intro h i a he
    obtain ⟨j, hj⟩ := (hh a).mp ⟨i, he⟩
    exact h j a hj

private theorem zeros [Fintype A] (x : I → Option A) :
    (∑ i, if x i = none then 1 else 0) + (∑ a, count x a) = Fintype.card I := by
  unfold count
  rw [sum_comm, ← sum_add_distrib]
  trans ∑ _i : I, 1
  · apply sum_congr rfl
    intro i _
    cases x i <;> simp
  · simp

private theorem monotone_unique [Fintype A] [LinearOrder (Option A)] {n : ℕ}
    (x y : Fin n → Option A) (hx : Monotone x) (hy : Monotone y) (h : Match x y) : x = y := by
  apply List.ofFn_injective
  apply List.Perm.eq_of_pairwise' hx.sortedLE_ofFn.pairwise hy.sortedLE_ofFn.pairwise
  apply List.perm_iff_count.mpr
  intro a
  rw [count_ofFn, count_ofFn]
  cases a with
  | some a => exact h a
  | none =>
    have h₁ := zeros x
    have h₂ := zeros y
    have hs : count x = count y := funext h
    rw [hs] at h₁
    omega

theorem band [Fintype A] [LinearOrder (Option A)] (x : I → Option A) (n : ℕ)
    (cap : (univ.filter fun i => x i ≠ none).card ≤ n) :
    ∃! y : Fin n → Option A, Monotone y ∧ Match x y := by
  let live := univ.filter fun i => x i ≠ none
  obtain ⟨e⟩ : Nonempty (↥live ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe, Fintype.card_fin] using cap)
  let z := Function.extend e (fun i => x i.val) (fun _ => none)
  have he : Match x z := by
    intro a
    unfold count
    rw [← sum_subset (subset_univ live), ← sum_subset (subset_univ (univ.image e))]
    · rw [sum_image e.injective.injOn, ← sum_coe_sort live]
      exact sum_congr rfl fun i _ => by rw [show z (e i) = x i.val from e.injective.extend_apply _ _ _]
    · intro i _ hi
      rw [show z i = none from Function.extend_apply' _ _ _ (by simpa using hi)]
      rfl
    · intro i _ hi
      have : x i = none := by simpa [live] using hi
      simp [this]
  let y := z ∘ Tuple.sort z
  have hy : Match x y := fun a => (he a).trans
    (Equiv.sum_comp (Tuple.sort z) (fun i => if z i = some a then 1 else 0)).symm
  exact ⟨y, ⟨Tuple.monotone_sort z, hy⟩, fun w hw =>
    monotone_unique _ _ hw.1 (Tuple.monotone_sort z) (fun a => (hw.2 a).symm.trans (hy a))⟩

def label (f : I → Option J) (x : I → A) (i : I) := (f i).map (fun j => (j, x i))
def names {n : ℕ} (y : J → Fin n → Option A) (p : J × Fin n) := (y p.1 p.2).map (Prod.mk p.1)

theorem by_name {n : ℕ} (f : I → Option J) (x : I → A) (y : J → Fin n → Option A) :
    Match (label f x) (names y) ↔
      ∀ j, Match (fun i => if f i = some j then some (x i) else none) (y j) := by
  have first (j : J) (a : A) : count (label f x) (j, a) =
      count (fun i => if f i = some j then some (x i) else none) a := by
    unfold count label
    refine sum_congr rfl fun i _ => ?_
    cases he : f i with
    | none => simp [he]
    | some k => by_cases hk : k = j <;> simp [he, hk]
  have second (j : J) (a : A) : count (names y) (j, a) = count (y j) a := by
    unfold count names
    rw [Fintype.sum_prod_type, sum_eq_single j]
    · exact sum_congr rfl fun t _ => by cases y j t <;> simp
    · intro k _ hk
      exact sum_eq_zero fun t _ => by cases y k t <;> simp [hk]
    · simp
  unfold Match
  simp only [Prod.forall, first, second]

/-- Padding and monotonicity remove any selector multiplicity. -/
theorem bands [Fintype A] [LinearOrder (Option A)] (f : I → Option J) (x : I → A) (n : ℕ)
    (cap : ∀ j, count f j ≤ n) :
    ∃! y : J → Fin n → Option A, (∀ j, Monotone (y j)) ∧ Match (label f x) (names y) := by
  have each (j : J) := band (fun i => if f i = some j then some (x i) else none) n
    (by simpa [count, sum_boole] using cap j)
  choose y hy uniq using each
  exact ⟨y, ⟨fun j => (hy j).1, (by_name f x y).mpr fun j => (hy j).2⟩,
    fun t ht => funext fun j => uniq j _ ⟨ht.1 j, (by_name _ _ _).mp ht.2 j⟩⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end

/-! # Canonical Boolean encoding of a band and the adjacent-row check -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Finset Transcript
open scoped Classical

variable {F X Y B I J : Type} [Field F]

def encode (s : Option (B → Bool)) : Option B → Bool
  | none => s.isSome
  | some i => (s.getD (fun _ => false)) i

def decode (f : Option B → Bool) : Option (B → Bool) :=
  if f none then some (fun i => f (some i)) else none

@[simp] theorem decode_encode (s : Option (B → Bool)) : decode (encode s) = s := by
  cases s <;> rfl

abbrev Store (J : Type) (n : ℕ) (B : Type) := J × Fin n × Option B

def line {n : ℕ} (z : Store J n B → Bool) (j : J) (i : Fin n) (p : Option B) := z (j, i, p)

def data {n : ℕ} (z : Store J n B → Bool) (j : J) (i : Fin n) := decode (line z j i)

def Canonical [LinearOrder (Option (B → Bool))] {n : ℕ} (z : Store J n B → Bool) : Prop :=
  (∀ j i, line z j i = encode (data z j i)) ∧ ∀ j, Monotone (data z j)

theorem unique_store [Fintype B] [LinearOrder (Option (B → Bool))] [Fintype I] [Fintype J]
    (f : I → Option J) (x : I → B → Bool) (n : ℕ) (cap : ∀ j, count f j ≤ n) :
    ∃! z : Store J n B → Bool, Canonical z ∧ Match (label f x) (names (data z)) := by
  obtain ⟨y, ⟨hm, hp⟩, uniq⟩ := bands f x n cap
  let z (u : Store J n B) := encode (y u.1 u.2.1) u.2.2
  have eq : data z = y := funext fun j => funext fun i => decode_encode _
  refine ⟨z, ?_, ?_⟩
  · change Canonical z ∧ Match _ (names (data z))
    unfold Canonical
    rw [eq]
    exact ⟨⟨fun _ _ => rfl, hm⟩, hp⟩
  · intro t ht
    have he := uniq _ ⟨ht.1.2, ht.2⟩
    funext ⟨j, i, p⟩
    have := ht.1.1 j i
    rw [he] at this
    exact congrFun this p

private def next {n : ℕ} (k : Fin n) : Fin n :=
  if h : k.val + 1 < n then ⟨k.val + 1, h⟩ else k

private theorem monotone {A : Type} [Preorder A] {n : ℕ} (f : Fin n → A) :
    Monotone f ↔ ∀ i, f i ≤ f (next i) := by
  refine ⟨fun h i => h ?_, fun h => ?_⟩
  · unfold next
    split <;> simp [Fin.le_def]
  cases n with
  | zero => exact fun i => i.elim0
  | succ n =>
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have he : next i.castSucc = i.succ := by ext; simp [next]
    rw [← he]
    exact h _

theorem all_flags [Fintype I] (p : I → Prop) [DecidablePred p] :
    (∏ i, if p i then (1 : F) else 0) = if ∀ i, p i then 1 else 0 := by
  by_cases h : ∀ i, p i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

variable [Fintype X] [Fintype B] [LinearOrder (Option (B → Bool))] [Fintype J]

/-- Verify canonical order and inactive padding by overlapping pairs of
rows. The dictionary needs no name bits. -/
theorem check_store {w j u n : ℕ} (tap : Store J n B → X) (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w)
    (hu : 3 ≤ u) (ha : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ u)
    (small : 2 * (Fintype.card B + 1) < j) (rows : Fintype.card J * n ≤ 2 ^ j) :
    WideWeight F u (Allowed F w) (fun x => if Canonical (x ∘ tap) then 1 else 0)
      (4 * Fintype.card X + 11000 * 2 ^ j * (1 + j)) := by
  let : LE (Option (B → Bool)) := (inferInstance : LinearOrder (Option (B → Bool))).toLE
  let test (a b : Option B → Bool) := a = encode (decode a) ∧ decode a ≤ decode b
  let f (x : Option B ⊕ Option B → Bool) : F :=
    if test (x ∘ Sum.inl) (x ∘ Sum.inr) then 1 else 0
  let read (i : J × Fin n) : Option B ⊕ Option B → X ⊕ Bool :=
    Sum.elim (fun k => .inl (tap (i.1, i.2, k))) (fun k => .inl (tap (i.1, next i.2, k)))
  have h := dictionary hj hj' hu ha (by simpa [two_mul] using small)
    (by simpa using rows) f read
  have eq (x : X → Bool) : (∏ i, f (Sum.elim x id ∘ read i)) =
      if Canonical (x ∘ tap) then 1 else 0 := by
    let z := x ∘ tap
    have eq (i : J × Fin n) : f (Sum.elim x id ∘ read i) =
        if test (line z i.1 i.2) (line z i.1 (next i.2)) then 1 else 0 := rfl
    simp_rw [eq]
    rw [all_flags]
    simp only [Prod.forall, test, forall_and, Canonical, monotone, data, z]
  simp_rw [eq] at h
  intro a i
  obtain ⟨v, hv, hnet⟩ := h a i
  exact ⟨v, hv, hnet.mono le_rfl sort_allowed⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end

/-! # Soundness of checking an exterior band against its original stacks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Finset
open scoped Classical

variable {I J S Q A B : Type} [Fintype I] [Fintype J]

private theorem sum_active [Fintype A] (x : I → Option A) (f : Option A → ℕ) (hf : f none = 0) :
    (∑ i, f (x i)) = ∑ a, count x a * f (some a) := by
  simp only [count, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  cases x i <;> simp [hf, ite_mul]

/-- Expand active records into their active slots. -/
def flatten (f : A → Q → Option B) (x : I → Option A) (i : I × Q) :=
  (x i.1).bind fun a => f a i.2

theorem Match.flatten [Fintype Q] [Fintype A] {x : I → Option A} {y : J → Option A}
    (h : Match x y) (f : A → Q → Option B) :
    Match (flatten f x) (flatten f y) := by
  intro b
  let wt (a : Option A) := ∑ q, if a.bind (fun v => f v q) = some b then 1 else 0
  have zero : wt none = 0 := by simp [wt]
  simp only [count, Fintype.sum_prod_type]
  change ∑ i, wt (x i) = ∑ j, wt (y j)
  rw [sum_active x wt zero, sum_active y wt zero]
  exact sum_congr rfl fun a _ => congrArg (· * wt (some a)) (h a)

theorem originals [Fintype S] (src : S → A) (keys : I → Option S) (payload : I → A)
    (unique : ∀ s, ∃! i, keys i = some s) :
    Match (fun s => some (s, src s)) (label keys payload) ↔
      ∀ i s, keys i = some s → payload i = src s := by
  constructor
  · intro h i s hi
    have ht := (h.all (fun k => k.2 = src k.1)).mp (by intro j _ he; cases he; rfl)
    exact ht i (s, payload i) (by simp [label, hi])
  · intro h
    rintro ⟨s, a⟩
    obtain ⟨i, hi, hu⟩ := unique s
    unfold count
    rw [sum_eq_single s, sum_eq_single i]
    · simp [label, hi, h i s hi]
    · intro j _ hn
      apply ite_eq_right
      intro he
      have hj : keys j = some s := by
        simpa [label, Function.comp_def] using congrArg (Option.map Prod.fst) he
      exact hn (hu j hj)
    · simp
    · intro t _ ht; simp [ht]
    · simp

abbrev Body (Q K P : Type) := Q × (Option K ⊕ P)

def stackRead {K P : Type} (x : Body Q K P → Bool) (q : Q) : Option (K ⊕ P → Bool) :=
  if x (q, .inl none) then some (Sum.elim (fun i => x (q, .inl (some i))) (fun i => x (q, .inr i)))
    else none

def concat {K P : Type} (code : A ↪ (K → Bool)) : A × (P → Bool) ↪ (K ⊕ P → Bool) where
  toFun x := Sum.elim (code x.1) x.2
  inj' _ _ h := Prod.ext (code.injective (congrArg (· ∘ Sum.inl) h)) (congrArg (· ∘ Sum.inr) h)

variable {K P : Type} [Fintype S] [Fintype Q] [Fintype K] [Fintype P] {n : ℕ}

/-- Input locations are known only through the descriptors on the
active internal rows. No addresses of padding stacks are required. -/
theorem compare (f : I → Option J) (g : I → Q → Option S)
    (cover : ∀ j s, ∃! i : I × Q, f i.1 = some j ∧ g i.1 i.2 = some s)
    (code : S ↪ (K → Bool)) (src : J → S → P → Bool)
    (x : I → Body Q K P → Bool)
    (ok : ∀ i j, f i = some j → ∀ q, stackRead (x i) q =
      (g i q).map (fun s => concat code (s, fun p => x i (q, .inr p))))
    (y : J → Fin n → Option (Body Q K P → Bool)) (copied : Match (label f x) (names y)) :
    (∀ j, Match (fun s => some (concat code (s, src j s))) (flatten stackRead (y j))) ↔
      ∀ i j q s, f i = some j → g i q = some s → (fun p => x i (q, .inr p)) = src j s := by
  have each (j : J) : Match (fun s => some (concat code (s, src j s))) (flatten stackRead (y j)) ↔
      ∀ i q s, f i = some j → g i q = some s → (fun p => x i (q, .inr p)) = src j s := by
    let key (t : I × Q) := if f t.1 = some j then g t.1 t.2 else none
    let pay (t : I × Q) (p : P) := x t.1 (t.2, .inr p)
    have hit (a : I × Q) (s : S) : key a = some s ↔ f a.1 = some j ∧ g a.1 a.2 = some s := by
      unfold key; split_ifs <;> simp_all
    have uniq (s : S) : ∃! a, key a = some s := by simpa only [hit] using cover j s
    have eq : flatten stackRead (fun i => if f i = some j then some (x i) else none) =
        fun i => (label key pay i).map (concat code) := by
      funext ⟨i, q⟩
      by_cases hi : f i = some j
      · simp only [flatten, label, key, ite_eq_left hi, Option.bind_some, ok _ _ hi, Option.map_map]
        rfl
      · simp [flatten, label, key, hi]
    have he := ((by_name f x y).mp copied j).flatten stackRead
    rw [eq] at he
    change Match (fun s => (some (s, src j s)).map (concat code)) _ ↔ _
    have transfer (p : S → Option (K ⊕ P → Bool)) :
        Match p (flatten stackRead (y j)) ↔ Match p (fun i => (label key pay i).map (concat code)) :=
      ⟨fun h a => (h a).trans (he a).symm, fun h a => (h a).trans (he a)⟩
    rw [transfer, match_map, originals _ _ _ uniq]
    simp only [hit, Prod.forall, and_imp, pay]
  exact ⟨fun h i j => (each j).mp (h j) i, fun h j => (each j).mpr (fun i => h i j)⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end

/-!
# Supplying exterior addresses from ordinary port headers

Only an active exterior row needs its original name. Its stack
addresses live inside its short descriptor, in the same order as
the payloads. A long sort puts all such descriptors in fixed bands.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Transcript
open scoped Classical

structure Input (X I J S Q N K P : Type) where
  names : J ↪ (N → Bool)
  keys : S ↪ (K → Bool)
  header : I → RowTap X N
  body : I → Body Q K P → X ⊕ Bool
  source : J → S → P → X

namespace Input
variable {X I J S Q N K P : Type} (A : Input X I J S Q N K P)


def payload (x : X → Bool) (i : I) := Sum.elim x id ∘ A.body i

variable [Fintype I] {n : ℕ}

structure Valid (n : ℕ) (x : X → Bool) (f : I → Option J) (id : I → Q → Option S) : Prop where
  names : ∀ i, (A.header i).read x = (f i).map A.names
  stack : ∀ i j, f i = some j → ∀ q, stackRead (A.payload x i) q =
    (id i q).map (fun s => concat A.keys (s, fun p => A.payload x i (q, .inr p)))
  cover : ∀ j s, ∃! a : I × Q, f a.1 = some j ∧ id a.1 a.2 = some s
  cap : ∀ j, count f j ≤ n

def Supplied (x : X → Bool) (f : I → Option J) (id : I → Q → Option S) : Prop :=
  ∀ i j q s, f i = some j → id i q = some s →
    (fun p => A.payload x i (q, .inr p)) = x ∘ A.source j s

variable [Fintype J] [Fintype Q] [Fintype N] [Fintype K] [Fintype P] [Fintype X]
  {F : Type} [Field F] {j w u : ℕ}

local notation "Z" => Store J n (Body Q K P)
local notation "B" => N ⊕ Body Q K P

theorem long_sort (hu : 3 ≤ u) (hj : w ≤ j) (hj' : j ≤ 2 * w)
    (room : 2 * 2 ^ j * (Fintype.card B + 2) ≤ u)
    (hb : w ≤ Fintype.card B + 2) (hw : Fintype.card B + 2 ≤ 4 * w)
    (hn : Fintype.card I + Fintype.card J * n ≤ 2 ^ j) :
    ∃ f : (X ⊕ Z → Bool) → F,
      WideWeight F u (Allowed F w) f (4 * Fintype.card (X ⊕ Z) + 1000 * 2 ^ j * (1 + w)) ∧
      ∀ (x : X → Bool) (own : I → Option J),
        (∀ i, (A.header i).read x = (own i).map A.names) → ∀ z : Z → Bool,
        f (Sum.elim x z) = if Match (label own (A.payload x)) (Exterior.names (data z)) then 1 else 0 := by
  let left (i : I) : RowTap (X ⊕ Z) B
    | none => Sum.map Sum.inl id (A.header i none)
    | some (.inl k) => Sum.map Sum.inl id (A.header i (some k))
    | some (.inr k) => Sum.map Sum.inl id (A.body i k)
  let right (q : J × Fin n) : RowTap (X ⊕ Z) B
    | none => .inl (.inr (q.1, q.2, none))
    | some (.inl k) => .inr (A.names q.1 k)
    | some (.inr k) => .inl (.inr (q.1, q.2, some k))
  let a := Messages.row (Fintype.card B) 0
  have ha : wd a = Fintype.card B + 2 := wd_word _
  have ok (o : LinearOrder (Val a)) (hf : Fast F a) : sorter F a j ∈ Allowed F w :=
    .inl ⟨j, a, o, hf, hj, hj', hb.trans_eq ha.symm, ha.le.trans hw, rfl⟩
  have h := match_rows ok hu room hw (by simpa using hn) left right
  refine ⟨_, h, fun x own ho z => ?_⟩
  have eval (k : X ⊕ Bool) : Sum.elim (Sum.elim x z) id (Sum.map Sum.inl id k) = Sum.elim x id k := by
    cases k <;> rfl
  have hl (i : I) : (left i).read (Sum.elim x z) =
      (label own (A.payload x) i).map (concat A.names) := by
    let head := (A.header i).read x
    have key : (left i).read (Sum.elim x z) = head.map (fun f => Sum.elim f (A.payload x i)) := by
      change (if _ then some _ else none) = Option.map _ (if _ then some _ else none)
      simp only [left, eval]
      split_ifs
      · apply congrArg some
        funext k; cases k <;> exact eval _
      · rfl
    rw [key, show head = _ from ho i]
    cases he : own i <;> simp only [label, he, Option.map_none, Option.map_some]
    rfl
  have hr (i : J × Fin n) : (right i).read (Sum.elim x z) =
      (Exterior.names (data z) i).map (concat A.names) := by
    change (if z (i.1, i.2, none) then some _ else none) =
      Option.map _ (Option.map _ (if z (i.1, i.2, none) then some _ else none))
    split_ifs
    · apply congrArg some
      funext k; cases k <;> rfl
    · rfl
  simp only [hl, hr, match_map]

end Input
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end

/-! # Checking the contents of each exterior band by short sorts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior.Input
open Transcript
open scoped Classical

variable {X I J S Q N K P : Type} [Fintype X] [Fintype J] [Fintype S]
  [Fintype Q] [Fintype K] [Fintype P] (A : Input X I J S Q N K P)
  {F : Type} [Field F] {w h u n : ℕ}

local notation "Z" => Store J n (Body Q K P)
local notation "B" => Body Q K P

def Short (x : X → Bool) (z : Z → Bool) : Prop :=
  ∀ j, Match (fun s => some (concat A.keys (s, x ∘ A.source j s))) (flatten stackRead (data z j))

/-- Each short sort uses only a stack identifier and one stack. It
does not carry a host address or the name of the exterior bit. -/
theorem short_sort [LinearOrder (Option (B → Bool))] (hu : 3 ≤ u)
    (size : Fintype.card S + n * Fintype.card Q ≤ 2 ^ h)
    (small : 2 * 2 ^ h * (Fintype.card K + Fintype.card P + 2) ≤ min u (min (2 ^ ((Nat.clog 2 w) ^ 3)) (2 ^ (w / 2)))) :
    ∃ f : (X ⊕ Z → Bool) → F,
      WideWeight F u (Allowed F w) f
        (8 * Fintype.card (X ⊕ Z) + 10000 * Fintype.card J * 2 ^ h * (Fintype.card K + Fintype.card P + 3)) ∧
      ∀ x z, Canonical z → f (Sum.elim x z) = if A.Short x z then 1 else 0 := by
  let L := Fintype.card (K ⊕ P)
  let T := (S × P) ⊕ (Fin n × B)
  let left (s : S) : RowTap T (K ⊕ P)
    | none => .inr true
    | some (.inl i) => .inr (A.keys s i)
    | some (.inr i) => .inl (.inl (s, i))
  let right (c : Fin n × Q) : RowTap T (K ⊕ P)
    | none => .inl (.inr (c.1, c.2, .inl none))
    | some (.inl i) => .inl (.inr (c.1, c.2, .inl (some i)))
    | some (.inr i) => .inl (.inr (c.1, c.2, .inr i))
  let b := Messages.row L 0
  have hb : wd b = L + 2 := wd_word _
  have hl : L = Fintype.card K + Fintype.card P := Fintype.card_sum
  have ok (o : LinearOrder (Val b)) (hf : Fast F b) : sorter F b h ∈ Allowed F w := by
    refine Or.inr ⟨sort_cheap _ _ hf _ (by omega), ?_⟩
    rw [arity_sorter, hb, hl]
    exact le_min_iff.mp (le_min_iff.mp small).2
  let f (x : T → Bool) : F := if Match (fun i => (left i).read x) (fun c => (right c).read x) then 1 else 0
  let cost := 4 * Fintype.card T + 1000 * 2 ^ h * (1 + (L + 2))
  have key : WideWeight F u (Allowed F w) f cost :=
    match_rows (w := L + 2) ok hu (by simpa using (le_min_iff.mp small).1)
      (by unfold L; omega) (by simpa using size) left right
  let loc (j : J) : T → X ⊕ Z
    | .inl (s, t) => .inl (A.source j s t)
    | .inr (i, k) => .inr (j, i, some k)
  have net := wide_sum (fun _ : J => f) (fun i t => (Sum.inl (loc i t) : (X ⊕ Z) ⊕ Empty))
    (fun _ => cost) hu (fun _ => key)
  let g (x : X ⊕ Z → Bool) := ∏ j, f (x ∘ loc j)
  have hg : WideWeight F u (Allowed F w) g (8 * Fintype.card (X ⊕ Z) + 9 * (Fintype.card J * cost)) := by
    convert net using 1
    · funext x; simp [g, weightedSum, Function.comp_def]
    · simp
  refine ⟨g, ?_, fun x z hp => ?_⟩
  · have hT : Fintype.card T ≤ 2 ^ h * (L + 1) := by
      simp only [T, Body, Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_fin, hl]
      have := Nat.mul_le_mul_right (Fintype.card K + Fintype.card P + 1) size
      nlinarith only [this, Nat.zero_le (Fintype.card S * Fintype.card K), Nat.zero_le (Fintype.card S)]
    have hc : 9 * cost ≤ 10000 * 2 ^ h * (L + 3) := by
      unfold cost
      nlinarith only [hT, Nat.zero_le (2 ^ h), Nat.zero_le (2 ^ h * L)]
    intro a ix
    obtain ⟨v, hv, hn⟩ := hg a ix
    refine ⟨v, hv.trans (Nat.add_le_add_left ?_ _), hn⟩
    rw [← hl]
    nlinarith only [Nat.mul_le_mul_left (Fintype.card J) hc]
  · have hleft j s : (left s).read (Sum.elim x z ∘ loc j) =
        some (concat A.keys (s, x ∘ A.source j s)) := by
      apply congrArg some
      funext i; cases i <;> rfl
    have hright (j : J) (a : Fin n × Q) :
        (right a).read (Sum.elim x z ∘ loc j) = flatten stackRead (data z j) a := by
      let y := line z j a.1
      have he : (right a).read (Sum.elim x z ∘ loc j) = stackRead (y ∘ some) a.2 := by
        change (if y _ then some _ else none) = (if y _ then some _ else none)
        split_ifs
        · apply congrArg some
          funext i; cases i <;> rfl
        · rfl
      have hc : y = encode (data z j a.1) := hp.1 _ _
      rw [he, hc]
      unfold flatten
      cases data z j a.1 <;> rfl
    change (∏ j, f (Sum.elim x z ∘ loc j)) = _
    simp only [f, hleft, hright]
    rw [all_flags]
    unfold Short
    congr! 1

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior.Input
end

/-!
# Exterior supply without a prescribed permutation of the blocks

Use one long sort to identify the assigned bands, a dictionary to
make their ordering and padding unique, and one short sort per
exterior name to compare each complete stack.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior.Input
open Transcript Finset
open scoped Classical

variable {X Z F : Type} [Field F] [Fintype X] [Fintype Z] {w u : ℕ}

private theorem combine {a b c : (X ⊕ Z → Bool) → F} {p q r : ℕ} (hu : 3 ≤ u)
    (ha : WideWeight F u (Allowed F w) a p)
    (hb : WideWeight F u (Allowed F w) b q)
    (hc : WideWeight F u (Allowed F w) c r) :
    WideWeight F u (Allowed F w)
      (fun x => ∑ z, a (Sum.elim x z) * b (Sum.elim x z) * c (Sum.elim x z))
      (8 * Fintype.card (X ⊕ Z) + 9 * (p + q + r)) := by
  let f : Fin 3 → (X ⊕ Z → Bool) → F := ![a, b, c]
  let t : Fin 3 → ℕ := ![p, q, r]
  have h : ∀ i, WideWeight F u (Allowed F w) (f i) (t i) := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  convert wide_sum f (fun _ => id) t hu h using 1
  · funext x
    simp [weightedSum, Fin.prod_univ_three, f]
  · simp [Fin.sum_univ_three, t]

variable {I J S Q N K P : Type} [Fintype I] [Fintype J] [Fintype S]
  [Fintype Q] [Fintype N] [Fintype K] [Fintype P]
  (A : Input X I J S Q N K P) {h j n : ℕ}

local notation "B" => Body Q K P
local notation "Tape" => Store J n B

/-- On any valid assignment of row names and local stack addresses,
the test compares exactly the required exterior bits. It receives no
inverse permutation or addresses for empty slots. -/
theorem supply (hu : 3 ≤ u) (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w)
    (ha : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ u)
    (low : w ≤ Fintype.card N + Fintype.card B + 2)
    (high : Fintype.card N + Fintype.card B + 2 ≤ 4 * w)
    (small : 2 * (Fintype.card B + 1) < j)
    (rows : Fintype.card I + Fintype.card J * n ≤ 2 ^ j)
    (size : Fintype.card S + n * Fintype.card Q ≤ 2 ^ h)
    (arity : 2 * 2 ^ h * (Fintype.card K + Fintype.card P + 2) ≤ min u (min (2 ^ ((Nat.clog 2 w) ^ 3)) (2 ^ (w / 2)))) :
    ∃ f : (X → Bool) → F,
      WideWeight F u (Allowed F w) f
        (1000000 * (Fintype.card X + 2 ^ j * (1 + w) + Fintype.card J * 2 ^ h * (Fintype.card K + Fintype.card P + 3))) ∧
      ∀ x owner idx, A.Valid n x owner idx → f x = if A.Supplied x owner idx then 1 else 0 := by
  let order := Fintype.equivFin (Option (B → Bool))
  let : LinearOrder (Option (B → Bool)) := LinearOrder.lift' order order.injective
  have room : 2 * 2 ^ j * (Fintype.card (N ⊕ B) + 2) ≤ u := by
    rw [Fintype.card_sum]
    calc
      _ ≤ 2 * 2 ^ j * (4 * w) := Nat.mul_le_mul_left _ high
      _ ≤ 2 * 2 ^ (j + 1) * (2 * j + 2) := by rw [pow_succ]; nlinarith only [Nat.mul_le_mul_left (2 ^ j) hj, Nat.zero_le (2 ^ j)]
      _ ≤ _ := ha
  obtain ⟨f, hf, ef⟩ := A.long_sort (F := F) hu hj (by omega) room
    (by rwa [Fintype.card_sum]) (by rwa [Fintype.card_sum]) rows
  have ht := check_store (F := F) (Sum.inr : Tape → X ⊕ Tape) hj hj' hu ha small (by omega)
  obtain ⟨g, hg, eg⟩ := A.short_sort (F := F) hu size arity
  let check (x : X → Bool) (z : Tape → Bool) :=
    f (Sum.elim x z) * (if Canonical z then 1 else 0) * g (Sum.elim x z)
  refine ⟨fun x => ∑ z, check x z, ?_, ?_⟩
  · have net := combine hu hf ht hg
    intro a ix
    obtain ⟨v, hv, hn⟩ := net a ix
    refine ⟨v, hv.trans ?_, hn⟩
    have hstore : Fintype.card Tape ≤ 2 ^ j * w := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_option, ← mul_assoc]
      exact Nat.mul_le_mul (by omega) (by omega)
    rw [Fintype.card_sum]
    have hh := Nat.mul_le_mul_left (2 ^ j) hj'
    have hshort := Nat.zero_le (Fintype.card J * 2 ^ h * (Fintype.card K + Fintype.card P + 3))
    nlinarith only [hh, hstore, Nat.zero_le (2 ^ j), Nat.zero_le (2 ^ j * w),
      Nat.zero_le (Fintype.card X), hshort]
  · intro x owner idx hvalid
    obtain ⟨z, ⟨hz, hcopy⟩, uniq⟩ := unique_store owner (A.payload x) n hvalid.cap
    change (∑ z, check x z) = _
    rw [sum_eq_single z]
    · unfold check
      rw [ef x owner hvalid.names, ite_eq_left hcopy, ite_eq_left hz, one_mul, one_mul, eg x z hz]
      have hs : A.Short x z ↔ A.Supplied x owner idx :=
        compare owner idx hvalid.cover A.keys (fun j s => x ∘ A.source j s)
          (A.payload x) hvalid.stack (data z) hcopy
      simp only [hs]
    · intro t _ hn
      unfold check
      by_cases hp : Canonical t
      · have hc : ¬Match (label owner (A.payload x)) (Exterior.names (data t)) :=
          fun hh => hn (uniq _ ⟨hp, hh⟩)
        rw [ef x owner hvalid.names, ite_eq_right hc, zero_mul, zero_mul]
      · rw [ite_eq_right hp, mul_zero, zero_mul]
    · simp

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior.Input
end
