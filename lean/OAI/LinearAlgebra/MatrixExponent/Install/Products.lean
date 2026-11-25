import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Network
import OAI.LinearAlgebra.MatrixExponent.Radix.WideTag
import OAI.LinearAlgebra.MatrixExponent.Lookup.Defs
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Network.Dense
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortBack

section
/-! # Products of local weights on named bit indices -/

namespace OAI.LinearAlgebra.MatrixExponent.Install.Weight

variable {F I J A : Type} [Field F] [Fintype I] [Fintype J] [Fintype A]
  {m n : ℕ} {f : (I → Bool) → F}

theorem dense (F I : Type) [Field F] [Fintype I] (f : (I → Bool) → F) :
    Weight F f (8 * 2 ^ Fintype.card I) := by
  intro a e
  obtain ⟨v, h, hv⟩ := Net.dense a .unit (fun x _ => f (bits a x ∘ e))
  exact ⟨v, by simpa [Fintype.card_congr e, wd] using hv, h⟩

theorem parallel {g : (J → Bool) → F} (h : Weight F f m) (k : Weight F g n) :
    Weight F (fun x => f (x ∘ Sum.inl) * g (x ∘ Sum.inr)) (m + n) := by
  let a := word (Fintype.card I)
  let b := word (Fintype.card J)
  let i : I ≃ slots (word (Fintype.card I)) := Fintype.equivOfCardEq (by simp)
  let j : J ≃ slots (word (Fintype.card J)) := Fintype.equivOfCardEq (by simp)
  obtain ⟨v, hv, h⟩ := h a i
  obtain ⟨w, hw, k⟩ := k b j
  apply of_layout (a := .pair a b) (i.sumCongr j)
  exact ⟨v + w, Nat.add_le_add hv hw, (h.par k).post (.unit' _)⟩

theorem pull (h : Weight F f m) (e : I → J) :
    Weight F (fun x => f (x ∘ e)) (Fintype.card J + 2 * Fintype.card I + m) := by
  have hp : BNet F (fun x => x ∘ e) (Fintype.card J + 2 * Fintype.card I) := by
    intro a b i j
    rw [Fintype.card_congr i, Fintype.card_congr j, card_slots, card_slots]
    exact project_net F (i ∘ e ∘ j.symm)
  exact hp.weight h

theorem mul {g : (I → Bool) → F} (h : Weight F f m) (k : Weight F g n) :
    Weight F (fun x => f x * g x) (5 * Fintype.card I + m + n) := by
  have hp := (h.parallel k).pull (Sum.elim id id)
  exact hp.mono (by rw [Fintype.card_sum]; omega)

theorem finite_product (f : A → (I → Bool) → F) (h : ∀ a, Weight F (f a) m) :
    Weight F (fun x => ∏ a, f a x)
      (Fintype.card I + Fintype.card A * (5 * Fintype.card I + m)) := by
  classical
  suffices ∀ u : Finset A, Weight F (fun x => ∏ a ∈ u, f a x)
    (Fintype.card I + u.card * (5 * Fintype.card I + m)) from this Finset.univ
  intro u
  induction u using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, zero_mul, add_zero]
    intro a e
    rw [Fintype.card_congr e, card_slots]
    exact DNet.discard F a
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    exact ((h a).mul ih).mono (by rw [add_mul]; omega)

end OAI.LinearAlgebra.MatrixExponent.Install.Weight
end

section
/-!
# Sparse assignment

Candidate `i` has six possible links. In each synchronous round an
active candidate takes its first uncontested link, if any. No still
active candidate can subsequently use that target.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

abbrev Candidate (n : ℕ) := Fin (2 * n)
abbrev Link (n : ℕ) := Candidate n × Fin 6
abbrev Status (n : ℕ) := Candidate n × Option (Fin 6)
abbrev Graph (n : ℕ) := Candidate n → Fin 6 → Fin n

variable {n : ℕ}

def Expands (g : Graph n) : Prop :=
  ∀ S : Finset (Candidate n), S.card * 131072 ≤ n →
    4 * S.card ≤ (S.biUnion (fun i => Finset.univ.image (g i))).card

def degree (g : Graph n) (S : Finset (Candidate n)) (j : Fin n) : ℕ :=
  ((S ×ˢ Finset.univ).filter (fun e => g e.1 e.2 = j)).card

def remain (g : Graph n) (S : Finset (Candidate n)) : Finset (Candidate n) :=
  S.filter (fun i => ∀ k, degree g S (g i k) ≠ 1)

def rounds (n : ℕ) : ℕ := 4 * (Nat.clog 2 n + 1)

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# Peeling sparse sets

Every reached target accounts for two links when links from retiring
sources are counted twice. This remains valid for parallel links.
Expansion therefore guarantees that at least a third of the sources retire.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {n : ℕ} {g : Graph n}

theorem remain_subset (g : Graph n) (S : Finset (Candidate n)) : remain g S ⊆ S :=
  Finset.filter_subset _ _

private theorem peel (he : Expands g) (S : Finset (Candidate n)) (hs : S.card * 131072 ≤ n) :
    3 * (remain g S).card ≤ 2 * S.card := by
  let U := S.biUnion (fun i => Finset.univ.image (g i))
  have sum_deg (T : Finset (Candidate n)) (hT : T ⊆ S) :
      ∑ j ∈ U, degree g T j = 6 * T.card := by
    have h : Set.MapsTo (fun e : Link n => g e.1 e.2)
        (↑(T ×ˢ (Finset.univ : Finset (Fin 6)))) ↑U := by
      intro e h
      exact Finset.mem_biUnion.mpr ⟨e.1, hT (Finset.mem_product.mp h).1,
        Finset.mem_image.mpr ⟨e.2, Finset.mem_univ _, rfl⟩⟩
    simpa [degree, mul_comm] using (Finset.card_eq_sum_card_fiberwise h).symm
  have bound (j) (hj : j ∈ U) : 2 ≤ degree g S j + degree g (S \ remain g S) j := by
    obtain ⟨i, hi, hk⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hk
    have pos (T : Finset (Candidate n)) (hi : i ∈ T) : 0 < degree g T (g i k) :=
      Finset.card_pos.mpr ⟨(i, k), by simp [hi]⟩
    have := pos S hi
    by_cases h : degree g S (g i k) = 1
    · have ni : i ∉ remain g S := fun hr => (Finset.mem_filter.mp hr).2 k h
      have := pos _ (Finset.mem_sdiff.mpr ⟨hi, ni⟩)
      omega
    · omega
  have ht := Finset.sum_le_sum bound
  rw [Finset.sum_add_distrib, sum_deg _ (by rfl), sum_deg _ Finset.sdiff_subset] at ht
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at ht
  have hc := Finset.card_sdiff_add_card_eq_card (remain_subset g S)
  have hex : 4 * S.card ≤ U.card := he S hs
  omega

theorem cleared {n : ℕ} {g : Graph n} (hn : 0 < n) (he : Expands g)
    (S : Finset (Candidate n)) (hs : S.card * 131072 ≤ n) :
    (remain g)^[rounds n] S = ∅ := by
  have keep (T : Finset (Candidate n)) (hT : T.card * 131072 ≤ n) :
      (remain g T).card * 131072 ≤ n :=
    (Nat.mul_le_mul_right _ (Finset.card_le_card (remain_subset g T))).trans hT
  have aux (k : ℕ) (T : Finset (Candidate n)) (hT : T.card * 131072 ≤ n)
      (hsize : T.card < 2 ^ k) : (remain g)^[4 * k] T = ∅ := by
    induction k generalizing T with
    | zero => exact Finset.card_eq_zero.mp (by simpa using hsize)
    | succ k ih =>
      have h₁ := peel he T hT
      have h₂ := peel he _ (keep _ hT)
      have h₃ := peel he _ (keep _ (keep _ hT))
      have h₄ := peel he _ (keep _ (keep _ (keep _ hT)))
      have half : 2 * ((remain g)^[4] T).card ≤ T.card := by
        change 2 * (remain g (remain g (remain g (remain g T)))).card ≤ T.card
        omega
      rw [Nat.mul_succ, Function.iterate_add_apply]
      rw [pow_succ] at hsize
      exact ih _ (keep _ (keep _ (keep _ (keep _ hT)))) (by omega)
  apply aux _ S hs
  have hp := Nat.le_pow_clog (by decide : 1 < 2) n
  rw [pow_succ]
  omega

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# Deterministic sparse assignment

Only the activity bits and the six selected-link bits at each candidate
are stored. A retiring candidate takes its first uncontested link.
The invariant forbids every active candidate from hitting an occupied
target, so a later round can never reuse that target.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {n : ℕ}

def active (x : Status n → Bool) : Finset (Candidate n) :=
  Finset.univ.filter (fun i => x (i, none))

def init (mask : Candidate n → Bool) : Status n → Bool
  | (i, none) => mask i
  | (_, some _) => false

def first (g : Graph n) (S : Finset (Candidate n)) (i : Candidate n) : Option (Fin 6) :=
  let ks := Finset.univ.filter (fun k => degree g S (g i k) = 1)
  if h : ks.Nonempty then some (ks.min' h) else none

def step (g : Graph n) (x : Status n → Bool) : Status n → Bool
  | (i, none) => x (i, none) && (first g (active x) i).isNone
  | (i, some k) => x (i, some k) || (x (i, none) && decide (first g (active x) i = some k))

def assign (g : Graph n) (mask : Candidate n → Bool) (i : Candidate n) (k : Fin 6) : Bool :=
  (step g)^[rounds n] (init mask) (i, some k)

variable {g : Graph n} {S : Finset (Candidate n)} {mask : Candidate n → Bool}
variable {x : Status n → Bool} {i j : Candidate n} {k l : Fin 6}

@[simp] theorem mem_active : i ∈ active x ↔ x (i, none) = true := by simp [active]

private theorem first_none : first g S i = none ↔ ∀ k, degree g S (g i k) ≠ 1 := by
  simp [first, Finset.filter_nonempty_iff]

private theorem first_unique (hi : i ∈ S) (hj : j ∈ S)
    (hk : first g S i = some k) (h : g i k = g j l) : i = j := by
  have hd : degree g S (g i k) = 1 := by
    unfold first at hk
    dsimp only at hk
    split at hk
    · rename_i has
      cases Option.some.inj hk
      exact (Finset.mem_filter.mp (Finset.min'_mem _ has)).2
    · cases hk
  unfold degree at hd
  have eq : (i, k) = (j, l) := Finset.card_le_one.mp hd.le _ (by simp [hi]) _ (by simp [hj, h])
  exact congrArg Prod.fst eq

private theorem after_active : i ∈ active (step g x) ↔ i ∈ active x ∧ first g (active x) i = none := by
  simp [mem_active, step]

private theorem after_select : step g x (i, some k) = true ↔
    x (i, some k) = true ∨ i ∈ active x ∧ first g (active x) i = some k := by
  simp [step]

private theorem active_iterate (r : ℕ) :
    active ((step g)^[r] x) = (remain g)^[r] (active x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [Function.iterate_succ_apply', ← ih]
    ext i
    rw [after_active, first_none, remain, Finset.mem_filter]

private structure Valid (g : Graph n) (mask : Candidate n → Bool) (x : Status n → Bool) : Prop where
  cover : ∀ i, mask i = true ↔ i ∈ active x ∨ ∃ k, x (i, some k) = true
  unique : ∀ {i k l}, x (i, some k) = true → x (i, some l) = true → k = l
  separate : ∀ {i j k l}, x (i, some k) = true → x (j, some l) = true → g i k = g j l → i = j
  free : ∀ {i j k l}, x (i, some k) = true → j ∈ active x → g i k ≠ g j l

private theorem Valid.next (H : Valid g mask x) : Valid g mask (step g x) := by
  constructor
  · intro i
    rw [H.cover, after_active]
    simp only [after_select]
    cases first g (active x) i <;> aesop
  · intro i k l hk hl
    rcases after_select.mp hk with hk | ⟨hi, hk⟩ <;>
      rcases after_select.mp hl with hl | ⟨hi', hl⟩
    · exact H.unique hk hl
    · exact (H.free hk hi' rfl).elim
    · exact (H.free hl hi rfl).elim
    · exact Option.some.inj (hk.symm.trans hl)
  · intro i j k l hk hl heq
    rcases after_select.mp hk with hk | ⟨hi, hk⟩ <;>
      rcases after_select.mp hl with hl | ⟨hj, hl⟩
    · exact H.separate hk hl heq
    · exact (H.free hk hj heq).elim
    · exact (H.free hl hi heq.symm).elim
    · exact first_unique hi hj hk heq
  · intro i j k l hk hj heq
    obtain ⟨ha, he⟩ := after_active.mp hj
    rcases after_select.mp hk with hk | ⟨hi, hk⟩
    · exact H.free hk ha heq
    · rw [first_unique hi ha hk heq, he] at hk
      cases hk

private theorem valid_iterate (g : Graph n) (mask : Candidate n → Bool) (r : ℕ) :
    Valid g mask ((step g)^[r] (init mask)) := by
  induction r with
  | zero =>
    rw [Function.iterate_zero_apply]
    constructor <;> simp [init]
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact ih.next

theorem assign_iff (hn : 0 < n) (he : Expands g) (hs : (active (init mask)).card * 131072 ≤ n)
    (i : Candidate n) : (∃ k, assign g mask i k = true) ↔ mask i = true := by
  have h := (valid_iterate g mask (rounds n)).cover i
  rw [active_iterate, cleared hn he _ hs] at h
  simpa [assign] using h.symm

theorem assign_unique (hx : assign g mask i k = true) (hy : assign g mask i l = true) : k = l :=
  (valid_iterate g mask (rounds n)).unique hx hy

theorem assign_injective (hx : assign g mask i k = true) (hy : assign g mask j l = true)
    (h : g i k = g j l) : i = j :=
  (valid_iterate g mask (rounds n)).separate hx hy h

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# Switching the payload after sparse assignment

Keep the activation mask separate from the payload bits, so only the
control bits need to pass through each round of the assignment algorithm.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

abbrev Bus (I J : Type) := I ⊕ (I × J)
abbrev Records (I J : Type) := Bus I J → Bool

variable {I K L J : Type} [Fintype I] [Fintype K] [Fintype L]

def marked (x : Records I J) : Finset I := Finset.univ.filter (fun i => x (.inl i))

@[simp] theorem mem_marked {x : Records I J} {i : I} :
    i ∈ marked x ↔ x (.inl i) = true := by simp [marked]

def Carries (x : Records I J) (y : Records K J) : Prop :=
  ∃ f : marked x ≃ marked y, ∀ (i : marked x) j, y (.inr (f i, j)) = x (.inr (i, j))

theorem Carries.card {x : Records I J} {y : Records K J} (h : Carries x y) :
    (marked y).card = (marked x).card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr h.choose).symm

theorem Carries.trans {x : Records I J} {y : Records K J} {z : Records L J}
    (h : Carries x y) (g : Carries y z) : Carries x z :=
  ⟨h.choose.trans g.choose, fun i j => (g.choose_spec _ j).trans (h.choose_spec i j)⟩

variable {n : ℕ} (g : Graph n)

abbrev Traffic (n : ℕ) (J : Type) := Link n ⊕ (Candidate n × J)

def signal (x : Records (Candidate n) J) : Traffic n J → Bool :=
  Sum.elim (fun e => assign g (x ∘ Sum.inl) e.1 e.2) (x ∘ Sum.inr)

def into (i : Fin n) : Finset (Link n) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun e => g e.1 e.2 = i)

@[simp] theorem mem_into (e : Link n) (i : Fin n) : e ∈ into g i ↔ g e.1 e.2 = i := by
  simp [into]

def switch (x : Traffic n J → Bool) : Records (Fin n) J
  | .inl i => decide (∃ e ∈ into g i, x (.inl e) = true)
  | .inr (i, j) => decide (∃ e ∈ into g i, x (.inl e) = true ∧ x (.inr (e.1, j)) = true)

theorem depends_switch (h : ∀ i, degree g Finset.univ i ≤ 24) : Depends (switch (J := J) g) 48 := by
  classical
  let flags (i : Fin n) := (into g i).image (Sum.inl : Link n → Traffic n J)
  have hf (i) : (flags i).card ≤ 24 := Finset.card_image_le.trans (h i)
  rintro (i | ⟨i, j⟩)
  · refine ⟨flags i, (hf i).trans (by decide), fun x y he => ?_⟩
    simp only [switch, decide_eq_decide]
    apply exists_congr
    intro e
    exact and_congr_right fun hi => by rw [he _ (Finset.mem_image_of_mem _ hi)]
  · let data := (into g i).image (fun e => (Sum.inr (e.1, j) : Traffic n J))
    have hd : data.card ≤ 24 := Finset.card_image_le.trans (h i)
    refine ⟨flags i ∪ data, (Finset.card_union_le ..).trans (Nat.add_le_add (hf i) hd),
      fun x y he => ?_⟩
    simp only [switch, decide_eq_decide]
    apply exists_congr
    intro e
    refine and_congr_right fun hi => ?_
    rw [he _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)),
      he _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi))]

theorem switch_carries (hn : 0 < n) (he : Expands g) (x : Records (Candidate n) J)
    (hs : (marked x).card * 131072 ≤ n) : Carries x (switch g (signal g x)) := by
  let mask := x ∘ Sum.inl
  let y := switch g (signal g x)
  have cov (i : Candidate n) : (∃ k, assign g mask i k = true) ↔ i ∈ marked x :=
    (assign_iff hn he hs i).trans mem_marked.symm
  choose k hk using fun i : marked x => (cov i).mpr i.property
  have hit (i : Fin n) : i ∈ marked y ↔ ∃ e : Link n, g e.1 e.2 = i ∧ assign g mask e.1 e.2 = true := by
    simp [y, switch, signal, mask]
  let f (i : marked x) : marked y :=
    ⟨g i (k i), (hit _).mpr ⟨(i, k i), rfl, hk i⟩⟩
  have hi : Function.Injective f := fun i j h =>
    Subtype.ext (assign_injective (hk i) (hk j) (congrArg Subtype.val h))
  have hg : Function.Surjective f := by
    intro j
    obtain ⟨⟨i, r⟩, hj, hr⟩ := (hit _).mp j.property
    let a : marked x := ⟨i, (cov _).mp ⟨r, hr⟩⟩
    exact ⟨a, Subtype.ext (by change g i (k a) = j; rw [assign_unique (hk a) hr]; exact hj)⟩
  refine ⟨Equiv.ofBijective f ⟨hi, hg⟩, fun i j => ?_⟩
  change y (.inr (g i (k i), j)) = _
  apply Bool.eq_iff_iff.mpr
  simp only [y, switch, signal, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, decide_eq_true_eq,
    mem_into]
  constructor
  · rintro ⟨e, hh, hr, hv⟩
    rwa [assign_injective hr (hk i) hh] at hv
  · exact fun hv => ⟨(i, k i), rfl, hk i, hv⟩

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# Oriented pairs of records

Both ends of a transport carry its identifier and its data. Flipping
the orientation bit must send each marked record to another marked
record. Unambiguous identifiers make the matching unique.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {I J K : Type}

def payload (x : Records I J) (i : I) (j : J) : Bool := x (.inr (i, j))

def flip [DecidableEq J] (o : J) (x : J → Bool) (j : J) : Bool :=
  if j = o then !(x j) else x j

theorem flip_involutive [DecidableEq J] (o : J) : Function.Involutive (flip o) := by
  intro x
  funext j
  by_cases h : j = o <;> simp [flip, h]

variable [Fintype I] [Fintype K]

def Unambiguous (x : Records I J) : Prop := Set.InjOn (payload x) (marked x)

def Closed [DecidableEq J] (o : J) (x : Records I J) : Prop :=
  ∀ i ∈ marked x, ∃ j ∈ marked x, payload x j = flip o (payload x i)

namespace Carries

variable {x : Records I J} {y : Records K J}

theorem symm (h : Carries x y) : Carries y x := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun i j => by simpa using (he (e.symm i) j).symm⟩

theorem unambiguous (h : Carries x y) (hx : Unambiguous x) : Unambiguous y := by
  obtain ⟨e, he⟩ := h.symm
  intro i hi j hj eq
  let a : marked y := ⟨i, hi⟩
  let b : marked y := ⟨j, hj⟩
  have hd : payload x (e a) = payload x (e b) :=
    (funext (he a)).trans (eq.trans (funext (he b)).symm)
  have heq : e a = e b := Subtype.ext (hx (e a).property (e b).property hd)
  exact congrArg Subtype.val (e.injective heq)

private theorem closed [DecidableEq J] {o : J} (h : Carries x y) (hx : Closed o x) : Closed o y := by
  obtain ⟨e, he⟩ := h
  intro i hi
  let a := e.symm ⟨i, hi⟩
  obtain ⟨j, hj, hj'⟩ := hx _ a.property
  have ha : payload y i = payload x a := by
    funext k
    simpa [a, payload] using he a k
  exact ⟨e ⟨j, hj⟩, (e ⟨j, hj⟩).property, (funext (he ⟨j, hj⟩)).trans (ha ▸ hj')⟩

theorem closed_iff [DecidableEq J] {o : J} (h : Carries x y) : Closed o y ↔ Closed o x :=
  ⟨h.symm.closed, h.closed⟩

end Carries
end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# Hiding the tags

For lists of distinct payloads, a proposed permutation has exactly one
valid assignment of positional tags. Summing over those tags therefore
works even over a field of positive characteristic.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install
open Tagged

variable {F : Type} [Field F] {a : Wire} {w : ℕ}

private theorem erase (z : Val (tree w (row w a))) :
    flatten w (payloads w z) = (flatten w z).map Prod.snd := flatten_mapRows _ _ _

/-- On a permutation of a distinct labelled list, erasure is invertible. -/
private theorem recover (x : Val (tree w a)) (hx : (flatten w x).Nodup) :
    ∃ f : Val a → Val (row w a), (∀ y, (f y).2 = y) ∧
      ∀ z, (flatten w z).Perm (flatten w (label w x)) → mapRows f w (payloads w z) = z := by
  classical
  let L := flatten w (label w x)
  have hd : (L.map Prod.snd).Nodup := by rw [← erase, label_payloads]; exact hx
  have hi := (List.nodup_map_iff_inj_on (label_nodup w x)).mp hd
  have exists_idx (y : Val a) : ∃ i, ∀ j, (j, y) ∈ L → i = j := by
    by_cases h : ∃ j, (j, y) ∈ L
    · obtain ⟨i, h⟩ := h
      exact ⟨i, fun j h' => congrArg Prod.fst (hi _ h _ h' rfl)⟩
    · exact ⟨Lookup.zero w, fun j hj => (h ⟨j, hj⟩).elim⟩
  choose idx hidx using exists_idx
  refine ⟨fun y => (idx y, y), fun _ => rfl, fun z hp => flatten_inj w ?_⟩
  rw [flatten_mapRows, erase, List.map_map]
  refine (List.map_congr_left ?_).trans (List.map_id _)
  intro r hr
  change (idx r.2, r.2) = r
  rw [hidx r.2 r.1 (hp.subset hr)]

private theorem untag (x y : Val (tree w a)) (hx : (flatten w x).Nodup) :
    (∑ z : Val (tree w (row w a)), tag F w a (x, z) () *
      if payloads w z = y then 1 else 0) = permuted F w x y := by
  classical
  obtain ⟨f, hi, hf⟩ := recover x hx
  let Z := mapRows f w y
  have hy : payloads w Z = y := by
    apply flatten_inj w
    simp [erase, Z, flatten_mapRows, List.map_map, Function.comp_def, hi]
  have hl : mapRows f w x = label w x := by
    simpa only [label_payloads] using hf (label w x) (.refl _)
  have hp : (flatten w Z).Perm (flatten w (label w x)) ↔ (flatten w y).Perm (flatten w x) := by
    rw [← hl, show Z = mapRows f w y from rfl, flatten_mapRows, flatten_mapRows]
    exact List.map_perm_map_iff (Function.LeftInverse.injective hi)
  rw [Finset.sum_eq_single Z]
  · simp only [hy, ite_true, mul_one, tag, permuted, hp]
  · intro z _ hz
    by_cases h : (flatten w z).Perm (flatten w (label w x))
    · have : payloads w z ≠ y := fun h' => hz ((hf z h).symm.trans (congrArg (mapRows f w) h'))
      simp [this]
    · simp [tag, permuted, h]
  · simp

theorem blind {w u m : ℕ} (ht : Radix.Tag F w u m) :
    ∃ (k : Val (tree w (word u)) → Val (tree w (word u)) → F) (v : ℕ),
      Net F (tree w (word u)) (tree w (word u)) k v ∧ v ≤ m + 10 * 2 ^ w * (u + w + 1) ∧
      ∀ x y, (flatten w x).Nodup → k x y = Tagged.permuted F w x y := by
  let a := word u
  have h := Net.curry (k := fun x z => tag F w a (x, z) ()) ht
  obtain ⟨v, hv, strip⟩ := mapRows_net (DNet.snd F (word w) a) w
  refine ⟨_, _, h.comp strip, ?_, untag⟩
  simp only [wd_tree, wd_word, wd, a] at hv ⊢
  ring_nf at hv ⊢
  omega

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# Checking opposite ends of transports

Compare the list of active records with the same list after reversing
orientation. Unmarked slots receive separate addresses. This keeps all
records distinct, so hiding positional tags introduces no multiplicities.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {F J : Type} [Field F] [DecidableEq J] {w u N : ℕ}

private abbrev Key (N : ℕ) (J : Type) := Fin N ⊕ (J → Bool)

private def key (o : J) (x : Records (Fin N) J) (b : Bool) (i : Fin N) : Key N J :=
  if i ∈ marked x then .inr (if b then flip o (payload x i) else payload x i) else .inl i

private theorem key_injective (o : J) (x : Records (Fin N) J) (hx : Unambiguous x) :
    Function.Injective (key o x true) := by
  intro i j he
  unfold key at he
  by_cases hi : i ∈ marked x <;> by_cases hj : j ∈ marked x
  · simp only [hi, hj, ite_true, Sum.inr.injEq] at he
    exact hx hi hj ((flip_involutive o).injective he)
  · simp [hi, hj] at he
  · simp [hi, hj] at he
  · simpa only [hi, hj, ite_false, Sum.inl.injEq] using he

private theorem key_perm (o : J) (x : Records (Fin N) J) (hx : Unambiguous x) :
    (List.ofFn (key o x false)).Perm (List.ofFn (key o x true)) ↔ Closed o x := by
  classical
  constructor
  · intro h i hi
    have := h.symm.subset (List.mem_ofFn.mpr ⟨i, rfl⟩)
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp this
    by_cases he : j ∈ marked x
    · exact ⟨j, he, by simpa [key, hi, he] using hj⟩
    · simp [key, hi, he] at hj
  · intro h
    have hsub : List.ofFn (key o x true) ⊆ List.ofFn (key o x false) := by
      intro r hr
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      by_cases hi : i ∈ marked x
      · obtain ⟨j, hj, he⟩ := h i hi
        exact List.mem_ofFn.mpr ⟨j, by simp [key, hi, hj, he]⟩
      · exact List.mem_ofFn.mpr ⟨i, by simp [key, hi]⟩
    have hn := List.nodup_ofFn.mpr (key_injective o x hx)
    exact ((hn.subperm hsub).perm_of_length_le (by simp)).symm

variable [Fintype J]

private abbrev Pos (J : Type) [Fintype J] (w u : ℕ) :=
  Unit ⊕ Fin w ⊕ J ⊕ Fin (u - (1 + w + Fintype.card J))

private def code (e : Fin (2 ^ w) ≃ (Fin w → Bool)) : Key (2 ^ w) J → Pos J w u → Bool
  | .inl i, .inr (.inl j) => e i j
  | .inr _, .inl _ => true
  | .inr d, .inr (.inr (.inl j)) => d j
  | _, _ => false

omit [DecidableEq J] in
private theorem code_injective (e : Fin (2 ^ w) ≃ (Fin w → Bool)) :
    Function.Injective (code (J := J) (u := u) e) := by
  rintro (i | x) (j | y) h
  · exact congrArg Sum.inl (e.injective (funext fun k => congrFun h (.inr (.inl k))))
  · exact (Bool.false_ne_true (congrFun h (.inl ()))).elim
  · exact (Bool.false_ne_true (congrFun h (.inl ())).symm).elim
  · exact congrArg Sum.inr (funext fun k => congrFun h (.inr (.inr (.inl k))))

private theorem code_depends (o : J) (e : Fin (2 ^ w) ≃ (Fin w → Bool))
    (b : Bool) (i : Fin (2 ^ w)) (j : Pos J w u) :
    ∃ S : Finset (Bus (Fin (2 ^ w)) J), S.card ≤ 2 ∧ ∀ x y, (∀ k ∈ S, x k = y k) →
      code e (key o x b i) j = code e (key o y b i) j := by
  let p : J := match j with
    | .inr (.inr (.inl t)) => t
    | _ => o
  refine ⟨{.inl i, .inr (i, p)}, by simp, fun x y h => ?_⟩
  have hi := h (.inl i) (by simp)
  have hj := h (.inr (i, p)) (by simp)
  simp only [key, mem_marked, hi]
  by_cases hm : y (.inl i) = true
  · simp only [hm, ite_true]
    rcases j with _ | _ | p' | _
    · rfl
    · rfl
    · change payload x i p' = payload y i p' at hj
      cases b <;> simp [code, flip, hj]
    · rfl
  · simp [hm]

theorem uncurry {a : Wire} {k : Val a → Val a → F} {v : ℕ}
    (h : Net F a a k v) : Net F (.pair a a) .unit (fun x _ => k x.1 x.2) (v + wd a) := by
  have both := (h.par (Tagged.cap a)).pre (.assoc a a a)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using
    (both.post (.swap _ _)).trace

open Classical in
/-- One verifier on words suffices for a group of oriented transports. -/
theorem check_turns {F J : Type} [Field F] [Fintype J] [DecidableEq J] {w u m : ℕ}
    (o : J) (hu : 1 + w + Fintype.card J ≤ u) (ht : Radix.Tag F w u m) :
    ∃ g : Records (Fin (2 ^ w)) J → F, Weight F g (m + 1000 * 2 ^ w * u) ∧
      ∀ x, Unambiguous x → g x = if Closed o x then 1 else 0 := by
  let e : Fin (2 ^ w) ≃ (Fin w → Bool) := Fintype.equivOfCardEq (by simp)
  let a := word u
  let t := tree w a
  let p : slots (word u) ≃ Pos J w u := Fintype.equivOfCardEq (by simp [Pos]; omega)
  let encode (z : Key (2 ^ w) J) := (bits a).symm (code e z ∘ p)
  have enc : Function.Injective encode := by
    intro x y hh
    apply code_injective (u := u) e
    funext j
    obtain ⟨i, rfl⟩ := p.surjective j
    exact congrFun ((bits a).symm.injective hh) i
  obtain ⟨L, hL⟩ := Layout.exists_tree a w
  let get (x : Records (Fin (2 ^ w)) J) (b : Bool) (j : slots t) :=
    code e (key o x b (L.positions.symm j).1) (p (L.positions.symm j).2)
  let prep (x : Records (Fin (2 ^ w)) J) : slots (.pair t t) → Bool :=
    Sum.elim (get x true) (get x false)
  have hp : Depends prep 2 := by
    rintro (j | j)
    · exact code_depends o e true _ _
    · exact code_depends o e false _ _
  let rows (x : Records (Fin (2 ^ w)) J) (b : Bool) := (bits t).symm (get x b)
  have hr (x) (b) : flatten w (rows x b) = (List.ofFn (key o x b)).map encode := by
    rw [← hL, List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp [Layout.read, rows, get, encode, Function.comp_def, t]
  obtain ⟨k, v, hk, hv, check⟩ := blind ht
  let test (x : slots (.pair t t) → Bool) :=
    k ((bits (.pair t t)).symm x).1 ((bits (.pair t t)).symm x).2
  have test_net : Weight F test (v + wd t) := by
    apply Weight.of_layout (a := .pair t t) (Equiv.refl _)
    refine ⟨_, le_rfl, ?_⟩
    simpa [test, Function.comp_def] using uncurry hk
  refine ⟨test ∘ prep, ((hp.bnet F).weight test_net).mono ?_, fun x hx => ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_slots,
      t, a, wd_word, wd_tree, localCost]
    have := Nat.mul_le_mul_left (2 ^ w) hu
    ring_nf at this hv ⊢
    omega
  · change k (rows x true) (rows x false) = _
    have hn : (flatten w (rows x true)).Nodup := by
      rw [hr]
      exact (List.nodup_ofFn.mpr (key_injective o x hx)).map enc
    simp only [check _ _ hn, Tagged.permuted, hr,
      List.map_perm_map_iff enc, key_perm o x hx]

end OAI.LinearAlgebra.MatrixExponent.Install
end
