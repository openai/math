import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Packets
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Machine
import OAI.LinearAlgebra.MatrixExponent.Transcript.RAM.Calls

section
/-! # Canonical allocation of processors with prescribed dyadic levels -/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open Finset

variable {G : Type} {P : G → ℕ} {V k : ℕ}

/-- The last number in each group denotes a vacant slot. -/
abbrev Plan (P : G → ℕ) (V k : ℕ) :=
  (g : G) → Slot (P g) V k → Fin (P g + 1)

variable (s : (g : G) → Fin (P g) → Fin (k + 1))

structure Assigned (y : Plan P V k) : Prop where
  order : ∀ g t, Monotone (fun i => y g ⟨t, i⟩)
  level : ∀ g a (p : Fin (P g)), y g a = p.castSucc → s g p = a.1
  occurs : ∀ g (p : Fin (P g)), ∃! a, y g a = p.castSucc

private def members (g : G) (t : Fin (k + 1)) := univ.filter (fun p => s g p = t)

private theorem capacity_bound (g : G) (t : Fin (k + 1)) (hs : ∑ p, 2 ^ (s g p).val ≤ 2 * V) :
    (members s g t).card ≤ seats (P g) V t.val := by
  apply le_min
  · simpa using (members s g t).card_le_univ
  · apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    calc
      _ = ∑ _ ∈ members s g t, 2 ^ t.val := by simp
      _ = ∑ p ∈ members s g t, 2 ^ (s g p).val :=
        sum_congr rfl (fun p hp => by rw [(mem_filter.mp hp).2])
      _ ≤ ∑ p, 2 ^ (s g p).val := sum_le_sum_of_subset (subset_univ _)
      _ ≤ 2 * V := hs

private theorem assigned_iff (y : Plan P V k) :
    Assigned s y ↔ ∀ g t, OrderedSeats (members s g t) (fun i => y g ⟨t, i⟩) := by
  constructor
  · intro h g t
    refine ⟨h.order g t, ?_, ?_⟩
    · intro p
      simp only [members, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact h.level g ⟨t, i⟩ p hi
      · intro ht
        obtain ⟨⟨r, i⟩, hi, _⟩ := h.occurs g p
        have hr : r = t := (h.level g ⟨r, i⟩ p hi).symm.trans ht
        subst r
        exact ⟨i, hi⟩
    · intro i j hij hi
      obtain ⟨p, hp⟩ := Fin.exists_castSucc_eq.mpr hi
      have e : (⟨t, i⟩ : Slot (P g) V k) = ⟨t, j⟩ :=
        (h.occurs g p).unique hp.symm (hij.symm.trans hp.symm)
      exact eq_of_heq (Sigma.mk.inj_iff.mp e).2
  · intro h
    have level (g) (a : Slot (P g) V k) (p : Fin (P g)) (ha : y g a = p.castSucc) :
        s g p = a.1 := (mem_filter.mp (((h g a.1).2.1 p).mp ⟨a.2, ha⟩)).2
    refine ⟨fun g t => (h g t).1, level, ?_⟩
    intro g p
    let t := s g p
    obtain ⟨i, hi⟩ := ((h g t).2.1 p).mpr (by simp [members, t])
    refine ⟨⟨t, i⟩, hi, ?_⟩
    rintro ⟨r, j⟩ hj
    have hr : r = t := (level g ⟨r, j⟩ p hj).symm
    subst r
    have he : j = i := (h g t).2.2 _ _ (hj.trans hi.symm) (hj.trans_ne (Fin.castSucc_ne_last p))
    rw [he]

/-- Sorting each group and level removes all allocation multiplicity. -/
theorem unique_plan (hs : ∀ g, ∑ p, 2 ^ (s g p).val ≤ 2 * V) :
    ∃! y : Plan P V k, Assigned s y := by
  have h (g : G) (t : Fin (k + 1)) := unique_seats _ (capacity_bound s g t (hs g))
  let y : Plan P V k := fun g a => (h g a.1).choose a.2
  refine ⟨y, (assigned_iff s y).mpr (fun g t => (h g t).choose_spec.1), ?_⟩
  intro z hz
  funext g ⟨t, i⟩
  exact congrFun ((h g t).choose_spec.2 _ ((assigned_iff s z).mp hz g t)) i

variable {s}

/-- Every processor contributes once, and vacant slots contribute one. -/
theorem Assigned.prod [Fintype G] {F : Type} [CommMonoid F] {y : Plan P V k}
    (hy : Assigned s y) (w : (g : G) → Slot (P g) V k → F) (f : (g : G) → Fin (P g) → F)
    (h₀ : ∀ g a, y g a = Fin.last (P g) → w g a = 1)
    (h₁ : ∀ g a (p : Fin (P g)), y g a = p.castSucc → w g a = f g p) :
    (∏ g, ∏ a, w g a) = ∏ g, ∏ p, f g p := by
  refine prod_congr rfl fun g _ => ?_
  have he (a : Slot (P g) V k) :
      w g a = ∏ p : Fin (P g), if y g a = p.castSucc then f g p else 1 := by
    by_cases ha : y g a = Fin.last (P g)
    · simp [h₀ g a ha, ha, Ne.symm (Fin.castSucc_ne_last _)]
    obtain ⟨p, hp⟩ := Fin.exists_castSucc_eq.mpr ha
    simp [h₁ g a p hp.symm, ← hp]
  simp_rw [he]
  rw [prod_comm]
  refine prod_congr rfl fun p _ => ?_
  obtain ⟨a, ha, hu⟩ := hy.occurs g p
  rw [prod_eq_single a]
  · exact ite_eq_left ha
  · intro b _ hb
    exact ite_eq_right (mt (hu b) hb)
  · simp

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

section
/-! # Matching active records in a padded pool -/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Match

/-- Each active key occurs once in each direction with the same payload. -/
def good {I α β : Type} (r : I → Bool × Bool × α × β) : Prop :=
  (∀ i k, (r i).1 = true → (r k).1 = true → (r i).2.1 = (r k).2.1 →
    (r i).2.2.1 = (r k).2.2.1 → i = k) ∧
  ∀ i, (r i).1 = true → ∃ k, r k = (true, !(r i).2.1, (r i).2.2)

theorem good_extend {I J α β : Type} (e : I ↪ J) (r : I → Bool × Bool × α × β)
    (z : Bool × Bool × α × β) (hz : z.1 = false) :
    good (Function.extend e r (fun _ => z)) ↔ good r := by
  let s := Function.extend e r (fun _ => z)
  change good s ↔ good r
  have he (i) : s (e i) = r i := e.injective.extend_apply _ _ _
  have ha (k) (hk : (s k).1 = true) : k ∈ Set.range e := by
    by_contra hn
    simp [s, Function.extend_apply' _ _ _ hn, hz] at hk
  constructor
  · rintro ⟨hu, hp⟩
    constructor
    · intro i k hi hk hd hb
      apply e.injective
      have h := hu (e i) (e k)
      rw [he, he] at h
      exact h hi hk hd hb
    · intro i hi
      obtain ⟨k, hk⟩ := hp (e i) (by rw [he, hi])
      obtain ⟨l, rfl⟩ := ha k (congrArg Prod.fst hk)
      exact ⟨l, by simpa only [he] using hk⟩
  · rintro ⟨hu, hp⟩
    constructor
    · intro i k hi hk hd hb
      obtain ⟨a, rfl⟩ := ha i hi
      obtain ⟨b, rfl⟩ := ha k hk
      simp only [he] at hi hk hd hb
      exact congrArg e (hu a b hi hk hd hb)
    · intro i hi
      obtain ⟨a, rfl⟩ := ha i hi
      rw [he] at hi
      obtain ⟨b, hb⟩ := hp a hi
      exact ⟨e b, by rw [he, he, hb]⟩

open Messages

private abbrev Record (H w : ℕ) := Bool × Bool × Val (word H) × Val (word w)

private def packFromMatchPadding {H w : ℕ} (x : Record H w) : Val (row H w) :=
  assemble (x.1, x.2.1, x.2.2.1) x.2.2.2

private theorem pack_injective {H w : ℕ} : Function.Injective (packFromMatchPadding (H := H) (w := w)) := by
  rintro ⟨a, d, k, v⟩ ⟨a', d', k', v'⟩ h
  have hh := congrArg (header H w) h
  simp only [packFromMatchPadding, header_assemble, Prod.mk.injEq] at hh
  obtain ⟨rfl, rfl, rfl⟩ := hh
  have hv : v = v' := assemble_injective (a, d, k) h
  rw [hv]

private theorem pack_reverse {H w : ℕ} (x : Record H w) (hx : x.1 = true) :
    reverse H w (packFromMatchPadding x) = packFromMatchPadding (true, !x.2.1, x.2.2) := by
  simp [packFromMatchPadding, reverse_assemble, opposite, hx]

/-- Unique inactive keys allow the full header check to ignore inactive data. -/
theorem good_valid {j H w : ℕ} (r : Fin (2 ^ j) → Bool × Bool × Val (word H) × Val (word w))
    (hu : ∀ i k, (r i).1 = false → (r k).1 = false → (r i).2.2.1 = (r k).2.2.1 → i = k)
    {m : Val (tree j (Messages.row H w))}
    (hm : flatten j m = List.ofFn (fun i =>
      Messages.assemble ((r i).1, (r i).2.1, (r i).2.2.1) (r i).2.2.2)) :
    Messages.valid j H w m ↔ good r := by
  change flatten j m = List.ofFn (fun i => packFromMatchPadding (r i)) at hm
  rw [Messages.valid_iff, hm, List.map_ofFn, List.nodup_ofFn]
  have hh (i) : (header H w ∘ fun i => packFromMatchPadding (r i)) i =
      ((r i).1, (r i).2.1, (r i).2.2.1) := header_assemble _ _
  constructor
  · rintro ⟨hn, hp⟩
    constructor
    · intro i k hi hk hd hb
      apply hn
      rw [hh, hh, hi, hk, hd, hb]
    · intro i hi
      have hp' := hp _ (List.mem_ofFn.mpr ⟨i, rfl⟩) hi
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hp'
      rw [pack_reverse _ hi] at hk
      exact ⟨k, pack_injective hk⟩
  · rintro ⟨hn, hp⟩
    constructor
    · intro i k h
      simp only [hh, Prod.mk.injEq] at h
      cases hi : (r i).1
      · exact hu i k hi (h.1.symm.trans hi) h.2.2
      · exact hn i k hi (h.1.symm.trans hi) h.2.1 h.2.2
    · intro x hx ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      obtain ⟨k, hk⟩ := hp i ha
      exact List.mem_ofFn.mpr ⟨k, by rw [pack_reverse _ ha, hk]⟩

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Match
end

/-!
# Matching messages from arbitrary finite pools

Inactive records retain arbitrary contents. The extended key carries the
slot number when inactive and zero when active. Each new bit therefore
reads at most one old bit. Only the extended headers need sorting.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Match

open Coloring Install Messages
open scoped Classical

abbrev format (A D : Format) := Format.pair .bit (.pair .bit (.pair A D))

private def pos (A : Format) (n : ℕ) (h : A.width = n) : slots (word n) ≃ A.pins :=
  Fintype.equivOfCardEq (by rw [MatrixExponent.card_slots, wd_word, ← h])

private def packFromMatch (A : Format) {n : ℕ} (h : A.width = n) (x : A.obj) : Val (word n) :=
  (bits (word n)).symm (A.code x ∘ pos A n h)

private theorem pack_inj (A : Format) {n : ℕ} (h : A.width = n) :
    Function.Injective (packFromMatch A h) := by
  intro x y he
  apply A.code.injective
  funext i
  obtain ⟨p, rfl⟩ := (pos A n h).surjective i
  exact congrFun ((bits (word n)).symm.injective he) p

private theorem pack_bit (A : Format) {n : ℕ} (h : A.width = n) (x : A.obj)
    (p : slots (word n)) : bits (word n) (packFromMatch A h x) p = A.code x (pos A n h p) :=
  congrFun ((bits (word n)).apply_symm_apply _) p

private theorem key_width (A : Format) (j : ℕ) : (A.pair (.addr j)).width = A.width + j := by
  simp

private theorem body_width (D : Format) {n : ℕ} (hn : D.width ≤ n) :
    (D.pair (.addr (n - D.width))).width = n := by
  simp only [Format.width_pair, Format.width_addr]
  omega

private def padded (A D : Format) {j n : ℕ} (hn : D.width ≤ n) (i : B j) (x : (format A D).obj) :
    Bool × Bool × Val (word (A.width + j)) × Val (word n) :=
  (x.1, x.2.1, packFromMatch (A.pair (.addr j)) (key_width A j) (x.2.2.1, if x.1 then 0 else i),
    packFromMatch (D.pair (.addr (n - D.width))) (body_width D hn) (x.2.2.2, 0))

private def packet (A D : Format) {j n : ℕ} (hn : D.width ≤ n) (i : B j) (x : (format A D).obj) :
    Val (row (A.width + j) n) :=
  let y := padded A D hn i x
  assemble (y.1, y.2.1, y.2.2.1) y.2.2.2

private theorem append_wire (H w : ℕ) :
    Rewire (.pair (word w) (word H)) (word (H + w)) (fun x => appendWord H w x.1 x.2) := by
  induction w with
  | zero => exact (Rewire.swap _ _).comp (.unit _)
  | succ w ih => exact (Rewire.assoc _ _ _).comp ((Rewire.id .bit).par ih)

private theorem packet_bit (A D : Format) {j n : ℕ} (hn : D.width ≤ n) (i : B j)
    (q : slots (row (A.width + j) n)) :
    ∃ p : (format A D).pins, ∀ x y, (format A D).code x p = (format A D).code y p →
      bits (row (A.width + j) n) (packet A D hn i x) q = bits (row (A.width + j) n) (packet A D hn i y) q := by
  rcases q with q|q|q
  · exact ⟨.inl q, fun _ _ h => h⟩
  · exact ⟨.inr (.inl q), fun _ _ h => h⟩
  obtain ⟨e, he⟩ := (append_wire (A.width + j) n).reindex_exists
  have hb (x : (format A D).obj) :
      bits (row (A.width + j) n) (packet A D hn i x) (.inr (.inr q)) =
        bits (.pair (word n) (word (A.width + j)))
          ((padded A D hn i x).2.2.2, (padded A D hn i x).2.2.1) (e q) := by
    let t := ((padded A D hn i x).2.2.2, (padded A D hn i x).2.2.1)
    change bits (word (A.width + j + n)) (appendWord _ _ t.1 t.2) q = _
    rw [show appendWord _ _ t.1 t.2 = reindex e t from congrFun he t, bits_reindex]
  simp only [hb]
  cases e q with
  | inl k =>
    let C := D.pair (.addr (n - D.width))
    change ∃ p, ∀ x y : (format A D).obj, (format A D).code x p = (format A D).code y p →
      bits (word n) (packFromMatch C (body_width D hn) (x.2.2.2, 0)) k =
        bits (word n) (packFromMatch C (body_width D hn) (y.2.2.2, 0)) k
    simp only [pack_bit]
    cases pos C _ (body_width D hn) k with
    | inl u => exact ⟨.inr (.inr (.inr u)), fun _ _ h => h⟩
    | inr _ => exact ⟨.inl (), fun _ _ _ => rfl⟩
  | inr k =>
    let C := A.pair (.addr j)
    change ∃ p, ∀ x y : (format A D).obj, (format A D).code x p = (format A D).code y p →
      bits (word (A.width + j)) (packFromMatch C (key_width A j) (x.2.2.1, if x.1 then 0 else i)) k =
        bits (word (A.width + j)) (packFromMatch C (key_width A j) (y.2.2.1, if y.1 then 0 else i)) k
    simp only [pack_bit]
    cases pos C _ (key_width A j) k with
    | inl u => exact ⟨.inr (.inr (.inl u)), fun _ _ h => h⟩
    | inr u =>
      refine ⟨.inl (), fun x y h => ?_⟩
      change x.1 = y.1 at h
      rw [h]
      rfl

private theorem padded_inactive (A D : Format) {j n : ℕ} (hn : D.width ≤ n)
    (r : B j → (format A D).obj) (i k : B j)
    (hi : (r i).1 = false) (hk : (r k).1 = false)
    (he : (padded A D hn i (r i)).2.2.1 = (padded A D hn k (r k)).2.2.1) : i = k := by
  have h := congrArg Prod.snd (pack_inj _ (key_width A j) he)
  simpa [hi, hk] using h

private theorem good_padded (A D : Format) {j n : ℕ} (hn : D.width ≤ n)
    (r : B j → (format A D).obj) :
    good (fun i => padded A D hn i (r i)) ↔ good r := by
  have key (i k : B j) (hi : (r i).1 = true) (hk : (r k).1 = true) :
      (padded A D hn i (r i)).2.2.1 = (padded A D hn k (r k)).2.2.1 ↔
        (r i).2.2.1 = (r k).2.2.1 := by
    simp [padded, hi, hk, (pack_inj _ (key_width A j)).eq_iff]
  have peer (i k : B j) (hi : (r i).1 = true) :
      padded A D hn k (r k) = (true, !(r i).2.1, (padded A D hn i (r i)).2.2) ↔
        r k = (true, !(r i).2.1, (r i).2.2) := by
    obtain ⟨b, d, a, v⟩ := r k
    cases b <;> simp [padded, hi, (pack_inj _ (body_width D hn)).eq_iff,
      (pack_inj _ (key_width A j)).eq_iff, Prod.ext_iff]
  constructor
  · rintro ⟨hu, hp⟩
    refine ⟨fun i k hi hk hd hb => hu i k hi hk hd ((key i k hi hk).mpr hb), fun i hi => ?_⟩
    obtain ⟨k, hk⟩ := hp i hi
    exact ⟨k, (peer i k hi).mp hk⟩
  · rintro ⟨hu, hp⟩
    refine ⟨fun i k hi hk hd hb => hu i k hi hk hd ((key i k hi hk).mp hb), fun i hi => ?_⟩
    obtain ⟨k, hk⟩ := hp i hi
    exact ⟨k, (peer i k hi).mpr hk⟩

/-- Check the entire pool, allowing padding both the pool and the payload. -/
theorem weight {F I : Type} [Field F] [Fintype I] (A D : Format) {j n m : ℕ}
    (hc : Fintype.card I ≤ 2 ^ j) (hn : D.width ≤ n)
    (ht : Radix.Tag F j (A.width + j + n + 2) m) :
    Weight F (fun x : I × (format A D).pins → Bool =>
      if good (fun i => (format A D).code.symm (fun p => x (i, p))) then 1 else 0)
      (m + 20000 * 2 ^ j * (n + (1 + A.width + j) * (j + 1) ^ 2)) := by
  let e : I ↪ B j := (Function.Embedding.nonempty_of_card_le (by simpa using hc)).some
  let z : (format A D).obj := (false, false, A.code.symm (fun _ => false), D.code.symm (fun _ => false))
  let X := I × (format A D).pins
  let read (x : X → Bool) (i : I) := (format A D).code.symm (fun p => x (i, p))
  let r (x : X → Bool) := Function.extend e (read x) (fun _ => z)
  let a := row (A.width + j) n
  let t := tree j a
  obtain ⟨L, hL⟩ := Layout.exists_tree a j
  let prep (x : X → Bool) (q : slots t) :=
    let p := L.positions.symm q
    bits a (packet A D hn p.1 (r x p.1)) p.2
  have hp : Depends prep 1 := by
    intro q
    let i := (L.positions.symm q).1
    let k := (L.positions.symm q).2
    change ∃ s : Finset X, s.card ≤ 1 ∧ ∀ x y, (∀ p ∈ s, x p = y p) →
      bits a (packet A D hn i (r x i)) k = bits a (packet A D hn i (r y i)) k
    by_cases hi : i ∈ Set.range e
    · obtain ⟨l, hl⟩ := hi
      obtain ⟨p, hp⟩ := packet_bit A D hn i k
      refine ⟨{(l, p)}, by simp, fun x y h => hp _ _ ?_⟩
      simp only [r, ← hl, e.injective.extend_apply, read, Equiv.apply_symm_apply]
      exact h _ (by simp)
    · exact ⟨∅, by simp, fun x y _ => by simp only [r, Function.extend_apply' _ _ _ hi]⟩
  let test (y : slots t → Bool) : F :=
    if valid j (A.width + j) n ((bits t).symm y) then 1 else 0
  have hw : Weight F test (m + 10000 * 2 ^ j * (n + (1 + (A.width + j)) * (j + 1) ^ 2)) := by
    apply Weight.of_layout (a := t) (Equiv.refl _)
    simpa only [test, Equiv.coe_refl, Function.comp_id, Equiv.symm_apply_apply] using
      Messages.net (H := A.width + j) (w := n) ht
  have hs (x : X → Bool) : valid j (A.width + j) n ((bits t).symm (prep x)) ↔ good (read x) := by
    have hm : flatten j ((bits t).symm (prep x)) =
        List.ofFn (fun i => packet A D hn i (r x i)) := by
      rw [← hL]
      apply congrArg List.ofFn
      funext i
      simp [Layout.read, prep, t]
    exact (good_valid (fun i => padded A D hn i (r x i)) (padded_inactive A D hn (r x)) hm).trans
      ((good_padded A D hn (r x)).trans (good_extend e (read x) z rfl))
  have net := (hp.bnet F).weight hw
  simp only [Function.comp_def, test, hs] at net
  apply net.mono
  have size : Fintype.card X ≤ 2 ^ j * (2 + A.width + n) := by
    rw [show Fintype.card X = Fintype.card I * (format A D).width from Fintype.card_prod _ _]
    apply Nat.mul_le_mul hc
    simp only [format, Format.width_pair]
    rw [Format.width_bit]
    omega
  simp only [MatrixExponent.card_slots, t, a, row, wd_tree, localCost]
  rw [wd_word]
  ring_nf at size ⊢
  omega

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Match
end

section
/-!
# Matching across payload formats

A per-class check enforces equality of payloads within each class. A
single check of all headers prevents reuse of a key across classes.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Channels

open Coloring

variable {G : Type}

abbrev Rows (A : Format) (D : G → Format) (E : G → Type) :=
  (g : G) → E g → (Match.format A (D g)).obj

variable {A : Format} {D : G → Format} {E E' : G → Type}

def packet (r : Rows A D E) (i : Sigma E) : Bool × Bool × A.obj × (Σ g, (D g).obj) :=
  let x := r i.1 i.2
  (x.1, x.2.1, x.2.2.1, ⟨i.1, x.2.2.2⟩)

def header (r : Rows A D E) (i : Sigma E) : (Match.format A (.addr 0)).obj :=
  let x := r i.1 i.2
  (x.1, x.2.1, x.2.2.1, 0)

def good (r : Rows A D E) : Prop := Match.good (packet r)

private theorem peer_iff (r : Rows A D E) (g : G) (i : E g) :
    (∃ k, packet r k = (true, !(r g i).2.1, (packet r ⟨g, i⟩).2.2)) ↔
      ∃ k, r g k = (true, !(r g i).2.1, (r g i).2.2) := by
  constructor
  · rintro ⟨⟨h, k⟩, hk⟩
    have he : h = g := congrArg (fun x => x.2.2.2.1) hk
    subst h
    have hb := congrArg (fun x => x.2.2.2) hk
    have hv : (r g k).2.2.2 = (r g i).2.2.2 := eq_of_heq (Sigma.mk.inj hb).2
    have hh := congrArg Prod.fst hk
    have hd := congrArg (fun x => x.2.1) hk
    have ha := congrArg (fun x => x.2.2.1) hk
    exact ⟨k, Prod.ext hh (Prod.ext hd (Prod.ext ha hv))⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨g, k⟩, by simp only [packet, hk]⟩

theorem good_iff (r : Rows A D E) :
    good r ↔ (∀ g, Match.good (r g)) ∧ Match.good (header r) := by
  constructor
  · rintro ⟨hu, hp⟩
    have peers (g : G) (i : E g) (hi : (r g i).1 = true) :
        ∃ k, r g k = (true, !(r g i).2.1, (r g i).2.2) :=
      (peer_iff r g i).mp (hp ⟨g, i⟩ hi)
    refine ⟨fun g => ⟨?_, peers g⟩, hu, ?_⟩
    · intro i k hi hk hd hb
      exact eq_of_heq (Sigma.mk.inj (hu ⟨g, i⟩ ⟨g, k⟩ hi hk hd hb)).2
    · rintro ⟨g, i⟩ hi
      obtain ⟨k, hk⟩ := peers g i hi
      exact ⟨⟨g, k⟩, by simp only [header, hk]⟩
  · rintro ⟨hc, hu, _⟩
    refine ⟨hu, ?_⟩
    rintro ⟨g, i⟩ hi
    exact (peer_iff r g i).mpr ((hc g).2 i hi)

/-- One can add or remove any number of inactive records in each class. -/
theorem good_congr (r : Rows A D E) (s : Rows A D E') (e : (g : G) → E g ↪ E' g)
    (he : ∀ g i, s g (e g i) = r g i)
    (ha : ∀ g k, (s g k).1 = true → k ∈ Set.range (e g)) : good s ↔ good r := by
  let f : Sigma E → Sigma E' := fun i => ⟨i.1, e i.1 i.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨g, i⟩ ⟨h, k⟩ hf
    have hg : g = h := congrArg Sigma.fst hf
    subst h
    have : i = k := (e g).injective (eq_of_heq (Sigma.mk.inj hf).2)
    subst k
    rfl
  have eq (i) : packet s (f i) = packet r i := by simp only [packet, f, he]
  have cover (k) (hk : (packet s k).1 = true) : k ∈ Set.range f := by
    rcases k with ⟨g, k⟩
    obtain ⟨i, rfl⟩ := ha g k hk
    exact ⟨⟨g, i⟩, rfl⟩
  constructor
  · rintro ⟨hu, hp⟩
    constructor
    · intro i k hi hk hd hb
      apply hinj
      have h := hu (f i) (f k)
      rw [eq, eq] at h
      exact h hi hk hd hb
    · intro i hi
      obtain ⟨k, hk⟩ := hp (f i) (by rw [eq, hi])
      obtain ⟨l, rfl⟩ := cover k (congrArg Prod.fst hk)
      exact ⟨l, by simpa only [eq] using hk⟩
  · rintro ⟨hu, hp⟩
    constructor
    · intro i k hi hk hd hb
      obtain ⟨a, rfl⟩ := cover i hi
      obtain ⟨b, rfl⟩ := cover k hk
      simp only [eq] at hi hk hd hb
      exact congrArg f (hu a b hi hk hd hb)
    · intro i hi
      obtain ⟨a, rfl⟩ := cover i hi
      rw [eq] at hi
      obtain ⟨b, hb⟩ := hp a hi
      exact ⟨f b, by rw [eq, eq, hb]⟩

abbrev Pins (A : Format) (D : G → Format) (E : G → Type) :=
  Σ g, E g × (Match.format A (D g)).pins

def decode (A : Format) (D : G → Format) (E : G → Type) (x : Pins A D E → Bool) :
    Rows A D E :=
  fun g i => (Match.format A (D g)).code.symm (fun p => x ⟨g, i, p⟩)

def cost (A : Format) (D : G → Format) (E : G → Type) [Fintype G] [∀ g, Fintype (E g)]
    (h C W : ℕ) :=
  1000000 * (W + 1) * ((Fintype.card G + Fintype.card (Sigma E) + 1) * (1 + h ^ C + A.width) +
    ∑ g, (1 + Fintype.card (E g)) * (D g).width)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Channels
end

/-!
# Processor records, advice and private inputs

Group processors by the length of their fixed private input. Each bit
of that input is advice or one of the exposed bits. A record consists
of a length class, guesses and incoming and outgoing message tapes.
The first field of a message marks an occupied table entry.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Coloring
open scoped Classical

abbrev Level (k : ℕ) := Fin (k + 1)

structure Spec (X : Type) (k H : ℕ) where
  P : Level k → ℕ
  named : ∀ g, P g < 2 ^ H
  supply : Level k → Format
  privateBits : (g : Level k) → Fin (P g) → (supply g).pins → X ⊕ Bool
  guesses : Level k → Level k → ℕ
  messages : ℕ
  key : Format
  body : Level k → Format

namespace Spec
variable {X : Type} {k H : ℕ} (S : Spec X k H)
abbrev Group := Level k
abbrev size := ∑ g, S.P g
abbrev Who := Σ g, Fin (S.P g)
abbrev Site (V : ℕ) := Σ g, Slot (S.P g) V k
abbrev Msg (l : Level k) := Match.format S.key (S.body l)
abbrev Port (j l : Level k) := Fin (seats S.messages (2 ^ j.val) l.val)
abbrev Fields (g j : Level k) :=
  Fin (S.guesses g j) ⊕ (Σ l : Level k, S.Port j l × (S.Msg l).pins)
abbrev Input (g j : Level k) := (Private.format (S.supply g) H).pins ⊕ S.Fields g j
abbrev Record (g : Level k) := Σ j : Level k, S.Fields g j → Bool
abbrev History := (g : Level k) → Fin (S.P g) → S.Record g

def data (x : X → Bool) (g : Level k) (p : Fin (S.P g)) : (S.supply g).obj :=
  (S.supply g).code.symm (Sum.elim x id ∘ S.privateBits g p)

def identifier (g : Level k) (p : Fin (S.P g + 1)) : B H := p.castLE (S.named g)

def input (x : X → Bool) (g j : Level k) (p : Fin (S.P g))
    (f : S.Fields g j → Bool) : S.Input g j → Bool :=
  Sum.elim ((Private.format _ _).code (true, S.identifier g p.castSucc, S.data x g p)) f

def vacant (g j : Level k) : S.Input g j → Bool :=
  Sum.elim ((Private.format _ _).code
    (false, S.identifier g (Fin.last (S.P g)), (S.supply g).code.symm (fun _ => false))) (fun _ => false)

def badge {g j : Level k} (a : S.Input g j → Bool) : (Private.format (S.supply g) H).obj :=
  (Private.format _ _).code.symm (a ∘ Sum.inl)

def on (g j : Level k) : S.Input g j := .inl (.inl ())

def mask (g j : Level k) : S.Input g j → Bool
  | .inl (.inr (.inl _)) => false
  | _ => true

def message {g j : Level k} (f : S.Fields g j → Bool) (l : Level k) (v : S.Port j l) : (S.Msg l).obj :=
  (S.Msg l).code.symm (fun t => f (.inr ⟨l, v, t⟩))

abbrev Real (a : S.History) (l : Level k) := Σ i : S.Who, S.Port (a i.1 i.2).1 l

def declared (a : S.History) : Channels.Rows S.key S.body (S.Real a) :=
  fun l i => S.message (a i.1.1 i.1.2).2 l i.2

abbrev Tape (V : ℕ) := (g : Level k) → (i : Slot (S.P g) V k) → S.Input g i.1 → Bool
abbrev Reserved (V : ℕ) (l : Level k) := Σ i : S.Site V, S.Port i.2.1 l

def issued {V : ℕ} (a : S.Tape V) : Channels.Rows S.key S.body (S.Reserved V) :=
  fun l i => S.message (a i.1.1 i.1.2 ∘ Sum.inr) l i.2

structure Places {V : ℕ} (x : X → Bool) (a : S.History) (b : S.Tape V) : Prop where
  spec : ∃ y : Plan S.P V k, Assigned (fun g p => (a g p).1) y ∧
    (∀ g i, y g i = Fin.last (S.P g) → b g i = S.vacant g i.1) ∧
    (∀ g i p, y g i = p.castSucc → ∃ f, a g p = ⟨i.1, f⟩ ∧ b g i = S.input x g i.1 p f)

end Spec
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # Charged bit strings on fixed seats -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings

open RAM Coloring

section
variable {n : ℕ}

/-- The unused suffix of each bucket carries the sentinel ordinal. -/
structure Placement (M T k : ℕ) (x : Fin n → List Bool) where
  toSlot : Fin n ↪ Slot M T k
  ordinal : Slot M T k → Fin (n + 1)
  ordered : ∀ l : Level k, OrderedSeats (bucket (fun j => callCharge (x j)) l.val)
    (fun s => ordinal ⟨l, s⟩)
  atSlot : ∀ j, ordinal (toSlot j) = j.castSucc
  fromSlot : ∀ s j, ordinal s = j.castSucc → toSlot j = s
  level : ∀ j, (toSlot j).1.val = Nat.clog 2 (callCharge (x j))

end

variable {I : Type} {A : Format} {n T : I → ℕ} {M k : ℕ}

abbrev Rows (A : Format) (n : I → ℕ) := (i : I) → Fin (n i) → Bool × A.obj × List Bool

abbrev Seats (M : ℕ) (T : I → ℕ) (l : Level k) := Σ i, Fin (seats M (T i) l.val)

variable (row : Rows A n)

abbrev Layout (M k : ℕ) (T : I → ℕ) :=
  (i : I) → Placement M (T i) k (fun j => (row i j).2.2)

variable (p : Layout row M k T)

def code : Channels.Rows A (fun l : Level k => token l.val) (Seats M T) :=
  fun l v => Fin.lastCases (false, false, A.code.symm (fun _ => false), emptyToken l.val)
    (fun j => (true, (row v.1 j).1, (row v.1 j).2.1, encodeToken l.val (row v.1 j).2.2))
    ((p v.1).ordinal ⟨l, v.2⟩)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end

/-! # Local ordinal bits for recovering message order across length classes -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings

open RAM Coloring
open scoped Classical

variable {I : Type} {A : Format} {n T : I → ℕ} {M k : ℕ}

abbrev Position (M : ℕ) := Format.addr (Nat.clog 2 (1 + M))

/-- Local data, separate from the key and payload compared by the channel. -/
abbrev Order (M k : ℕ) (T : I → ℕ) := (i : I) → Slot M (T i) k → (Position M).obj

def order (row : Rows A n) (q : Layout row M k T) (hm : ∀ i, n i ≤ M) : Order M k T :=
  fun i s => Fin.castLE (le_trans (by have := hm i; omega : n i + 1 ≤ 1 + M)
    (Nat.le_pow_clog (by decide) _)) ((q i).ordinal s)

def unpack (b : ℕ) (x : (token b).obj) : List Bool := (List.ofFn x.2.2).take x.2.1.val

/-- Look up an ordinal without access to the original population sizes or strings. -/
def restore (c : Channels.Rows A (fun l : Level k => token l.val) (Seats M T))
    (o : Order M k T) (i : I) (j : ℕ) : Option (Bool × A.obj × List Bool) :=
  if h : ∃! s : Slot M (T i) k, (c s.1 ⟨i, s.2⟩).1 = true ∧ (o i s).val = j then
    let s := h.choose
    let x := c s.1 ⟨i, s.2⟩
    some (x.2.1, x.2.2.1, unpack s.1.val x.2.2.2)
  else none

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end

/-!
# Logical bit-RAM transcript

At a given input width and time limit all processors share a
verifier. Branches and memory accesses may depend on the data.
The verified record includes a dyadic class and the bits presented
to the verifier. Emissions reside in its final memory, and the
dictionary is applied only after execution.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Coloring Finset
open scoped Classical
variable {X : Type} {k H U : ℕ}

structure System (S : Spec X k H) (U : ℕ) where
  width : ℕ
  verify : (g j : Level k) → Controller (S.Input g j) (Output (2 ^ j.val) U) width

namespace System
variable {S : Spec X k H} (D : System S U)

abbrev output (g j : Level k) := (D.verify g j).value j.val

def record (x : X → Bool) (g : Level k) (p : Fin (S.P g)) (a : S.Record g) :=
  D.output g a.1 (S.input x g a.1 p a.2)

def accepts (x : X → Bool) (a : S.History) : Prop :=
  Channels.good (S.declared a) ∧ ∀ g p, D.record x g p (a g p) (.inl ()) = true

/-- Charge bounds on the logical protocol. A dyadic record of level
`j` fits in `2^j` units, at most twice a charge in that class. -/
structure Bounded [Fintype X] (V h c B : ℕ) : Prop where
  processors : 0 < S.size
  height : k + 1 ≤ B
  longest : 2 ^ k ≤ 2 * V
  static : ∑ g, S.P g * (S.supply g).width ≤ 2 * V
  exterior : Fintype.card X ≤ V
  level : ∀ g, (S.supply g).width ≤ 2 ^ g.val
  key : S.key.width ≤ h ^ 2
  payload : ∀ l, (S.body l).width ≤ 4 * 2 ^ l.val
  count : S.messages ≤ h ^ c
  names : H ≤ h ^ 2
  dictionary : U ≤ h
  guesses : ∀ g j, S.guesses g j ≤ B * 2 ^ j.val
  addresses : D.width ≤ B
  control : ∀ g j, (D.verify g j).size ≤ B
  charge : ∀ x a, D.accepts x a → ∑ g, ∑ p, 2 ^ (a g p).1.val ≤ 2 * V

variable {K : Type} [Field K] (W : List Bool → K)

def value (x : X → Bool) (g : Level k) (p : Fin (S.P g)) (a : S.Record g) : K :=
  localValue W (D.output g a.1) (S.input x g a.1 p a.2)

def tensor (x : X → Bool) : K :=
  ∑ a : S.History, if D.accepts x a then ∏ g, ∏ p, D.value W x g p (a g p) else 0

end System
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # A local record with variable-length binary message tapes -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec

variable {X : Type} {k H : ℕ} (S : Spec X k H)

abbrev withStrings : Spec X k H := { S with body := fun l => RAM.token l.val }

variable {n : S.Who → ℕ} (j : S.Who → Level k) (row : Strings.Rows S.key n)
    (p : Strings.Layout row S.messages k (fun i => 2 ^ (j i).val))
    (f : (i : S.Who) → Fin (S.guesses i.1 (j i)) → Bool)

def literal : S.withStrings.History :=
  fun g v =>
    let i : S.Who := ⟨g, v⟩
    ⟨j i, Sum.elim (f i) (fun a =>
      (S.withStrings.Msg a.1).code (Strings.code row p a.1 ⟨i, a.2.1⟩) a.2.2)⟩

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
end
