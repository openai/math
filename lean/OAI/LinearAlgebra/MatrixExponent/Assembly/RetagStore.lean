import OAI.LinearAlgebra.MatrixExponent.Assembly.ChannelPlan
import OAI.LinearAlgebra.MatrixExponent.Control.Ranks
import OAI.LinearAlgebra.MatrixExponent.Assembly.Hold
import OAI.LinearAlgebra.MatrixExponent.Coloring.Add
import Mathlib.Algebra.Group.Fin.Basic
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Keys
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal

/-! # Pinning the unused suffix of each payload slot -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Payload

open Coloring Transcript
open scoped Classical

variable {m V k : ℕ} (p : Payload m V k)

abbrev Lengths (m V k : ℕ) := Fmt.pi (fun _ : Slot (2 ^ m) V k => Format.addr (k + 1))

def used (s : Slot (2 ^ m) V k) := (p.seat.read s).elim 0 p.length

def lengths : (Lengths m V k).obj := fun s => ⟨p.used s, by
  unfold used
  cases p.seat.read s with
  | none => exact Nat.two_pow_pos _
  | some i =>
    change p.length i < 2 ^ (k + 1)
    rw [pow_succ]
    have := Nat.two_pow_pos k
    have := p.longest i
    omega⟩

def mask (x : (Lengths m V k).obj) (i : Fmt.Port m V k) := decide ((x i.1).val ≤ i.2.val)

theorem occupied (i : Fmt.Port m V k) : i ∈ Set.range p.wire ↔ i.2.val < p.used i.1 := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    change b.val < p.used (p.seat.write a)
    rw [used, (p.seat.valid _ _).mpr rfl]
    exact b.isLt
  · rcases i with ⟨i, b⟩
    intro hi
    change b.val < (p.seat.read i).elim 0 p.length at hi
    cases h : p.seat.read i with
    | none => simp [h] at hi
    | some a =>
      have ha := (p.seat.valid _ _).mp h
      subst i
      rw [h] at hi
      exact ⟨⟨a, b.val, hi⟩, rfl⟩

theorem mask_eq (i : Fmt.Port m V k) : mask p.lengths i = decide (i ∉ Set.range p.wire) := by
  apply Bool.eq_iff_iff.mpr
  simp only [mask, lengths, decide_eq_true_eq, occupied, not_lt]
  exact decide_eq_true_iff

variable {F : Type} [Field F] {u : ℕ} {L : Set (Table F)}

private theorem threshold (j w : ℕ) :
    Circuit F (.addr w) (Fmt.raw (B j)) (fun x i => decide (x.val ≤ i.val)) (2000 * 2 ^ j * (w + 1)) := by
  have h := Install.BNet.share j _ fun i => Control.threshold_one F w i.val
  apply (h.rename (.refl _) (Equiv.prodUnique _ Unit)).mono
  rw [MatrixExponent.card_slots, wd_word]
  ring_nf
  omega

theorem mask_net (hu : 3 ≤ u) : Map F u L (Lengths m V k) (Fmt.payload m V k) mask
    (8000 * (k + 2) * (Fmt.payload m V k).width) := by
  let A := fun s : Slot (2 ^ m) V k => Fmt.raw (B s.1.val)
  have h (s : Slot (2 ^ m) V k) : Map F u L (.addr (k + 1)) (A s)
      (fun x i => decide (x.val ≤ i.val)) (8000 * (k + 2) * capacity s) := by
    refine (Map.circuit hu (threshold s.1.val (k + 1))).mono ?_
    unfold capacity
    exact le_of_eq (by ring)
  have t := Map.family h
  have eq : (∑ s : Slot (2 ^ m) V k, 8000 * (k + 2) * capacity s) =
      8000 * (k + 2) * (Fmt.payload m V k).width := by
    simp only [Fmt.payload, Format.width, Fintype.card_sigma, Fintype.card_fin, Finset.mul_sum]
  rw [eq] at t
  intro a b i j
  obtain ⟨v, hv, t⟩ := t a b i j
  refine ⟨v, hv, ?_⟩
  convert t using 1
  funext x y
  dsimp only
  congr 1
  apply propext
  constructor
  · intro he
    funext s i
    exact congrFun he ⟨s, i⟩
  · intro he
    funext ⟨s, i⟩
    exact congrFun (congrFun he s) i

end OAI.LinearAlgebra.MatrixExponent.Assembly.Payload
end

section
/-! Circuit for gathering a packet from span metadata. -/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Intervals
open Coloring
noncomputable section

variable (F : Type) [Field F] {j h k t : ℕ}

private theorem span_bound (hk : 3 * k ≤ t) : (span k).width ≤ 2 ^ 0 * (100 + t) ^ 1 := by
  simp [span]
  omega

private theorem fixed (hk : 3 * k ≤ t) (a : B k) :
    Cheap F 0 t (span k) (.addr k) (fun _ => a) 2 :=
  Cheap.const F (span_bound hk) (by simp; omega) _

private theorem cheap_key (hk : 3 * k ≤ t) : Cheap F 0 t (span k) (.addr k) key 12 := by
  have h : k ≤ t := by omega
  have x := Cheap.id F (span_bound hk)
  have lt := (x.fst.pair x.snd.fst).comp (cheap_compare F h)
  have choose := ((x.fst.pair (fixed F hk ⊤)).pair lt).comp ((cheap_select F k).widen h)
  convert choose.mono (d := 12) (by decide) using 1
  funext v
  by_cases he : v.1 < v.2.1 <;> simp [key, he]

theorem cheap_add (h : k ≤ t) : Cheap F 0 t (.pair (.addr k) (.addr k)) (.addr k) (fun x => x.1 + x.2) 4 := by
  refine ⟨_, numeric_add F k, ?_⟩
  simp only [Format.width_pair, Format.width_addr]
  ring_nf
  omega

private theorem cheap_get (q pad : B k) (hk : 3 * k ≤ t) : Cheap F 0 t (span k) (.addr k) (get q pad) 16 := by
  have h : k ≤ t := by omega
  have hadd := cheap_add F h
  have v := Cheap.id F (span_bound hk)
  have query := fixed F hk q
  have default := fixed F hk pad
  have lower := (query.pair v.fst).comp (cheap_compare F h)
  have upper := (query.pair v.snd.fst).comp (cheap_compare F h)
  have index := (query.pair v.snd.snd).comp hadd
  have sel := (cheap_select F k).widen h
  have ptr := ((index.pair default).pair upper).comp sel
  have done := ((default.pair ptr).pair lower).comp sel
  convert done.mono (d := 16) (by decide) using 1
  funext v
  by_cases h₁ : q < v.1 <;> by_cases h₂ : q < v.2.1 <;> simp [get, h₁, h₂]

private theorem cheap_packed (q : B h → B k) (pad : B k) (hk : h + 3 * k ≤ t) :
    Cheap F h t (.vec h (span k)) (Col h k) (packed q pad) 60 := by
  have hs : 3 * k ≤ t := by omega
  have hw : (span k).width ≤ t := by simp [span]; omega
  have hb := vec_bound h (show (span k).width ≤ 100 + t by omega)
  have keys := Cheap.map _ (fun _ : B h => cheap_key F hs)
  have mask := Cheap.const F hb (vec_bound (A := .bit) (t := t) h (by simp; omega)) (fun _ => true)
  have perm := (keys.pair mask).comp ((cheap_permutation F h k).widen (show h + k ≤ t by omega))
  have read := Cheap.lookup F h t (span k) (by omega) hw
  have sorted := ((Cheap.id F hb).pair perm).comp read
  have which := (sorted.comp keys).comp (cheap_seek F q (show h + k ≤ t by omega))
  have answer := ((sorted.pair which).comp read).comp (Cheap.map _ (fun b => cheap_get F (q b) pad hs))
  exact answer.mono (by decide)

/-- The two vector heights are independent of the pointer width.
Padding reads existing rows repeatedly, so it never introduces new
intervals into a query. -/
theorem cheap (query : B h → B k) (pad : B k) :
    Cheap F (max j h) (max j h + 3 * k) (.vec j (span k)) (.vec h (.addr k)) (eval query pad) 100 := by
  let n := max j h
  let t := n + 3 * k
  have width (A : Format) (ha : A.width ≤ t) (l : ℕ) (hl : l ≤ n) :
      (Format.vec l A).width ≤ 2 ^ n * (100 + t) ^ 1 :=
    (vec_bound l (ha.trans (Nat.le_add_left _ _))).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hl))
  have hs : (span k).width ≤ t := by simp [span, t]; omega
  have hk : (Format.addr k).width ≤ t := by simp [t]; omega
  have hj : j ≤ n := le_max_left _ _
  have hh : h ≤ n := le_max_right _ _
  have prep : Cheap F n t (.vec j (span k)) (.vec n (span k)) (fun x => x ∘ shrink j) 2 :=
    Cheap.project F (width _ hs _ hj) (width _ hs _ le_rfl) (fun a => (shrink j a.1, a.2))
      (fun _ _ => rfl)
  have out : Cheap F n t (Col n k) (Col h k) (fun x => x ∘ extend hh) 2 :=
    Cheap.project F (width _ hk _ le_rfl) (width _ hk _ hh) (fun a => (extend hh a.1, a.2))
      (fun _ _ => rfl)
  exact ((prep.comp (cheap_packed F (query ∘ shrink h) pad le_rfl)).comp out).mono (by decide)

end
end OAI.LinearAlgebra.MatrixExponent.Assembly.Intervals
end

section
/-! Pointers from channel starts, span lengths and local bank addresses. -/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Intervals
open Coloring
noncomputable section
variable {j h k t : ℕ}

/-- Metadata is (channel start, length, bank start). -/
def encode (r : (span k).obj) : (span k).obj := (r.1, r.1 + r.2.1, r.2.2 - r.1)

def pointers (query : B h → B k) (pad : B k) (x : B j → (span k).obj) :=
  eval query pad (encode ∘ x)

def covers (v : (span k).obj) (i : ℕ) := v.1.val ≤ i ∧ i < v.1.val + v.2.1.val

theorem contains_encode (v : (span k).obj) (b : B k) (h : v.1.val + v.2.1.val < 2 ^ k) :
    contains (encode v) b ↔ covers v b.val := by
  simp only [contains, encode, covers, Fin.le_def, Fin.lt_def, Fin.val_add, Nat.mod_eq_of_lt h]

theorem pointers_at (query : B h → B k) (pad : B k) (x : B j → (span k).obj)
    (hx : ∀ i, (x i).1.val + (x i).2.1.val < 2 ^ k) (b : B h) (i : B j)
    (hc : covers (x i) (query b).val)
    (hu : ∀ u v, covers (x i) v → covers (x u) v → u = i) :
    pointers query pad x b = (x i).2.2 + (query b - (x i).1) := by
  unfold pointers
  rw [eval_at query pad _ b i ((contains_encode _ _ (hx i)).mpr hc) (fun u v hi hj => by
    rw [hu _ _ ((contains_encode _ _ (hx i)).mp hi) ((contains_encode _ _ (hx u)).mp hj)])]
  change query b + ((x i).2.2 - (x i).1) = _
  abel

theorem pointers_pad (query : B h → B k) (pad : B k) (x : B j → (span k).obj)
    (hx : ∀ i, (x i).1.val + (x i).2.1.val < 2 ^ k) (b : B h)
    (hc : ∀ i, ¬ covers (x i) (query b).val) : pointers query pad x b = pad :=
  eval_pad query pad _ b (fun i hi => hc i ((contains_encode _ _ (hx i)).mp hi))

variable (F : Type) [Field F]

private abbrev Pair (k : ℕ) := Format.pair (.addr k) (.addr k)

/-- After k doublings the coefficient 2^k vanishes modulo 2^k. -/
theorem cheap_neg (k : ℕ) : Cheap F 0 k (.addr k) (.addr k) Neg.neg 16 := by
  let step (x : (Pair k).obj) := (x.1, x.2 + x.2 + x.1)
  have he (n : ℕ) (x : B k) : step^[n] (x, 0) = (x, (2 ^ n : ℕ) • x - x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ, mul_nsmul, two_nsmul]
      unfold step
      congr 1
      dsimp only
      abel
  have hp : (Pair k).width ≤ 2 ^ 0 * (100 + k) ^ 2 := by simp [Pair]; ring_nf; omega
  have ha : (Format.addr k).width ≤ 2 ^ 0 * (100 + k) ^ 1 := by simp
  have x := Cheap.id F hp
  have sum := cheap_add F (k := k) le_rfl
  have db := (x.snd.pair x.snd).comp sum
  have it : Cheap F 0 k (Pair k) (Pair k) step 10 :=
    (x.fst.pair ((db.pair x.fst).comp sum)).mono (by decide)
  have init := (Cheap.id F ha).pair (Cheap.const F ha ha 0)
  have run := (init.comp (it.iterate le_rfl)).snd
  convert run.mono (d := 16) (by decide) using 1
  funext x
  have hz : (2 ^ k : ℕ) • x = 0 := by simpa using (card_nsmul_eq_zero (x := x))
  change -x = (step^[k] (x, 0)).2
  rw [he, hz, zero_sub]

theorem cheap_encode (hk : 3 * k ≤ t) : Cheap F 0 t (span k) (span k) encode 24 := by
  have hv : (span k).width ≤ 2 ^ 0 * (100 + t) ^ 1 := by simp [span]; omega
  have x := Cheap.id F hv
  have h : k ≤ t := by omega
  have dest := (x.fst.pair x.snd.fst).comp (cheap_add F h)
  have neg := x.fst.comp ((cheap_neg F k).widen h)
  have bias := (x.snd.snd.pair neg).comp (cheap_add F h)
  convert (x.fst.pair (dest.pair bias)).mono (d := 24) (by decide) using 1
  funext v
  simp [encode, sub_eq_add_neg]

theorem cheap_pointers (query : B h → B k) (pad : B k) :
    Cheap F (max j h) (max j h + 3 * k) (.vec j (span k)) (.vec h (.addr k)) (pointers query pad) 101 := by
  let t := max j h + 3 * k
  have he : Cheap F (max j h) t (.vec j (span k)) (.vec j (span k)) (fun x => encode ∘ x) 24 := by
    obtain ⟨m, hm, hb⟩ := Cheap.map _ fun _ : B j => cheap_encode F (show 3 * k ≤ t by omega)
    exact ⟨m, hm, hb.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (le_max_left _ _)))⟩
  exact he.comp (cheap F query pad)

end
end OAI.LinearAlgebra.MatrixExponent.Assembly.Intervals
end

/-! A sparse edge list determines the global peer permutation. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring

namespace Peers

variable {p q : ℕ}

abbrev row (q : ℕ) := Format.pair .bit (.pair (.addr q) (.addr q))

def interval (v : (row q).obj) : (Intervals.span q).obj :=
  (v.2.1, if v.1 then 1 else 0, v.2.2)

def eval (x : B p → (row q).obj) (i : B q) : B q :=
  let j := Intervals.pointers id ⊤ (interval ∘ x) i
  if j < ⊤ then j else i

private theorem one_val {v : B q} (h : v < ⊤) : (1 : B q).val = 1 := by
  change (1 : ℕ) % 2 ^ q = 1
  apply Nat.mod_eq_of_lt
  have h₁ := (⊤ : B q).isLt
  change v.val < (⊤ : B q).val at h
  omega

theorem eval_eq (x : B p → (row q).obj) (f : B q → B q)
    (h : ∀ j, (x j).1 = true → (x j).2.1 < ⊤ ∧ (x j).2.2 < ⊤ ∧ f (x j).2.1 = (x j).2.2)
    (ha : ∀ i, f i ≠ i → ∃ j, (x j).1 = true ∧ (x j).2.1 = i) : eval x = f := by
  let y := interval ∘ x
  have fits (j : B p) : (y j).1.val + (y j).2.1.val < 2 ^ q := by
    by_cases hj : (x j).1 = true
    · have hlt := (h j hj).1
      simp only [y, Function.comp_apply, interval, ite_eq_left hj, one_val hlt]
      exact (Nat.succ_le_of_lt hlt).trans_lt (⊤ : B q).isLt
    · simp [y, interval, hj]
  have hit (j : B p) (i : B q) :
      Intervals.contains (Intervals.encode (y j)) i ↔ (x j).1 = true ∧ (x j).2.1 = i := by
    rw [Intervals.contains_encode _ _ (fits j)]
    by_cases hj : (x j).1 = true
    · simp only [Intervals.covers, y, Function.comp_apply, interval, hj, ↓reduceIte, one_val (h j hj).1,
        true_and, Fin.ext_iff]
      omega
    · simp [Intervals.covers, y, interval, hj]
  funext i
  change (if Intervals.pointers id ⊤ y i < ⊤ then Intervals.pointers id ⊤ y i else i) = f i
  by_cases hh : ∃ j, (x j).1 = true ∧ (x j).2.1 = i
  · obtain ⟨j, hj, rfl⟩ := hh
    have hv := h j hj
    have he : Intervals.pointers id ⊤ y (x j).2.1 = (x j).2.2 := by
      unfold Intervals.pointers
      rw [Intervals.eval_at _ _ _ _ j ((hit _ _).mpr ⟨hj, rfl⟩) (fun a b h₁ h₂ => by
        obtain ⟨_, he⟩ := (hit j b).mp h₁
        obtain ⟨h', he'⟩ := (hit a b).mp h₂
        have heq := he'.trans he.symm
        have ho := (h a h').2.2.symm.trans ((congrArg f heq).trans hv.2.2)
        have e : x a = x j := Prod.ext (h'.trans hj.symm) (Prod.ext heq ho)
        simp [y, e])]
      change _ + ((x j).2.2 - (x j).2.1) = _
      simp
    rw [he, ite_eq_left hv.2.1, hv.2.2]
  · have he : Intervals.pointers id ⊤ y i = ⊤ :=
      Intervals.eval_pad _ _ _ _ (fun j hj => hh ⟨j, (hit _ _).mp hj⟩)
    rw [he, ite_eq_right (lt_irrefl _)]
    exact (not_not.mp (mt (ha i) hh)).symm

end Peers

namespace Bank
variable {A D : Format} {P : Bank A D} {k d : ℕ} (i : P.Level k d)

theorem index_lt_top (v : P.Port d i.1.val) : P.index k d i v < ⊤ := by
  change (Fintype.equivFin _ v).val < 2 ^ (P.count k d i) - 1
  have h := Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card (P.Port d i.1.val) + 1)
  exact (Fintype.equivFin _ v).isLt.trans_le (by unfold count; omega)

namespace Links
variable (L : P.Links k d) (i : P.Level k d)

def peerRow (a : L.At i × Bool) : (Peers.row (P.count k d i)).obj :=
  (true, P.index k d i (L.location i a), P.index k d i (L.location i (L.opposite i a)))

theorem peers_correct {p : ℕ} (x : B p → (Peers.row (P.count k d i)).obj)
    (ok : ∀ j, (x j).1 = true → ∃ a, x j = L.peerRow i a)
    (cover : ∀ a, ∃ j, x j = L.peerRow i a) : Peers.eval x = L.plan.control.2.1 i := by
  classical
  let f := P.index k d i
  let g := L.location i
  let t := L.opposite i
  change Peers.eval x = ⇑((t.viaEmbedding g).viaEmbedding f)
  apply Peers.eval_eq
  · intro j hj
    obtain ⟨a, he⟩ := ok j hj
    rw [he]
    refine ⟨index_lt_top _ _, index_lt_top _ _, ?_⟩
    change (t.viaEmbedding g).viaEmbedding f (f (g a)) = f (g (t a))
    rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply]
  · intro b hb
    by_cases hf : b ∈ Set.range f
    · obtain ⟨a, rfl⟩ := hf
      by_cases hg : a ∈ Set.range g
      · obtain ⟨e, rfl⟩ := hg
        obtain ⟨j, hj⟩ := cover e
        exact ⟨j, by rw [hj]; rfl, by rw [hj]; rfl⟩
      · exact (hb (by rw [Equiv.Perm.viaEmbedding_apply,
          Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hg])).elim
    · exact (hb (Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hf)).elim

end Links
end Bank
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! Expand compact interval metadata only at the local channel endpoints. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Channels
open Coloring
open scoped Classical

variable {A D : Format} (S : Channels A D) (n : S.I → ℕ)

private abbrev Global := Format.pair (Fmt.pi (fun k => Perm (S.count k))) (Fmt.raw D.pins)

abbrev shortControl : Format :=
  .pair (Fmt.pi (fun i => .vec (n i) (Intervals.span (S.localWidth i)))) S.Global

def expandControl (query : ∀ i, B (S.localWidth i) → B (S.localWidth i))
    (pad : ∀ i, B (S.localWidth i)) (x : (S.shortControl n).obj) : S.control.obj :=
  (fun i => Intervals.pointers (query i) (pad i) (x.1 i), x.2)

def pointerCost (j k : ℕ) := 4 * (2 ^ max j k * (100 + (max j k + 3 * k)) ^ 101)

def expandCost := (∑ i, pointerCost (n i) (S.localWidth i)) + 4 * S.Global.width

theorem expand_control {F : Type} [Field F] {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u)
    (query : ∀ i, B (S.localWidth i) → B (S.localWidth i)) (pad : ∀ i, B (S.localWidth i)) :
    Map F u L (S.shortControl n) S.control (S.expandControl n query pad) (S.expandCost n) := by
  have h (i : S.I) : Map F u L (.vec (n i) (Intervals.span (S.localWidth i))) (Perm (S.localWidth i))
      (Intervals.pointers (query i) (pad i)) (pointerCost (n i) (S.localWidth i)) := by
    obtain ⟨m, hm, hb⟩ := Intervals.cheap_pointers F (j := n i) (query i) (pad i)
    exact (Map.circuit hu hm).mono (Nat.mul_le_mul_left _ (by omega))
  exact (Map.family h).par (Map.circuit hu (Circuit.id F S.Global))

theorem expand_bound {j k : ℕ} (hj : ∀ i, n i ≤ j) (hk : ∀ i, S.localWidth i ≤ k) :
    S.expandCost n ≤ 4 * ((Fintype.card S.I * 2 ^ j + ∑ i, 2 ^ S.localWidth i) *
      (100 + j + 4 * k) ^ 101 + (∑ i, 2 ^ S.count i * S.count i) + D.width) := by
  have hh (i : S.I) : pointerCost (n i) (S.localWidth i) ≤
      4 * ((2 ^ j + 2 ^ S.localWidth i) * (100 + j + 4 * k) ^ 101) := by
    have hu : 2 ^ max (n i) (S.localWidth i) ≤ 2 ^ j + 2 ^ S.localWidth i := by
      rw [max_def]
      split
      · exact Nat.le_add_left _ _
      · exact (Nat.pow_le_pow_right (by decide) (hj i)).trans (Nat.le_add_right _ _)
    have hx : 100 + (max (n i) (S.localWidth i) + 3 * S.localWidth i) ≤ 100 + j + 4 * k := by
      have := hj i
      have := hk i
      omega
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hu (Nat.pow_le_pow_left hx _))
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at ht
  unfold expandCost
  rw [show S.Global.width = (∑ i, 2 ^ S.count i * S.count i) + D.width by simp [Global]]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Channels
end

/-!
# Encoding active gathers by disjoint runs

A run specifies its first position in the packed lane, length and
first bank address. No condition is needed on unused ports, whose
permutation is the identity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Bank

open Coloring
open scoped Classical

variable {A D : Format} {P : Bank A D} {k d : ℕ}

private theorem Plan.pointer_eq (p : P.Plan k d) (i : P.Level k d) (e : P.Port d i.1.val)
    (b : B i.1.val) :
    p.control.1 ⟨i, e.1⟩ (P.bitIndex k d ⟨i, e.1⟩ (e.2, b)) = encode (p.pointer i e b) := by
  unfold Plan.control
  dsimp only
  rw [(P.bitIndex k d ⟨i, e.1⟩).injective.extend_apply]

namespace Links
variable (M : P.Links k d)


def vector (i : P.Level k d) (e : M.At i × Bool) : P.Endpoint k d := ⟨i, (M.location i e).1⟩

def offset (i : P.Level k d) (e : M.At i × Bool) (b : B i.1.val) :=
  P.bitIndex k d (M.vector i e) ((M.location i e).2, b)

theorem offset_val (i : P.Level k d) (e : M.At i × Bool) (b : B i.1.val) :
    (M.offset i e b).val = b.val + 2 ^ i.1.val * (M.location i e).2.val := rfl

/-- Equality of commands where they are actually read. -/
structure Represents (q : (P.channels k d).control.obj) : Prop where
  peer : q.2.1 = M.plan.control.2.1
  mask : q.2.2 = M.pad
  reads : ∀ i e b, q.1 (M.vector i e) (M.offset i e b) =
    encode (M.plan.pointer i (M.location i e) b)

private theorem Represents.atPort {q : (P.channels k d).control.obj} (hq : M.Represents q)
    (i : P.Level k d) (e : M.At i × Bool) (b : B i.1.val) :
    (P.channels k d).atPort q i (P.index k d i (M.location i e)) b =
      (P.channels k d).atPort M.plan.control i (P.index k d i (M.location i e)) b := by
  have ht : (P.channels k d).tap i (P.index k d i (M.location i e)) b =
      some ⟨M.vector i e, M.offset i e b⟩ := by
    unfold channels
    dsimp only
    exact (P.index k d i).injective.extend_apply _ _ _
  have hr : q.1 (M.vector i e) (M.offset i e b) =
      M.plan.control.1 (M.vector i e) (M.offset i e b) :=
    (hq.reads i e b).trans (M.plan.pointer_eq i (M.location i e) b).symm
  unfold Channels.atPort
  rw [ht, Option.bind_some, Option.bind_some]
  exact congrArg ((P.channels k d).bank (M.vector i e)) hr

theorem Represents.carries {q : (P.channels k d).control.obj} (hq : M.Represents q)
    (x : A.obj) (y : D.obj) : (P.channels k d).Carries q x y ↔ M.Matches x y := by
  let S := P.channels k d
  let a := M.plan.control
  have he (i : P.Level k d) (j : B (P.count k d i)) (b : B i.1.val) :
      Channels.value x y (S.atPort q i j b) = Channels.value x y (S.atPort q i (a.2.1 i j) b) ↔
      Channels.value x y (S.atPort a i j b) = Channels.value x y (S.atPort a i (a.2.1 i j) b) := by
    by_cases h₁ : j ∈ Set.range (P.index k d i)
    swap
    · rw [show a.2.1 i j = j from Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ h₁]
      simp
    obtain ⟨t, rfl⟩ := h₁
    rw [show a.2.1 i (P.index k d i t) = P.index k d i (M.plan.peer i t) from
      Equiv.Perm.viaEmbedding_apply _ _ _]
    by_cases h₂ : t ∈ Set.range (M.location i)
    swap
    · rw [show M.plan.peer i t = t from Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ h₂]
      simp
    obtain ⟨⟨e, c⟩, rfl⟩ := h₂
    rw [M.peer_at, Represents.atPort M hq i (e, c) b, Represents.atPort M hq i (e, !c) b]
  rw [← M.carries]
  unfold Channels.Carries
  rw [hq.peer, hq.mask]
  exact and_congr Iff.rfl (forall_congr' fun i =>
    and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun b => he i j b))

end Links
end OAI.LinearAlgebra.MatrixExponent.Assembly.Bank
end

/-! # Expanding a description by contiguous intervals -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Bank
open Coloring
open scoped Classical

variable {A D : Format} (P : Bank A D) (k d : ℕ) (n : P.Endpoint k d → ℕ)

abbrev intervals := Fmt.pi (fun i => .vec (n i) (Intervals.span (P.localWidth k d i)))

def sentinel (i : P.Endpoint k d) : B (P.localWidth k d i) := encode none

variable {P k d} (M : P.Links k d) (x : (P.intervals k d n).obj)

namespace Links

/-- Span starts are measured from the start of the whole packed
buffer. The first bit of lane `i` in a level-`j` buffer is at
`i*2^j`. -/
structure Runs : Prop where
  fits : ∀ i u, (x i u).1.val + (x i u).2.1.val < 2 ^ (P.localWidth k d i)
  disjoint : ∀ i a b t, Intervals.covers (x i a) t → Intervals.covers (x i b) t → b = a
  live : ∀ i (e : M.At i × Bool) (b : B i.1.val) (h : b.val < M.length e.1.val),
    let r := M.vector i e
    let t := (M.offset i e b).val
    ∃ v, Intervals.covers (x r v) t ∧
      (x r v).2.2.val + (t - (x r v).1.val) = (M.pointer e.1.val e.2 ⟨b.val, h⟩).val
  gap : ∀ i (e : M.At i × Bool) (b : B i.1.val), M.length e.1.val ≤ b.val →
    ∀ v, ¬Intervals.covers (x (M.vector i e) v) (M.offset i e b).val

theorem Runs.read (h : M.Runs n x) (i : P.Level k d) (e : M.At i × Bool) (b : B i.1.val) :
    Intervals.pointers id (P.sentinel k d (M.vector i e)) (x (M.vector i e)) (M.offset i e b)
      = encode (M.plan.pointer i (M.location i e) b) := by
  apply Fin.ext
  rw [M.pointer_at]
  let r := M.vector i e
  let t := M.offset i e b
  split
  · rename_i hb
    obtain ⟨v, hv, he⟩ := h.live i e b hb
    have ht := Intervals.pointers_at id (P.sentinel k d r) (x r) (h.fits r) t v hv (h.disjoint r v)
    change (Intervals.pointers id (P.sentinel k d r) (x r) t).val = _
    rw [ht, id_eq, Fin.val_add, Fin.sub_val_of_le (show (x r v).1 ≤ t from hv.1)]
    change (x r v).2.2.val + (t.val - (x r v).1.val) = _ at he
    rw [he]
    exact Nat.mod_eq_of_lt ((M.pointer _ _ _).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
  · rename_i hb
    have ht := Intervals.pointers_pad id (P.sentinel k d r) (x r) (h.fits r) t
      (h.gap i e b (Nat.le_of_not_gt hb))
    exact congrArg Fin.val ht

theorem Runs.represents (h : M.Runs n x) :
    M.Represents ((P.channels k d).expandControl n (fun _ => id) (P.sentinel k d)
      (x, M.plan.control.2)) := by
  refine ⟨rfl, rfl, fun i e b => ?_⟩
  exact Runs.read n M x h i e b

end Links
end OAI.LinearAlgebra.MatrixExponent.Assembly.Bank
end

/-!
# Changing the station number of the exterior

At a host, all exterior bits use a common station number. Changing
this number preserves their order by block, span and bit offset.
Thus the same physical payload can be used before and after the cut.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Coloring
open scoped Classical

variable {F : Type} [Field F] {S U : Scheme F} {x : S.format.obj} {y : U.format.obj}
  {a b : Wire} {G H : Diagram F a b} (p : S.Presentation x G) (q : U.Presentation y H)
  {V k : ℕ}

structure Retag : Prop where
  m : U.m = S.m
  owner : ∀ i, (U.owner y (q.boundary i)).val = (S.owner x (p.boundary i)).val
  block : ∀ i, (q.boundary i).val.1.1.2.1.val = (p.boundary i).val.1.1.2.1.val
  span : ∀ i, (q.boundary i).val.1.2.val = (p.boundary i).val.1.2.val
  offset : ∀ i, (q.boundary i).val.2.val = (p.boundary i).val.2.val
  left : ∀ i j, (p.boundary i).val.1.1.2.2 = (p.boundary j).val.1.1.2.2
  right : ∀ i j, (q.boundary i).val.1.1.2.2 = (q.boundary j).val.1.1.2.2

namespace Retag
variable {p q} (t : Retag p q)

private abbrev names := finCongr (congrArg (fun v => 2 ^ v) t.m)

theorem load (v : B U.m) : U.load y v = S.load x (names t v) := by
  let e := q.boundary.symm.trans p.boundary
  have same (j : U.exposed y) : U.owner y j = v ↔ S.owner x (e j) = t.names v := by
    have eq := t.owner (q.boundary.symm j)
    simp only [Equiv.apply_symm_apply] at eq
    simp only [Fin.ext_iff]
    exact iff_of_eq (congrArg (· = v.val) eq)
  exact Fintype.card_congr (e.subtypeEquiv same)

include t in
theorem fits (h : S.Fits x V k) : U.Fits y V k := by
  refine ⟨?_, fun v => (t.load v).le.trans (h.2 _)⟩
  simpa only [t.load, (t.names).sum_comp (fun v => max 1 (S.load x v))] using h.1

omit [Field F] in
private theorem precedes (f : S.Fits x V k) (i j : S.exposed x) (hs : S.owner x i = S.owner x j)
    (h : S.spanIndex i.val.1 < S.spanIndex j.val.1) :
    (S.index x f i).2.val < (S.index x f j).2.val := by
  have small (u : S.exposed x) : u.val.2.val < S.extent x (S.owner x u) (S.spanIndex u.val.1) := by
    simp [Scheme.extent, Scheme.owner, u.property]
  have hi := small i
  rw [hs] at hi
  rw [S.index_val, S.index_val, hs]
  exact Routing.offset_lt (S.extent x (S.owner x j)) Fin.val
    (u := ⟨_, ⟨_, hi⟩⟩) (z := ⟨_, ⟨_, small j⟩⟩) h

omit [Field F] in
private theorem index_order (f : S.Fits x V k) (i j : S.exposed x) (hs : S.owner x i = S.owner x j) :
    (S.index x f i).2.val < (S.index x f j).2.val ↔
      S.spanIndex i.val.1 < S.spanIndex j.val.1 ∨
        S.spanIndex i.val.1 = S.spanIndex j.val.1 ∧ i.val.2.val < j.val.2.val := by
  rcases lt_trichotomy (S.spanIndex i.val.1) (S.spanIndex j.val.1) with h | h | h
  · exact iff_of_true (precedes f i j hs h) (.inl h)
  · simp [S.index_val, hs, h]
  · exact iff_of_false (precedes f j i hs.symm h).not_gt
      (fun hh => hh.elim h.not_gt (fun h' => h.ne' h'.1))

omit [Field F] in
private theorem span_order (i j : S.Span) (he : i.1.2.2 = j.1.2.2) :
    S.spanIndex i < S.spanIndex j ↔ i.1.2.1.val < j.1.2.1.val ∨
      (i.1.2.1.val = j.1.2.1.val ∧ i.2.val < j.2.val) := by
  change (Match.rowIndex _ _).symm ((Match.rowIndex S.h S.k).symm i.1.2, i.2) <
    (Match.rowIndex _ _).symm ((Match.rowIndex S.h S.k).symm j.1.2, j.2) ↔ _
  rw [rowIndex_lt, rowIndex_lt, (Match.rowIndex S.h S.k).symm.injective.eq_iff, Prod.ext_iff, he]
  simp only [lt_self_iff_false, and_false, or_false, and_true, Fin.lt_def, Fin.ext_iff]

include t in
theorem order (f : S.Fits x V k) (g : U.Fits y V k) (i j : slots a ⊕ slots b)
    (hh : S.owner x (p.boundary i) = S.owner x (p.boundary j)) :
    (U.index y g (q.boundary i)).2.val < (U.index y g (q.boundary j)).2.val ↔
      (S.index x f (p.boundary i)).2.val < (S.index x f (p.boundary j)).2.val := by
  have hv : U.owner y (q.boundary i) = U.owner y (q.boundary j) :=
    Fin.ext (by rw [t.owner, t.owner, hh])
  have hf (u v) : U.spanIndex (q.boundary u).val.1 < U.spanIndex (q.boundary v).val.1 ↔
      S.spanIndex (p.boundary u).val.1 < S.spanIndex (p.boundary v).val.1 := by
    rw [span_order _ _ (t.right ..), span_order _ _ (t.left ..), t.block, t.block, t.span, t.span]
  have he : U.spanIndex (q.boundary i).val.1 = U.spanIndex (q.boundary j).val.1 ↔
      S.spanIndex (p.boundary i).val.1 = S.spanIndex (p.boundary j).val.1 := by
    simp only [le_antisymm_iff, ← not_lt, hf]
  rw [index_order g _ _ hv, index_order f _ _ hh, hf, he, t.offset, t.offset]

end Retag
end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-! # Uniqueness of the order-preserving enumeration in a payload bank -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring

variable {m n V k : ℕ} {I : Type}

private theorem same_order (P : Payload m V k) (f g : I ≃ P.Bit)
    (host : ∀ i, (g i).1.val = (f i).1.val)
    (order : ∀ i j, (f i).1 = (f j).1 → (f i).2.val < (f j).2.val → (g i).2.val < (g j).2.val) :
    g = f := by
  have first (i) := Fin.ext (host i)
  have eq (v : B m) (i : Fin (P.length v)) :
      g (f.symm ⟨v, i⟩) = ⟨v, i⟩ := by
    have hv (j : Fin (P.length v)) : (g (f.symm ⟨v, j⟩)).1 = v :=
      (first _).trans (congrArg Sigma.fst (f.apply_symm_apply _))
    let perm (j : Fin (P.length v)) : Fin (P.length v) :=
      (g (f.symm ⟨v, j⟩)).2.cast (congrArg _ (hv j))
    have mono : StrictMono perm := by
      intro i j hij
      exact order _ _ (by rw [f.apply_symm_apply, f.apply_symm_apply])
        (by rw [f.apply_symm_apply, f.apply_symm_apply]; exact hij)
    exact Sigma.ext (hv i) ((Fin.heq_ext_iff (congrArg P.length (hv i))).mpr
      (congrArg Fin.val (congrFun mono.eq_id i)))
  exact Equiv.ext fun i => by simpa using eq (f i).1 (f i).2

private theorem same_bank (P : Payload m V k) (Q : Payload n V k) (hm : n = m)
    (length : ∀ v, Q.length v = P.length (finCongr (congrArg (fun t => 2 ^ t) hm) v))
    (f : I ≃ P.Bit) (g : I ≃ Q.Bit)
    (host : ∀ i, (g i).1.val = (f i).1.val)
    (order : ∀ i j, (f i).1 = (f j).1 → (f i).2.val < (f j).2.val → (g i).2.val < (g j).2.val)
    (s : P.Bit → Bool) (t : Q.Bit → Bool) (read : ∀ i, t (g i) = s (f i)) :
    HEq (Q.store t) (P.store s) := by
  subst n
  have he : Q.length = P.length := funext length
  have h : Q = P := by cases Q; cases P; cases he; rfl
  subst Q
  have hf := same_order P f g host order
  subst g
  have ht : t = s := by
    funext j
    obtain ⟨i, rfl⟩ := f.surjective j
    exact read i
  rw [ht]

namespace Scheme.Presentation.Retag
variable {F : Type} [Field F] {S U : Scheme F} {x : S.format.obj} {y : U.format.obj}
  {a b : Wire} {G H : Diagram F a b} {p : S.Presentation x G} {q : U.Presentation y H}
  (t : Retag p q)

theorem store (h : S.Fits x V k) (i : Val a) (j : Val b) :
    HEq (U.store y (t.fits h) (q.exterior i j)) (S.store x h (p.exterior i j)) := by
  refine same_bank (S.payload x h) (U.payload y (t.fits h)) t.m t.load
    (p.boundary.trans (S.index x h)) (q.boundary.trans (U.index y (t.fits h))) t.owner
    (fun i j he => (t.order h (t.fits h) i j he).mpr) _ _ ?_
  intro u
  simp only [Equiv.trans_apply, Function.comp_apply, Equiv.symm_apply_apply, exterior_boundary]

end Scheme.Presentation.Retag
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! Expand sparse peers as singleton intervals. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Peers

open Coloring
variable (F : Type) [Field F] {q t : ℕ}

private theorem prepare (hq : q ≤ t) :
    Cheap F 0 t (row q) (Intervals.span q) interval 12 := by
  have hi : (row q).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp [row]; ring_nf; omega
  have hw : (Format.addr q).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp; ring_nf; omega
  have x := Cheap.id F hi
  have u := ((Cheap.const F hi hw 1).pair (Cheap.const F hi hw 0)).pair x.fst
  have len := u.comp ((cheap_select F q).widen hq)
  exact (x.snd.fst.pair (len.pair x.snd.snd)).mono (by decide)

private theorem restore (hq : q ≤ t) (i : B q) :
    Cheap F 0 t (.addr q) (.addr q) (fun x => if x < ⊤ then x else i) 12 := by
  have hw : (Format.addr q).width ≤ 2 ^ 0 * (100 + t) ^ 1 := by simp; omega
  have x := Cheap.id F hw
  have lt := (x.pair (Cheap.const F hw hw ⊤)).comp (Intervals.cheap_compare F hq)
  have y := ((x.pair (Cheap.const F hw hw i)).pair lt).comp ((cheap_select F q).widen hq)
  convert y.mono (d := 12) (by decide) using 1
  funext x
  by_cases h : x < ⊤ <;> simp [h]

theorem lift {A D : Format} {f : A.obj → D.obj} {h k c : ℕ}
    (v : Cheap F h t A D f c) (hk : h ≤ k) : Cheap F k t A D f c := by
  obtain ⟨m, hm, h⟩ := v
  exact ⟨m, hm, h.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hk))⟩

theorem cheap (p q : ℕ) :
    Cheap F (max p q) (max p q + 3 * q) (.vec p (row q)) (Perm q) eval 110 := by
  have hq : q ≤ max p q + 3 * q := by omega
  have a := lift F (Cheap.map _ (fun _ : B p => prepare F hq)) (le_max_left p q)
  have b := Intervals.cheap_pointers F (j := p) (h := q) id ⊤
  have c := lift F (Cheap.map _ (restore F hq)) (le_max_right p q)
  exact ((a.comp b).comp c).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Peers
end

/-! Reading physical port addresses from fixed slot-and-lane lookup tables. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring

namespace Peers
variable (F : Type) [Field F]

private theorem full_table (R : Format) {p q t : ℕ} (hr : R.width = p) (hp : p ≤ t) (hq : q ≤ t)
    (v : R.obj → B q) :
    Cheap F p t (.vec p R) (.vec p (.addr q)) (fun x => v ∘ x) 10 := by
  subst p
  have hi := Intervals.vec_bound R.width (show R.width ≤ 100 + t by omega)
  have ht := Cheap.const F hi (column_width R.width hq) (v ∘ R.serial.symm)
  have read := (ht.pair (cheap_keys R F R.width hp)).comp (Cheap.lookup F R.width t (.addr q) hp
    (by simpa using hq))
  convert read.mono (d := 10) (by decide) using 1
  funext x j
  simp [Format.keys]

theorem cheap_table (p : ℕ) (R : Format) {q : ℕ} (v : R.obj → B q) :
    Cheap F (max p R.width) (max p R.width + q + 1) (.vec p R) (.vec p (.addr q)) (fun x => v ∘ x) 20 := by
  let n := max p R.width
  let t := n + q + 1
  let K := Format.pair R (.addr (n - R.width))
  have hk : K.width = n := by simp [K, n]
  have hp : p ≤ n := le_max_left _ _
  have width (A : Format) (ha : A.width ≤ t) (l : ℕ) (hl : l ≤ n) :
      (Format.vec l A).width ≤ 2 ^ n * (100 + t) ^ 1 :=
    (Intervals.vec_bound l (ha.trans (Nat.le_add_left _ _))).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hl))
  have hr : R.width ≤ t := by omega
  have hq : (Format.addr q).width ≤ t := by simp [t]; omega
  have pad : Cheap F n t (.vec p R) (.vec n R) (fun x => x ∘ Intervals.shrink p) 2 :=
    Cheap.project F (width _ hr p hp) (width _ hr n le_rfl) (fun i => (Intervals.shrink p i.1, i.2))
      (fun _ _ => rfl)
  have zeros := Cheap.const F (width _ hr p hp)
    (column_width n (show n - R.width ≤ t by omega)) (fun _ => 0)
  have read := full_table F K hk (show n ≤ t by omega) (show q ≤ t by omega) (fun z => v z.1)
  have out : Cheap F n t (.vec n (.addr q)) (.vec p (.addr q))
      (fun x => x ∘ Intervals.extend hp) 2 :=
    Cheap.project F (width _ hq n le_rfl) (width _ hq p hp) (fun i => (Intervals.extend hp i.1, i.2))
      (fun _ _ => rfl)
  convert (((pad.pair zeros).zip.comp read).comp out).mono (d := 20) (by decide) using 1
  funext x i
  simp only [Function.comp_apply, Intervals.shrink_extend]

end Peers

namespace Bank
variable {A D : Format} (P : Bank A D) {k d h q : ℕ} (i : P.Level k d)
  (host : P.Slot ↪ B h) (hd : d ≤ 2 ^ q)

abbrev pairCode (h q : ℕ) := Format.pair (.addr h) (.addr q)

def codePort : P.Port d i.1.val ↪ (pairCode h q).obj where
  toFun e := (host e.1.val, e.2.castLE ((min_le_left _ _).trans hd))
  inj' := by
    rintro ⟨s, v⟩ ⟨t, w⟩ he
    have h : s = t := Subtype.ext (host.injective (congrArg Prod.fst he))
    subst t
    have h : v = w := Fin.ext (congrArg (fun x => x.2.val) he)
    rw [h]

def portTable : (pairCode h q).obj → B (P.count k d i) :=
  Function.extend (P.codePort i host hd) (P.index k d i) (fun _ => ⊤)

theorem portTable_at (e : P.Port d i.1.val) :
    P.portTable i host hd (P.codePort i host hd e) = P.index k d i e :=
  (P.codePort i host hd).injective.extend_apply _ _ _

end Bank
end OAI.LinearAlgebra.MatrixExponent.Assembly
end
