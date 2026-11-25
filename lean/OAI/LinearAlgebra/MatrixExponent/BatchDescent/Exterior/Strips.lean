import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.EquivFin
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Pieces
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Plan
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dictionary
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.PortRelay
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior.Supply

/-!
# Padding exterior stacks to whole rows

Reserve one partial row per occupied holder. Unused slots receive
dummy stacks so the reindexing is a bijection on a fixed tape.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Finset
open scoped Classical

variable {S I : Type} [Fintype S] [DecidableEq I]

/-- A genuine stack and its padding copy occupy distinct slots. -/
structure Grouping (holder : S → I) (C Q : Type) [Fintype Q] where
  order : S ⊕ S ≃ C × Q
  same : ∀ s t, (order (.inl s)).1 = (order (.inl t)).1 → holder s = holder t
  rows : ∀ i, ((univ.filter fun s => holder s = i).image fun s => (order (.inl s)).1).card ≤
    1 + Fintype.card {s // holder s = i} / Fintype.card Q

private theorem padded {B : Type} [Fintype B] (e : S ↪ B)
    (hc : Fintype.card B = 2 * Fintype.card S) :
    ∃ f : S ⊕ S ≃ B, ∀ s, f (.inl s) = e s := by
  let u := Equiv.ofInjective e e.injective
  let v := Equiv.Set.sumCompl (Set.range e)
  have hb := Fintype.card_congr v
  rw [Fintype.card_sum, ← Fintype.card_congr u, hc] at hb
  let w : S ≃ ↥(Set.range e)ᶜ := Fintype.equivOfCardEq (by omega)
  exact ⟨(u.sumCongr w).trans v, fun _ => rfl⟩

abbrev Fiber (holder : S → I) (i : I) := {t // holder t = i}

/-- Ceiling of the stack count divided by the capacity `q`, with
zero rows for an unoccupied holder. -/
def needed (holder : S → I) (q : ℕ) (i : I) :=
  if i ∈ univ.image holder then (Fintype.card (Fiber holder i) - 1) / q + 1 else 0

private theorem needed_le (holder : S → I) (q : ℕ) (i : I) :
    needed holder q i ≤ (if i ∈ univ.image holder then 1 else 0) +
      Fintype.card (Fiber holder i) / q := by
  unfold needed
  have ht := Nat.div_le_div_right (c := q) (Nat.sub_le (Fintype.card (Fiber holder i)) 1)
  split_ifs
  · omega
  · exact Nat.zero_le _

/-- Within each holder the rank fixes both the local row and offset. -/
def orderedSlot (holder : S → I) (q : ℕ) (hq : 0 < q) (i : I)
    (rank : Fiber holder i ≃ Fin (Fintype.card (Fiber holder i))) :
    Fiber holder i ↪ Fin (needed holder q i) × Fin q where
  toFun t := (⟨(rank t).val / q, by
    rw [needed, ite_eq_left (mem_image.mpr ⟨t.val, mem_univ _, t.property⟩)]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_pred_of_lt (rank t).isLt))⟩,
    ⟨(rank t).val % q, Nat.mod_lt _ hq⟩)
  inj' := by
    intro t t' h
    apply rank.injective
    apply Fin.ext
    simpa only [Nat.div_add_mod] using congrArg (fun z => q * z.1.val + z.2.val) h

private theorem assigned [Fintype I] (holder : S → I) (C Q : Type) [Fintype C] [Fintype Q]
    (q : ℕ) (hQ : Fintype.card Q = q) (hq : 0 < q)
    (hp : (univ.image holder).card * q ≤ Fintype.card S)
    (hsize : Fintype.card C * q = 2 * Fintype.card S)
    (slot : ∀ i, Fiber holder i ↪ Fin (needed holder q i) × Q) :
    ∃ (e : Grouping holder C Q) (r : (Σ i, Fin (needed holder q i)) ↪ C),
      ∀ i (s : Fiber holder i), e.order (.inl s.val) = (r ⟨i, (slot i s).1⟩, (slot i s).2) := by
  let used := univ.image holder
  let n := needed holder q
  have hsum : (∑ i, Fintype.card (Fiber holder i)) = Fintype.card S := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv holder)
  have total : (∑ i, n i) * q ≤ Fintype.card C * q := calc
    _ ≤ (∑ i, ((if i ∈ used then 1 else 0) + Fintype.card (Fiber holder i) / q)) * q :=
      Nat.mul_le_mul_right _ (sum_le_sum fun i _ => needed_le holder q i)
    _ = used.card * q + ∑ i, Fintype.card (Fiber holder i) / q * q := by
      simp [sum_add_distrib, add_mul, sum_mul]
    _ ≤ used.card * q + Fintype.card S := by
      rw [← hsum]
      exact Nat.add_le_add_left (sum_le_sum fun i _ => Nat.div_mul_le_self _ _) _
    _ ≤ _ := by unfold used; omega
  obtain ⟨rows⟩ : Nonempty ((Σ i, Fin (n i)) ↪ C) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa using Nat.le_of_mul_le_mul_right total hq)
  let e : S ↪ C × Q := (Equiv.sigmaFiberEquiv holder).symm.toEmbedding.trans <|
    ((Function.Embedding.refl I).sigmaMap slot).trans <|
    (Equiv.sigmaProdDistrib _ _).symm.toEmbedding.trans (rows.prodMap (.refl Q))
  obtain ⟨f, hf⟩ := padded e (by simpa [hQ] using hsize)
  have position (i : I) (s : Fiber holder i) :
      f (.inl s.val) = (rows ⟨i, (slot i s).1⟩, (slot i s).2) := by
    rcases s with ⟨s, rfl⟩
    rw [hf]
    rfl
  refine ⟨⟨f, ?_, ?_⟩, rows, position⟩
  · intro s t h
    rw [position _ ⟨s, rfl⟩, position _ ⟨t, rfl⟩] at h
    exact congrArg Sigma.fst (rows.injective h)
  · intro i
    calc
      _ ≤ (univ.image fun j : Fin (n i) => rows ⟨i, j⟩).card := by
        apply card_le_card
        intro c hc
        obtain ⟨s, hs, rfl⟩ := mem_image.mp hc
        rw [position _ ⟨s, (mem_filter.mp hs).2⟩]
        exact mem_image_of_mem _ (mem_univ _)
      _ ≤ n i := by simpa using (card_image_le (s := univ) (f := fun j : Fin (n i) => rows ⟨i, j⟩))
      _ ≤ _ := by
        rw [hQ]
        exact (needed_le holder q i).trans (Nat.add_le_add_right (by split_ifs <;> omega) _)

/-- If one row per occupied holder fits in the padding budget, doubling
the stack count suffices, preserving any prescribed order inside each holder. -/
theorem group_order [Fintype I] (holder : S → I) (C : Type) [Fintype C] (q : ℕ) (hq : 0 < q)
    (hp : (univ.image holder).card * q ≤ Fintype.card S)
    (hsize : Fintype.card C * q = 2 * Fintype.card S)
    (rank : ∀ i, Fiber holder i ≃ Fin (Fintype.card (Fiber holder i))) :
    ∃ (e : Grouping holder C (Fin q)) (r : (Σ i, Fin (needed holder q i)) ↪ C),
      ∀ i (s : Fiber holder i), e.order (.inl s.val) =
        (r ⟨i, (orderedSlot holder q hq i (rank i) s).1⟩, (orderedSlot holder q hq i (rank i) s).2) :=
  assigned holder C (Fin q) q (Fintype.card_fin _) hq hp hsize
    (fun i => orderedSlot holder q hq i (rank i))

theorem group [Fintype I] (holder : S → I) (C Q : Type) [Fintype C] [Fintype Q]
    (hq : 0 < Fintype.card Q) (hp : (univ.image holder).card * Fintype.card Q ≤ Fintype.card S)
    (hsize : Fintype.card C * Fintype.card Q = 2 * Fintype.card S) :
    Nonempty (Grouping holder C Q) := by
  obtain ⟨e, _⟩ := assigned holder C Q _ rfl hq hp hsize fun i =>
    (orderedSlot holder _ hq i (Fintype.equivFin _)).trans <|
      (Function.Embedding.refl _).prodMap (Fintype.equivFin Q).symm.toEmbedding
  exact ⟨e⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end

/-! # Canonical port ordinals for exterior stacks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Finset
open scoped Classical

variable {J S : Type} [Fintype J] [Fintype S] {H m d : ℕ}
  (loc : J → S → Fin H × Fin m) (χ : Fin H → J → Fin d)

private def position (x : J × S) := (loc x.1 x.2, χ (loc x.1 x.2).1 x.1)

def counts : PackRows.Inventory H m d :=
  fun i t c => Fintype.card {x // position loc χ x = ((i, t), c)}

def lengths (b : ℕ) : PackRows.Inventory H m d := fun i t c => counts loc χ i t c * b

theorem lengths_eq (b : ℕ) (i : Fin H) (t : Fin m) (c : Fin d) :
    lengths loc χ b i t c =
      (univ.filter fun x : J × S => loc x.1 x.2 = (i, t) ∧ χ (loc x.1 x.2).1 x.1 = c).card * b := by
  simp only [lengths, counts, Fintype.card_subtype, position, Prod.mk.injEq]

private def flattenFromPoints (l : PackRows.Inventory H m d) :
    (Σ z : (Fin H × Fin m) × Fin d, Fin (l z.1.1 z.1.2 z.2)) ≃ PackRows.Endpoints l where
  toFun p := ⟨p.1.1.1, p.1.1.2, p.1.2, p.2⟩
  invFun p := ⟨((p.1, p.2.1), p.2.2.1), p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def sortedIndex {A : Type} [Fintype A] (key : A → ℕ) (hk : Function.Injective key) :
    A ≃ Fin (Fintype.card A) :=
  let e : A ≃ Σ _ : A, Fin 1 :=
    ⟨fun x => ⟨x, 0⟩, Sigma.fst, fun _ => rfl, fun x => by
      rcases x with ⟨x, i⟩; rw [Fin.eq_zero i]⟩
  (e.trans (Routing.pack (fun _ => 1) key (fun _ _ _ _ he => hk he))).trans (finCongr (by simp))

private def index : J × S ≃ Fin (Fintype.card J * Fintype.card S) :=
  ((Fintype.equivFin J).prodCongr (Fintype.equivFin S)).trans finProdFinEquiv

private def orderedAt (z : (Fin H × Fin m) × Fin d) :
    Fiber (position loc χ) z ≃ Fin (Fintype.card (Fiber (position loc χ) z)) :=
  sortedIndex (fun t => (index t.val).val)
    (Fin.val_injective.comp (index.injective.comp Subtype.val_injective))

def stack : J × S ≃ PackRows.Endpoints (counts loc χ) :=
  (Equiv.sigmaFiberEquiv (position loc χ)).symm.trans <|
    (Equiv.sigmaCongrRight (orderedAt loc χ)).trans
      (flattenFromPoints (counts loc χ))

/-- The position of a stack on its channel depends only on the
stack indices present at the same occurrence. -/
theorem stack_slot
    (sep : ∀ i j a b, (loc i a).1 = (loc j b).1 → χ (loc i a).1 i = χ (loc j b).1 j → i = j)
    (i : J) (s : S) :
    (stack loc χ (i, s)).2.2.2.val =
      (univ.filter fun t => loc i t = loc i s ∧ Fintype.equivFin S t < Fintype.equivFin S s).card := by
  let pos := position loc χ
  let key : J × S → ℕ := fun t => (index t).val
  change (∑ _t ∈ (univ.filter fun t : Fiber pos (pos (i, s)) => key t.val < key (i, s)), 1) = _
  rw [sum_filter, ← sum_subtype (univ.filter fun z => pos z = pos (i, s))
    (fun _ => mem_filter_univ _) (fun z => if key z < key (i, s) then 1 else 0), sum_filter,
    Fintype.sum_prod_type, sum_eq_single i]
  · rw [card_eq_sum_ones, sum_filter]
    refine sum_congr rfl fun t _ => ?_
    have he : key (i, t) < key (i, s) ↔ Fintype.equivFin S t < Fintype.equivFin S s := by
      change _ + Fintype.card S * (Fintype.equivFin J i).val <
        _ + Fintype.card S * (Fintype.equivFin J i).val ↔ _
      exact Nat.add_lt_add_iff_right
    by_cases h : loc i t = loc i s <;> simp [pos, position, h, he]
  · intro j _ hj
    refine sum_eq_zero fun t _ => ite_eq_right ?_
    intro he
    exact hj (sep j i t s (congrArg (fun z => z.1.1) he) (congrArg Prod.snd he))
  · simp

private def scale (l : PackRows.Inventory H m d) (b : ℕ) :
    PackRows.Endpoints l × Fin b ≃ PackRows.Endpoints (fun i t c => l i t c * b) where
  toFun p := ⟨p.1.1, p.1.2.1, p.1.2.2.1, finProdFinEquiv (p.1.2.2.2, p.2)⟩
  invFun p := (⟨p.1, p.2.1, p.2.2.1, (finProdFinEquiv.symm p.2.2.2).1⟩,
    (finProdFinEquiv.symm p.2.2.2).2)
  left_inv p := by simp
  right_inv p := by
    obtain ⟨i, t, c, j⟩ := p
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

/-- All finest bundles of a stack are consecutive at its port. -/
def point (b : ℕ) : (J × S) × Fin b ≃ PackRows.Endpoints (lengths loc χ b) :=
  ((stack loc χ).prodCongr (.refl _)).trans (scale _ b)

@[simp] theorem point_host {b : ℕ} (i : J) (s : S) (k : Fin b) :
    (point loc χ b ((i, s), k)).1 = (loc i s).1 := rfl

@[simp] theorem point_block {b : ℕ} (i : J) (s : S) (k : Fin b) :
    (point loc χ b ((i, s), k)).2.1 = (loc i s).2 := rfl

@[simp] theorem point_channel {b : ℕ} (i : J) (s : S) (k : Fin b) :
    (point loc χ b ((i, s), k)).2.2.1 = χ (loc i s).1 i := rfl

theorem point_slot {b : ℕ} (x : J × S) (k : Fin b) :
    (point loc χ b (x, k)).2.2.2.val = (stack loc χ x).2.2.2.val * b + k.val := by
  change k.val + b * (stack loc χ x).2.2.2.val = _
  ac_rfl

theorem point_rank {b : ℕ} (x : J × S) (k : Fin b) :
    PackRows.rank _ (point loc χ b (x, k)) = PackRows.rank _ (stack loc χ x) * b + k.val := by
  let z := stack loc χ x
  change PackRows.start (fun i => counts loc χ z.1 i z.2.2.1 * b) z.2.1 +
    (finProdFinEquiv (z.2.2.2, k)).val = PackRows.rank _ z * b + k.val
  simp only [PackRows.rank, PackRows.start, PackRows.port, Routing.offset, ← sum_mul,
    show (finProdFinEquiv (z.2.2.2, k)).val = k.val + b * z.2.2.2.val from rfl, Nat.add_mul]
  ac_rfl

private def listPorts (l : PackRows.Inventory H m d) :
    PackRows.Endpoints l ≃ (Σ z : Fin H × Fin d, PackRows.Blocks (PackRows.port (l z.1) z.2)) where
  toFun p := ⟨(p.1, p.2.2.1), p.2.1, p.2.2.2⟩
  invFun p := ⟨p.1.1, p.2.1, p.1.2, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- If names sharing a holder always use different channels, the
port ordinals enumerate exactly the stacks of one name at that holder. -/
theorem port_ordinals
    (sep : ∀ i j a b, (loc i a).1 = (loc j b).1 → χ (loc i a).1 i = χ (loc j b).1 j → i = j) (i : J) (v : Fin H) :
    let A := Fiber (fun s => (loc i s).1) v
    ∃ rank : A ≃ Fin (Fintype.card A), ∀ s : A,
      (rank s).val = PackRows.rank _ (stack loc χ (i, s.val)) := by
  intro A
  by_cases hn : Nonempty A
  swap
  · exact ⟨Fintype.equivFin _, fun s => (hn ⟨s⟩).elim⟩
  let n (z : Fin H × Fin d) := ∑ t, counts loc χ z.1 t z.2
  let e : J × S ≃ Σ z, Fin (n z) := ((stack loc χ).trans (listPorts _)).trans
    (Equiv.sigmaCongrRight fun _ => PackRows.order _)
  have key (s : A) : (e (i, s.val)).1 = (v, χ v i) :=
    Prod.ext s.property (congrArg (fun a => χ a i) s.property)
  let pos (s : A) : Fin (n (v, χ v i)) := (e (i, s.val)).2.cast (congrArg n (key s))
  have hi : Function.Injective pos := by
    intro s t h
    have he := (key s).trans (key t).symm
    have eq : e (i, s.val) = e (i, t.val) :=
      Sigma.ext he ((Fin.heq_ext_iff (congrArg n he)).mpr (congrArg Fin.val h))
    exact Subtype.ext (congrArg Prod.snd (e.injective eq))
  have hr : Function.Surjective pos := by
    intro k
    obtain ⟨⟨j, t⟩, he⟩ := e.surjective ⟨(v, χ v i), k⟩
    have hv : (loc j t).1 = v := congrArg (fun a => a.1.1) he
    have hc : χ (loc j t).1 j = χ v i := congrArg (fun a => a.1.2) he
    have := sep j i t hn.some.val (hv.trans hn.some.property.symm)
      (hc.trans (congrArg (fun a => χ a i) hn.some.property.symm))
    subst j
    exact ⟨⟨t, hv⟩, Fin.ext (congrArg (fun z => z.2.val) he)⟩
  let f := Equiv.ofBijective pos ⟨hi, hr⟩
  have hc : n (v, χ v i) = Fintype.card A := by simpa using Fintype.card_congr f.symm
  exact ⟨f.trans (finCongr hc), fun _ => rfl⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end

/-! # Aligning exterior stacks with the port rows of a contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Finset PackRows
open scoped Classical

variable {J S C : Type} [Fintype J] [Fintype S] [Fintype C] {H m d b q u v K : ℕ}

private theorem split (n q b : ℕ) (hq : 0 < q) (k : Fin b) :
    (n * b + k.val) / (q * b) = n / q ∧ (n * b + k.val) % (q * b) = n % q * b + k.val := by
  have hb : 0 < b := by have := k.isLt; omega
  have lo : n % q * b + k.val < q * b := calc
    _ < n % q * b + b := Nat.add_lt_add_left k.isLt _
    _ = (n % q + 1) * b := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mod_lt n hq)
  have he : n * b + k.val = (q * b) * (n / q) + (n % q * b + k.val) := by
    rw [← Nat.add_assoc, Nat.mul_right_comm q b, ← Nat.add_mul, Nat.div_add_mod]
  rw [he, Nat.mul_add_div (Nat.mul_pos hq hb), Nat.div_eq_of_lt lo, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt lo]
  exact ⟨rfl, rfl⟩

private theorem aligned (holder : S → Fin H) (ordinal : S → ℕ)
    (rank : ∀ i, Fiber holder i ≃ Fin (Fintype.card (Fiber holder i)))
    (hr : ∀ i s, (rank i s).val = ordinal s.val)
    (hq : 0 < q) (hp : (univ.image holder).card * q ≤ Fintype.card S)
    (hsize : Fintype.card C * q = 2 * Fintype.card S) :
    ∃ e : S ⊕ S ≃ C × Fin q,
      (∀ s, (e (.inl s)).2.val = ordinal s % q) ∧
      (∀ s t, (e (.inl s)).1 = (e (.inl t)).1 ↔
        holder s = holder t ∧ ordinal s / q = ordinal t / q) := by
  obtain ⟨e, r, he⟩ := group_order holder C q hq hp hsize rank
  have pos (s : S) := he (holder s) ⟨s, rfl⟩
  refine ⟨e.order, fun s => ?_, fun s t => ?_⟩
  · rw [pos s]
    change (rank _ _).val % q = _
    rw [hr]
  · constructor
    · intro h
      refine ⟨e.same _ _ h, ?_⟩
      rw [pos s, pos t] at h
      have h' := congrArg (fun z => z.2.val) (r.injective h)
      change (rank _ _).val / q = (rank _ _).val / q at h'
      simpa only [hr] using h'
    · rintro ⟨hh, ho⟩
      rw [he (holder t) ⟨s, hh⟩, pos t]
      apply congrArg (fun j => r ⟨holder t, j⟩)
      apply Fin.ext
      change (rank _ _).val / q = (rank _ _).val / q
      simpa only [hr] using ho

variable (loc : J → S → Fin H × Fin m) (χ : Fin H → J → Fin d) {d' : ℕ}

/-- For the prescribed port order, all active exterior rows pair
one-to-one with their inside rows. The within-row offset is unchanged. -/
theorem pack_ports (sep : ∀ i j a b, (loc i a).1 = (loc j b).1 → χ (loc i a).1 i = χ (loc j b).1 j → i = j)
    (hq : 0 < q) (cap : ∀ i, (univ.image fun s => (loc i s).1).card * q ≤ Fintype.card S)
    (hsize : Fintype.card C * q = 2 * Fintype.card S) (width : q * b = 2 * u)
    (l : Inventory H m d') (L : PackRows.Layout (append l (lengths loc χ b)) u v K) :
    let slot := fun i s k => L.portSlots (extendR l _ (point loc χ b ((i, s), k)))
    ∃ e : J → S ⊕ S ≃ C × Fin q,
      (∀ i s k, (slot i s k).2.val = (e i (.inl s)).2.val * b + k.val) ∧
      (∀ i j s t k a, (slot i s k).1 = (slot j t a).1 ↔
        i = j ∧ (e i (.inl s)).1 = (e j (.inl t)).1) := by
  intro slot
  let ord i s := rank _ (stack loc χ (i, s))
  choose f hf using port_ordinals loc χ sep
  choose e epos erow using fun i => aligned (fun s => (loc i s).1) (ord i)
    (f i) (hf i) hq (cap i) hsize
  refine ⟨e, ?_, ?_⟩
  · intro i s k
    rw [epos]
    unfold slot
    rw [L.ordinal, rank_extendR, point_rank, ← width]
    exact (split (ord i s) q b hq k).2
  · intro i j s t k a
    unfold slot
    rw [L.row_eq, and_assoc, rank_extendR, rank_extendR, point_rank, point_rank, ← width,
      (split _ q b hq k).1, (split _ q b hq a).1]
    change ((loc i s).1 = (loc j t).1 ∧ Fin.natAdd d' (χ (loc i s).1 i) = Fin.natAdd d' (χ (loc j t).1 j) ∧
      ord i s / q = ord j t / q) ↔ _
    constructor
    · rintro ⟨hm, hh, ho⟩
      have := sep i j s t hm ((Fin.natAddEmb d').injective hh)
      subst j
      exact ⟨rfl, (erow i s t).mpr ⟨hm, ho⟩⟩
    · rintro ⟨rfl, hh⟩
      obtain ⟨hm, ho⟩ := (erow i s t).mp hh
      exact ⟨hm, by rw [hm], ho⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end

section
/-!
# Arity of the short exterior sorts

Stack addresses grow at most quadratically in the beat count. The
payload covers the address, and the logarithm of the entire table
arity fits both caps for a short sorting vertex.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Filter

theorem limits (v B : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ h p w : ℕ, h ≤ v * j ^ 2 → 2 ^ j ≤ p → p ≤ w → w ≤ 2 ^ (2 * B * j) →
      h + 4 ≤ p ∧ 2 * 2 ^ (h + 2) * (h + 1 + p + 2) ≤ min (2 ^ ((Nat.clog 2 w) ^ 3)) (2 ^ (w / 2)) := by
  let k := v + 4 + 2 * B
  filter_upwards [eventually_ge_atTop (2 * k), replication (by norm_num : (0 : ℝ) < 1) (2 * k)]
    with j hj hr h p w hh hp hw he
  have hj' : 1 ≤ j := by unfold k at hj; omega
  have hq : h + 4 + 2 * B * j ≤ k * j ^ 2 := by
    unfold k
    nlinarith only [hh, Nat.mul_le_mul_left (2 * B) (show j ≤ j ^ 2 by nlinarith),
      show 1 ≤ j ^ 2 by nlinarith]
  have hf : 2 * (k * j ^ 2) ≤ 2 ^ j := by
    have hm := hr (2 ^ j) le_rfl
    rw [Real.rpow_one] at hm
    have hn : (2 : ℕ) ^ (2 * k * j ^ 2) ≤ 2 ^ (2 ^ j) := by exact_mod_cast hm
    simpa [mul_assoc] using (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hn
  have hl : h + 4 ≤ p := by omega
  have hn : j ≤ Nat.clog 2 w :=
    (Nat.clog_pow 2 j (by decide)).symm.le.trans (Nat.clog_mono_right 2 (hp.trans hw))
  have htop : k * j ^ 2 ≤ (Nat.clog 2 w) ^ 3 := calc
    _ ≤ j * j ^ 2 := Nat.mul_le_mul_right _ (by omega)
    _ = j ^ 3 := by ring
    _ ≤ _ := Nat.pow_le_pow_left hn _
  refine ⟨hl, le_trans ?_ (le_min (Nat.pow_le_pow_right (by decide) (hq.trans htop))
    (Nat.pow_le_pow_right (by decide) (show h + 4 + 2 * B * j ≤ w / 2 by omega)))⟩
  calc
    _ ≤ 2 * 2 ^ (h + 2) * (2 * 2 ^ (2 * B * j)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by simp only [pow_add]; ring

/-- Apply both caps to the height and bundle width chosen by the batch recipe. -/
theorem recipe_limits {F : Type} [Field F] (P : Recipe F) (R Q B : ℕ) (hB : 6 + Q ≤ B) :
    ∀ᶠ j : ℕ in atTop, ∀ z w : ℕ, 2 ^ (B * j) ≤ w → w ≤ 2 ^ (2 * B * j) →
      16 * (2 ^ (Q * j) * P.b ^ j) * z ≤ w → w ≤ 32 * (2 ^ (Q * j) * P.b ^ j) * z →
      let h := P.blocks R j
      let p := P.b ^ j * z
      h + 4 ≤ p ∧ 2 * 2 ^ (h + 2) * (h + 1 + p + 2) ≤ min (2 ^ ((Nat.clog 2 w) ^ 3)) (2 ^ (w / 2)) := by
  filter_upwards [eventually_ge_atTop 1, limits (R + P.n * (P.H + 5)) B]
    with j hj ht z w hl hu hlo hup
  apply ht _ _ w _ _ _ hu
  · unfold Recipe.blocks Recipe.group
    nlinarith only [Nat.mul_le_mul_left R (show j ≤ j ^ 2 by nlinarith)]
  · have hd : 32 * 2 ^ (Q * j) * 2 ^ j ≤ 32 * 2 ^ (Q * j) * (P.b ^ j * z) := calc
      _ = 2 ^ (5 + Q * j + j) := by simp [pow_add]
      _ ≤ 2 ^ (B * j) := Nat.pow_le_pow_right (by decide) (by nlinarith)
      _ ≤ w := hl
      _ ≤ _ := by simpa [mul_assoc] using hup
    exact Nat.le_of_mul_le_mul_left hd (by positivity)
  · exact (Nat.le_mul_of_pos_left _ (by positivity : 0 < 16 * 2 ^ (Q * j))).trans
      (by simpa [mul_assoc] using hlo)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end

/-! # Exterior row capacity and channels on the reduced host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Finset Packing PackRows
open scoped Classical

namespace Exterior

theorem arity {J S : Type} [Fintype J] [Fintype S] {H m d : ℕ}
    (loc : J → S → Fin H × Fin m) (χ : Fin H → J → Fin d) (b : ℕ) (i : Fin H) (t : Fin m) :
    PackRows.arity (lengths loc χ b i) t =
      (univ.filter fun x : J × S => loc x.1 x.2 = (i, t)).card * b := by
  simp only [PackRows.arity, lengths_eq, ← sum_mul]
  congr 1
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  by_cases h : loc x.1 x.2 = (i, t) <;> simp [h]

end Exterior
namespace Stack.Holders

variable {F : Type} {x y : Wire} {h u a z K H m : ℕ} {G : Diagram F x y}
  {Q : HostNet F (fringe (copies x (2 ^ h * u)) (copies y (2 ^ h * u))) a z}
  (p : Holders G Q K) (f : Q.V ↪ Fin H) (g : Cell a ↪ Fin m)

def loc (i : Outer x y) (t : Cell h) := (f (p.core i t), g (p.block t))

/-- Assign local channels to exactly the exterior names reaching a site. -/
theorem channels (d : ℕ) (hd : 0 < d)
    (names : ∀ v, (univ.filter fun i : Outer x y => ∃ t, p.core i t = v).card ≤ d) :
    ∃ χ : Fin H → Outer x y → Fin d, ∀ i j s t,
      (p.loc f g i s).1 = (p.loc f g j t).1 →
      χ (p.loc f g i s).1 i = χ (p.loc f g j t).1 j → i = j := by
  let A (v : Fin H) := univ.filter fun i => ∃ t, (p.loc f g i t).1 = v
  have lim (v : Fin H) : (A v).card ≤ d := by
    by_cases hv : ∃ z, f z = v
    · obtain ⟨z, rfl⟩ := hv
      simpa [A, loc, f.injective.eq_iff] using names z
    · have no i t : (p.loc f g i t).1 ≠ v := fun he => hv ⟨_, he⟩
      simp [A, no]
  let code (v : Fin H) : ↥(A v) ↪ Fin d :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using lim v))
  let χ (v : Fin H) (i : Outer x y) := if hi : i ∈ A v then code v ⟨i, hi⟩ else ⟨0, hd⟩
  refine ⟨χ, fun i j s t eq he => ?_⟩
  have hi : i ∈ A (p.loc f g j t).1 := mem_filter.mpr ⟨mem_univ _, s, eq⟩
  have hj : j ∈ A (p.loc f g j t).1 := mem_filter.mpr ⟨mem_univ _, t, rfl⟩
  rw [eq] at he
  simp only [χ, dite_eq_left hi, dite_eq_left hj] at he
  exact congrArg Subtype.val ((code _).injective he)

/-- Relative to one original name, the tail blocks pay for the final
partial row at every holder. -/
theorem capacity (k q : ℕ) (ha : a ≤ h) (hK : k * q ≤ 2 ^ a)
    (reach : ∀ i, (univ.image (p.core i)).card ≤ k * 2 ^ (h - a)) (i : Outer x y) :
    (univ.image fun t => (p.loc f g i t).1).card * q ≤ Fintype.card (Cell h) := by
  have hc : (univ.image fun t => (p.loc f g i t).1).card ≤ (univ.image (p.core i)).card := by
    change (univ.image (f ∘ p.core i)).card ≤ _
    rw [← image_image]
    exact card_image_le
  calc
    _ ≤ (k * 2 ^ (h - a)) * q := Nat.mul_le_mul_right _ (hc.trans (reach i))
    _ = k * q * 2 ^ (h - a) := by ring
    _ ≤ 2 ^ a * 2 ^ (h - a) := Nat.mul_le_mul_right _ hK
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le ha, card_cell]

/-- The external port inventory counts all exposed bits, in units of
final bundle width. -/
theorem load_eq {d b : ℕ} (χ : Fin H → Outer x y → Fin d) (hu : u = b * z) (v : Q.V) (t : Cell a) :
    (PackRows.arity (Exterior.lengths (p.loc f g) χ b (f v)) (g t) : ℝ) * z =
      (Q.tetherLoad (v, t) : ℝ) := by
  rw [HostNet.tetherLoad, port_load]
  rw [Exterior.arity, Nat.cast_mul, mul_assoc, ← Nat.cast_mul, ← hu, push,
    ← (bit h u x y).sum_comp]
  rw [Fintype.sum_prod_type, sum_comm]
  simp_rw [Fintype.sum_prod_type, Function.comp_apply, p.tip, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← sum_boole, sum_mul, Fintype.sum_prod_type]
  simp only [loc, Prod.mk.injEq, f.injective.eq_iff, g.injective.eq_iff, mul_comm]

end Stack.Holders
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Naming the finest exterior bundles by their source stack -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly Packing

variable {F : Type} [Field F] {x y : Wire} {h z c a K : ℕ}

namespace Stack

abbrev strips (h c z : ℕ) (x y : Wire) :
    ((Outer x y × Cell h) × Fin c) × Fin z ≃
    Outer (copies x (2 ^ h * (c * z))) (copies y (2 ^ h * (c * z))) :=
  (Equiv.prodAssoc _ _ _).trans <| ((Equiv.refl _).prodCongr finProdFinEquiv).trans <|
    (Equiv.prodAssoc _ _ _).trans <| (Equiv.prodComm _ _).trans (bit h (c * z) x y)

end Stack

namespace Exterior

variable {S : Scheme F} {r : S.format.obj} {D : Diagram F x y}

theorem boundary_owner (p : S.Presentation r D) (i : Stack.Outer x y) :
    (p.boundary i).val.1.1 = p.vertex (portEnd D i) := by
  have H (j : D.End) : (p.toSeating.ends j).1.1 = p.vertex (D.station j) := by
    obtain ⟨⟨k, t⟩, rfl⟩ := D.portEquiv.surjective j
    rw [p.toSeating.ends_at, D.station_port]
    rfl
  cases i with
  | inl i => exact H (.inl (.inl i))
  | inr i => exact H (.inr (.inl i))

variable {Q : HostNet F (Stack.fringe (copies x (2 ^ h * (c * z))) (copies y (2 ^ h * (c * z)))) a z}
  (p : S.Posting r Q) (L : Stack.Holders D Q K)

abbrev ports := (Stack.strips h c z x y).trans p.toPresentation.boundary

theorem ports_at (i : Stack.Outer x y) (b : Cell h) (j : Fin c) (t : Fin z) :
    (ports p (((i, b), j), t)).val.1.1 = (p.host (L.core i b), p.block (L.block b), 0) := by
  change (p.toPresentation.boundary (Stack.bit _ _ _ _ ((b, finProdFinEquiv (j, t)), i))).val.1.1 = _
  rw [boundary_owner, p.vertex_eq, L.tip]

theorem addresses {d : ℕ} (χ : Fin (2 ^ S.m) → Stack.Outer x y → Fin d)
    (hz : 0 < z) (he : Strips (ports p)) :
    let loc := L.loc p.host p.block
    ∃ e : outer S r z ≃ PackRows.Endpoints (lengths loc χ c),
      (∀ j, (e j).1 = j.val.1 ∧ (e j).2.1 = j.val.2.1) ∧
      ∀ i t, ports p (i, t) =
        toOuter (p.all_uniform (he.uniform hz)) (e.symm (point loc χ c i)) t := by
  intro loc
  obtain ⟨f, hf⟩ := Strips.segments (p.all_uniform (he.uniform hz)) he hz
  let e := f.symm.trans (point loc χ c)
  refine ⟨e, ?_, ?_⟩
  · intro j
    obtain ⟨⟨⟨i, b⟩, u⟩, rfl⟩ := f.surjective j
    rw [show e (f ((i, b), u)) = point loc χ c ((i, b), u) from
      congrArg (point loc χ c) (f.symm_apply_apply _)]
    have hv := ports_at p L i b u ⟨0, hz⟩
    rw [hf] at hv
    exact ⟨(congrArg Prod.fst hv).symm, (congrArg (fun a => a.2.1) hv).symm⟩
  · intro i t
    simp only [e, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    exact hf i t

end Exterior
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Exterior descriptors for a canonical port layout -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Finset
open scoped Classical

/-- The name belongs to the row. Only the stack address is needed for
each active payload inside that row. -/
structure Descriptor (J S I Q : Type) [Fintype I] (n : ℕ) where
  place : J × S ↪ I × Q
  owner : I → Option J
  addr : I → Q → Option S
  owner_eq : ∀ i j, owner i = some j ↔ ∃ s, (place (j, s)).1 = i
  addr_eq : ∀ i q j s, owner i = some j ∧ addr i q = some s ↔ place (j, s) = (i, q)
  bound : ∀ j, count owner j ≤ n

variable {J S I Q : Type} [Fintype I] {n : ℕ}

namespace Descriptor
variable (D : Descriptor J S I Q n)

theorem cover (j : J) (s : S) : ∃! a : I × Q, D.owner a.1 = some j ∧ D.addr a.1 a.2 = some s :=
  ⟨D.place (j, s), (D.addr_eq _ _ _ _).mpr rfl, fun _ h => ((D.addr_eq _ _ _ _).mp h).symm⟩

variable {X N K P : Type} (B : Input X I J S Q N K P) (x : X → Bool)

theorem valid (name : ∀ i, (B.header i).read x = (D.owner i).map B.names)
    (addr : ∀ i j, D.owner i = some j → ∀ q, decode (fun k => B.payload x i (q, .inl k)) =
      (D.addr i q).map B.keys) : B.Valid n x D.owner D.addr := by
  refine ⟨name, ?_, D.cover, D.bound⟩
  intro i j hi q
  have := addr i j hi q
  have h := congrArg (Option.map (fun f : K → Bool => Sum.elim f (fun p => B.payload x i (q, .inr p)))) this
  unfold stackRead
  unfold decode at h
  cases hb : B.payload x i (q, .inl none) <;> simp only [hb, Bool.false_eq_true, ite_false, ite_true,
    Option.map_none, Option.map_some, Option.map_map] at h ⊢ <;> exact h

theorem supplied : B.Supplied x D.owner D.addr ↔ ∀ j s t,
    B.payload x (D.place (j, s)).1 ((D.place (j, s)).2, .inr t) = x (B.source j s t) := by
  constructor
  · intro h j s t
    obtain ⟨hv, hs⟩ := (D.addr_eq _ _ j s).mpr (Prod.mk.eta (p := D.place (j, s))).symm
    exact congrFun (h _ _ _ _ hv hs) t
  · intro h i j k s hv hs
    have he := (D.addr_eq i k j s).mp ⟨hv, hs⟩
    funext t
    simpa only [he, Function.comp_apply] using h j s t

end Descriptor

private theorem descriptor [Fintype S] (loc : J × S ↪ I × Q)
    (same : ∀ a b, (loc a).1 = (loc b).1 → a.1 = b.1)
    (cap : ∀ j, (univ.image fun s => (loc (j, s)).1).card ≤ n) :
    ∃ D : Descriptor J S I Q n, D.place = loc := by
  let owner i := if h : ∃ x, (loc x).1 = i then some h.choose.1 else none
  let addr i q := if h : ∃ x, loc x = (i, q) then some h.choose.2 else none
  have ho i j : owner i = some j ↔ ∃ s, (loc (j, s)).1 = i := by
    unfold owner
    split
    · rename_i h
      refine ⟨fun he => ?_, fun ⟨s, hs⟩ => congrArg some (same _ _ (h.choose_spec.trans hs.symm))⟩
      rw [← Option.some.inj he]
      exact ⟨h.choose.2, h.choose_spec⟩
    · rename_i h
      exact iff_of_false (by simp) (fun ⟨s, hs⟩ => h ⟨(j, s), hs⟩)
  refine ⟨⟨loc, owner, addr, ho, ?_, ?_⟩, rfl⟩
  · intro i q j s
    constructor
    · rintro ⟨ho', ha⟩
      unfold addr at ha
      split at ha
      · rename_i h
        obtain ⟨t, ht⟩ := (ho i j).mp ho'
        have hj := same h.choose (j, t) ((congrArg Prod.fst h.choose_spec).trans ht.symm)
        have eq : h.choose = (j, s) := Prod.ext hj (Option.some.inj ha)
        exact eq ▸ h.choose_spec
      · cases ha
    · intro he
      have h : ∃ x, loc x = (i, q) := ⟨_, he⟩
      exact ⟨(ho i j).mpr ⟨s, congrArg Prod.fst he⟩,
        by simp only [addr, dite_eq_left h, loc.injective (h.choose_spec.trans he.symm)]⟩
  · intro j
    rw [count, sum_boole, Nat.cast_id]
    refine le_trans (card_le_card ?_) (cap j)
    intro i hi
    obtain ⟨s, hs⟩ := (ho i j).mp (mem_filter.mp hi).2
    exact mem_image.mpr ⟨s, mem_univ _, hs⟩

variable [Fintype J] [Fintype S] {H m d b q u v K d' : ℕ}
  (loc : J → S → Fin H × Fin m) (χ : Fin H → J → Fin d)

/-- Construct a descriptor for the rows that actually carry exterior
stacks. The output agreement is stated at every finest bundle. -/
theorem make_descriptor (sep : ∀ i j a b, (loc i a).1 = (loc j b).1 →
      χ (loc i a).1 i = χ (loc j b).1 j → i = j)
    (hb : 0 < b) (hq : 0 < q)
    (cap : ∀ i, (univ.image fun s => (loc i s).1).card * q ≤ Fintype.card S)
    (size : n * q = 2 * Fintype.card S) (width : q * b = 2 * u)
    (l : PackRows.Inventory H m d') (L : PackRows.Layout (PackRows.append l (lengths loc χ b)) u v K) :
    let slot := fun i s k => L.portSlots (PackRows.extendR l _ (point loc χ b ((i, s), k)))
    ∃ D : Descriptor J S (PackRows.Address v K) (Fin q) n,
      ∀ i s k, (slot i s k).1 = (D.place (i, s)).1 ∧
        (slot i s k).2.val = (D.place (i, s)).2.val * b + k.val := by
  intro slot
  obtain ⟨e, he, hr⟩ := pack_ports (C := Fin n) loc χ sep hq cap (by simpa using size) width l L
  let k : Fin b := ⟨0, hb⟩
  let f (z : J × S) := ((slot z.1 z.2 k).1, (e z.1 (.inl z.2)).2)
  have same (x y : J × S) (h : (f x).1 = (f y).1) : x.1 = y.1 := ((hr _ _ _ _ _ _).mp h).1
  have inj : Function.Injective f := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    obtain ⟨h, h'⟩ := Prod.mk.inj h
    obtain ⟨rfl, r⟩ := (hr i j s t k k).mp h
    exact Prod.ext rfl (Sum.inl.inj ((e i).injective (Prod.ext r h')))
  let pos := Function.Embedding.mk f inj
  have capacity (i : J) : (univ.image fun s => (pos (i, s)).1).card ≤ n := by
    let A := univ.image fun s => (pos (i, s)).1
    have rep (a : A) : ∃ s, (slot i s k).1 = a.val := by
      obtain ⟨s, _, hs⟩ := mem_image.mp a.property
      exact ⟨s, hs⟩
    choose witness hw using rep
    let g (a : A) := (e i (.inl (witness a))).1
    have hg : Function.Injective g := by
      intro a b hab
      exact Subtype.ext ((hw a).symm.trans (((hr _ _ _ _ k k).mpr ⟨rfl, hab⟩).trans (hw b)))
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective g hg
  obtain ⟨D, hD⟩ := descriptor pos same (by convert! capacity using 1; congr! 3)
  refine ⟨D, fun i s z => ?_⟩
  rw [hD]
  exact ⟨(hr i i s s z k).mpr ⟨rfl, rfl⟩, he i s z⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end
