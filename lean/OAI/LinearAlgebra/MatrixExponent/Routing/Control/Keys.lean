import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Decor
import OAI.LinearAlgebra.MatrixExponent.Routing.Packets
import OAI.LinearAlgebra.MatrixExponent.Protocol.Frame
import OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
import OAI.LinearAlgebra.MatrixExponent.Protocol.Alignment

/-!
# Ordering disjoint blocks by local keys

Only the keys of nonempty blocks need to be distinct. In particular
unused centers do not need to be globally ordered.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Finset
variable {J : Type} [Fintype J] (v key : J → ℕ)

def offset (j : J) := ∑ i ∈ univ.filter (fun i => key i < key j), v i

private theorem offset_le (j : J) (A : Finset J) (hA : ∀ i, key i ≤ key j → i ∈ A) :
    offset v key j + v j ≤ ∑ i ∈ A, v i := by
  classical
  let S := univ.filter fun i => key i < key j
  have he : j ∉ S := by simp [S]
  have hs : insert j S ⊆ A := insert_subset (hA j le_rfl)
    (fun i hi => hA i (mem_filter.mp hi).2.le)
  have h := sum_le_sum_of_subset (f := v) hs
  rw [sum_insert he, add_comm] at h
  exact h

def offsetIndex (u : Σ j, Fin (v j)) : Fin (∑ i, v i) :=
  ⟨offset v key u.1 + u.2.val,
    (Nat.add_lt_add_left u.2.isLt _).trans_le (offset_le v key u.1 univ (fun i _ => mem_univ i))⟩

theorem offset_lt {u z : Σ j, Fin (v j)} (h : key u.1 < key z.1) :
    offsetIndex v key u < offsetIndex v key z := by
  have e : offset v key u.1 + v u.1 ≤ offset v key z.1 :=
    offset_le v key _ _ fun i hi => mem_filter.mpr ⟨mem_univ _, hi.trans_lt h⟩
  exact ((Nat.add_lt_add_left u.2.isLt _).trans_le e).trans_le (Nat.le_add_right _ _)

def Ordered : Prop := ∀ i j, v i ≠ 0 → v j ≠ 0 → key i = key j → i = j

def pack (h : Ordered v key) : (Σ j, Fin (v j)) ≃ Fin (∑ i, v i) :=
  Equiv.ofBijective (offsetIndex v key) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp⟩
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    have hk : key i = key j := by
      rcases lt_trichotomy (key i) (key j) with h | h | h
      · exact ((offset_lt v key (u := ⟨i, x⟩) (z := ⟨j, y⟩) h).ne he).elim
      · exact h
      · exact ((offset_lt v key (u := ⟨j, y⟩) (z := ⟨i, x⟩) h).ne he.symm).elim
    have hij := h i j (Nat.ne_of_gt (Nat.zero_lt_of_lt x.isLt))
      (Nat.ne_of_gt (Nat.zero_lt_of_lt y.isLt)) hk
    subst j
    exact congrArg (fun t : Fin (v i) => (⟨i, t⟩ : Σ j, Fin (v j)))
      (Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))))

theorem pack_val (h : Ordered v key) (j : J) (i : Fin (v j)) :
    (pack v key h ⟨j, i⟩).val = offset v key j + i := rfl

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Decor
open scoped Classical

variable {G : Type} [Group G] {q : ℕ} {X : Type*}

def shift (a : G) (r : Decor G q) : Decor G q := ⟨r.toRoot.shift a, r.mark⟩

theorem Local.shift {f : Decor G q → X} (h : Local f) (a : G) : Local (f ∘ Decor.shift a) := by
  obtain ⟨E, hE⟩ := h
  refine ⟨E.image (· * a), fun r s he hm => hE _ _ ?_ ?_⟩
  · intro x hx y hy
    have hh := he _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)
    simp only [Root.see, Root.label, Decor.shift, Root.shift, mul_smul] at hh ⊢
    exact hh
  · intro x hx
    have hh := hm _ (Finset.mem_image_of_mem _ hx)
    simp only [Root.label, Decor.shift, Root.shift, mul_smul] at hh ⊢
    exact hh

end OAI.LinearAlgebra.MatrixExponent.Routing.Decor
end

/-!
# Addressing overlapping action balls

Two centers are neighbors precisely when they differ by a product
of two radius words, one inverted. A fixed list enumerates these
products, and its first occurrence of each label is used.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open scoped Classical Pointwise

variable {G I : Type} [Group G] [MulAction G I] (H : Finset G) (r : ℕ)

namespace Root

variable {t : ℕ} (w : Fin (2 ^ t) → G)

def first (x : Root G) := Finset.univ.filter fun j : Fin (2 ^ t) =>
  ∀ l, x.see (w l) (w j) = true → j ≤ l

theorem local_first : Local (first w) := by
  have h : Local (fun x : Root G => fun j l => x.see (w l) (w j)) :=
    local_pi fun j => local_pi fun l => local_see _ _
  exact h.map (fun f => Finset.univ.filter fun j => ∀ l, f j l = true → j ≤ l)

theorem first_char (x : Root G) (j : Fin (2 ^ t)) :
    j ∈ x.first w ↔ ∀ l, x.label (w l) = x.label (w j) → j ≤ l := by
  simp only [first, Finset.mem_filter, Finset.mem_univ, true_and, see, decide_eq_true_eq]

theorem first_distinct (x : Root G) : Set.InjOn (fun j => x.label (w j)) (x.first w) :=
  fun _ hi _ hj he => le_antisymm ((first_char _ _ _).mp hi _ he.symm)
    ((first_char _ _ _).mp hj _ he)

theorem first_rep (x : Root G) (j : Fin (2 ^ t)) :
    ∃ i ∈ x.first w, x.label (w i) = x.label (w j) := by
  let u := Finset.univ.filter fun l => x.label (w l) = x.label (w j)
  have hu : u.Nonempty := ⟨j, by simp [u]⟩
  have hj := (Finset.mem_filter.mp (u.min'_mem hu)).2
  exact ⟨u.min' hu, (first_char _ _ _).mpr fun l hl =>
    u.min'_le l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl.trans hj⟩), hj⟩

end Root

def offsets := H ^ r * (H ^ r)⁻¹

theorem exists_offsets (hH : 1 ∈ H) :
    ∃ t : ℕ, ∃ w : Fin (2 ^ t) → G, Set.range w = offsets H r := by
  let D := offsets H r
  have hD : D.Nonempty := by
    have h := Finset.one_mem_pow (n := r) hH
    exact ⟨_, Finset.mul_mem_mul h (Finset.inv_mem_inv h)⟩
  let _ : Nonempty D := hD.to_subtype
  let f := D.equivFin.toEmbedding.trans (Fin.castLEEmb Nat.lt_two_pow_self.le)
  refine ⟨D.card, fun j => (Function.invFun f j).val, Set.ext fun x => ?_⟩
  exact ⟨fun ⟨_, he⟩ => he ▸ (Function.invFun f _).property,
    fun h => ⟨f ⟨x, h⟩, congrArg Subtype.val (Function.leftInverse_invFun f.injective _)⟩⟩

variable [Fintype I] (hH : 1 ∈ H) (g : G) (hg : g ∈ H ^ r)

omit [Fintype I] in
theorem market_support (i : I) : (market H hH r g hg).support i = ball H r i := by
  ext j
  rw [Market.support, Finset.mem_map]
  constructor
  · rintro ⟨t, _, rfl⟩
    exact (labels H hH r g hg i t).property
  · intro h
    obtain ⟨t, ht⟩ := (labels H hH r g hg i).surjective ⟨j, h⟩
    exact ⟨t, Finset.mem_univ _, congrArg Subtype.val ht⟩

variable [DecidableEq I]

theorem market_neighbors (i j : I) :
    j ∈ (market H hH r g hg).neighbors i ↔ ∃ a ∈ offsets H r, a • i = j := by
  simp only [Market.neighbors, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    market_support, ball, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨a, ha, rfl⟩, b, hb, he⟩
    exact ⟨b * a⁻¹, Finset.mul_mem_mul hb (Finset.inv_mem_inv ha),
      by rw [mul_smul, ← he, smul_inv_smul]⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_mul.mp ha
    exact ⟨c • i, ⟨c⁻¹, by simpa using hc, by rw [inv_inv]⟩,
      b, hb, by rw [mul_smul, inv_smul_smul]⟩

def marketPorts {t : ℕ} (w : Fin (2 ^ t) → G) (hw : Set.range w = offsets H r) :
    (market (I := I) H hH r g hg).Ports t where
  addr j i := w j • i
  use i := Root.first w ⟨I, i⟩
  distinct i := Root.first_distinct w ⟨I, i⟩
  image i := by
    ext j
    rw [market_neighbors, Finset.mem_image]
    constructor
    · rintro ⟨l, _, he⟩
      exact ⟨w l, Set.ext_iff.mp hw _ |>.mp ⟨l, rfl⟩, he⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨l, rfl⟩ := (Set.ext_iff.mp hw _).mpr ha
      exact Root.first_rep w ⟨I, i⟩ l

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# The control metadata uses only a bounded orbit diagram

In particular, comparing two request tuples does not require forming
an array indexed by every possible tuple of global labels.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral
open scoped Classical Pointwise

variable {G K S : Type} [Group G] [Field K] [Fintype S] [DecidableEq S]
  (A : Finset (Tensor K S)) (H : Finset G) (r : ℕ) (hH : 1 ∈ H) (g : G) (hg : g ∈ H ^ r)
  {t : ℕ} (w : Fin (2 ^ t) → G)

abbrev Mask (N t : ℕ) (A : Finset (Tensor K S)) := Fin (2 ^ t) → Key N A → Key N A → Bool

private def agreeSlots (a b : Board H r) (same : Bool) (names : ↥(H ^ r) → ↥(H ^ r) → Bool) :
    a.1.Req A → b.1.Req A → Prop
  | none, none => same = true
  | some (x, i), some (y, j) => i = j ∧ ∀ s, names (a.2 (x s)) (b.2 (y s)) = true
  | _, _ => False

private def linksAt (a b : Board H r) (use : Prop) (same : Bool)
    (names : ↥(H ^ r) → ↥(H ^ r) → Bool) (x y : Key (H ^ r).card A) : Bool :=
  decide (use ∧ ∃ u v, x = ⟨a.1, u⟩ ∧ y = ⟨b.1, v⟩ ∧ agreeSlots A H r a b same names u v)

def observations (x : Root G) : Mask (H ^ r).card t A := fun j =>
  linksAt A H r (Board.choose H r hH g hg x) (Board.choose H r hH g hg (x.shift (w j)))
    (j ∈ x.first w) (x.see 1 (w j)) (fun u v => x.see u.val⁻¹ (v.val⁻¹ * w j))

theorem local_observations : Root.Local (observations A H r hH g hg w) := by
  apply Root.local_pi
  intro j
  have he : Root.Local (fun x : Root G => fun u v : ↥(H ^ r) => x.see u.val⁻¹ (v.val⁻¹ * w j)) :=
    Root.local_pi fun _ => Root.local_pi fun _ => Root.local_see _ _
  have h := Board.local_choose H r hH g hg
  exact ((h.pair (h.shift (w j))).pair
    ((Root.local_first w).pair ((Root.local_see 1 (w j)).pair he))).map
      fun y => linksAt A H r y.1.1 y.1.2 (j ∈ y.2.1) y.2.2.1 y.2.2.2

variable {I : Type} [MulAction G I] [Fintype I] [DecidableEq I] (hw : Set.range w = offsets H r)

theorem observations_eq (i : I) :
    observations A H r hH g hg w ⟨I, i⟩ =
      (market H hH r g hg).mask A (marketPorts H r hH g hg w hw) i := by
  let b := market (I := I) H hH r g hg
  let x : Root G := ⟨I, i⟩
  let p := board H hH r g hg i
  funext j l n
  let y := w j • i
  let q := board H hH r g hg y
  let names := fun u v : ↥(H ^ r) => x.see u.val⁻¹ (v.val⁻¹ * w j)
  have he (u : p.1.Req A) (v : q.1.Req A) :
      agreeSlots A H r p q (x.see 1 (w j)) names u v ↔ b.request A i u = b.request A y v := by
    erw [b.request_eq]
    rcases u with _ | ⟨u, k⟩ <;> rcases v with _ | ⟨v, k'⟩
    · simp only [agreeSlots, Root.see, decide_eq_true_eq]
      change 1 • i = y ↔ i = y
      rw [one_smul]
    · rfl
    · rfl
    · simp only [agreeSlots, names, Root.see, decide_eq_true_eq]
      change (k = k' ∧ ∀ s, p.word (u s) • i = (q.word (v s) * w j) • i) ↔
        (k = k' ∧ ∀ s, p.word (u s) • i = q.word (v s) • (w j • i))
      simp only [mul_smul]
  apply Bool.eq_iff_iff.mpr
  simp only [observations, linksAt, Market.mask, decide_eq_true_eq]
  change (j ∈ x.first w ∧ ∃ u v, l = ⟨p.1, u⟩ ∧ n = ⟨q.1, v⟩ ∧
    agreeSlots A H r p q (x.see 1 (w j)) names u v) ↔ _
  simp only [he]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# A bounded local transcript of a whole schedule

A transcript records the initial stocks, the successive decisions
and the stocks after each round. The initial state and the local
update tests characterize the image of the branch encoding.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral
open scoped Classical

variable {K S I : Type} [Field K] [Fintype S] [DecidableEq S]
  [Fintype I] [DecidableEq I] {N M : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)}

namespace Atlas
variable (a : Atlas N A M ρ) (m R : ℕ) (s : Shape N)

abbrev Timeline : ℕ → Type 1
  | 0 => ULift (s.Req A → Fin (R + 1))
  | k + 1 => (s.Req A → Fin (R + 1)) × a.Record s m × Timeline k

instance finiteTimeline (k : ℕ) : Finite (a.Timeline m R s k) := by
  have _ : Finite (a.Record s m) := inferInstance
  induction k with
  | zero => unfold Timeline; infer_instance
  | succ k ih => unfold Timeline; infer_instance

def start : (k : ℕ) → a.Timeline m R s k → s.Req A → Fin (R + 1)
  | 0, t => t.down
  | _ + 1, t => t.1

end Atlas

namespace Market

variable (b : Market I N) (a : Atlas N A M ρ) (μ d m R : ℕ)

abbrev Path := Protocol.Branch (b.payload A) (b.decision a μ d m)
abbrev Logset (k : ℕ) := ∀ i, a.Timeline m R (b.code i) k

def initialLog {k : ℕ} (x : b.Logset a m R k) (i : I) (j : (b.code i).Req A) :=
  (a.start m R _ k (x i) j).val

def checkedLog : (k : ℕ) → b.Logset a m R k → Prop
  | 0, _ => True
  | k + 1, x =>
    let y := fun i => (x i).2.2
    b.Checks a μ d m (b.initialLog a m R x) (fun i => (x i).2.1) (b.initialLog a m R y) ∧
      checkedLog k y

def project (z : b.Request A → ℕ) (i : I) (j : (b.code i).Req A) : Fin (R + 1) :=
  ⟨min (b.localStock A z i j) R, Nat.lt_succ_of_le (min_le_right _ _)⟩

def encodeLog : (k : ℕ) → (z : b.Request A → ℕ) → b.Path a μ d m k z → b.Logset a m R k
  | 0, z, _ => fun i => ⟨b.project R z i⟩
  | k + 1, z, u => fun i =>
    (b.project R z i, b.record a (b.stockPrice (M := M) μ d z) m u.1 i,
      encodeLog k (b.after a μ d m z u.1) u.2 i)

theorem encodeLog_injective (k : ℕ) (z : b.Request A → ℕ) :
    Function.Injective (b.encodeLog a μ d m R k z) := by
  induction k generalizing z with
  | zero => exact fun u v _ => Subsingleton.elim (α := Unit) u v
  | succ k ih =>
    rintro ⟨u, v⟩ ⟨u', v'⟩ he
    have hu : u = u' := b.record_injective a (b.stockPrice (M := M) μ d z) m
      (funext fun i => congrArg (fun x => x.2.1) (congrFun he i))
    subst u'
    have hv : v = v' := ih _ (funext fun i => congrArg (fun x => x.2.2) (congrFun he i))
    rw [hv]

variable [Nonempty S]

def rateBound := N * (2 * a.capacity * m) + 1

theorem encodeLog_spec (room : a.Room m) (hm : 1 ≤ M) (hd : d ≤ M)
    (k : ℕ) (z : b.Request A → ℕ) (hz : ∀ i, z i + k * rateBound a m ≤ R)
    (x : b.Logset a m R k) :
    (b.initialLog a m R x = b.localStock A z ∧ b.checkedLog a μ d m R k x) ↔
      ∃ u, b.encodeLog a μ d m R k z u = x := by
  have init (k : ℕ) (z : b.Request A → ℕ) (hz : ∀ i, z i + k * rateBound a m ≤ R)
      (u : b.Path a μ d m k z) :
      b.initialLog a m R (b.encodeLog a μ d m R k z u) = b.localStock A z := by
    funext i j
    have h : b.localStock A z i j ≤ R := (Nat.le_add_right _ _).trans (hz _)
    cases k <;> exact min_eq_left h
  induction k generalizing z with
  | zero =>
    constructor
    · rintro ⟨hx, _⟩
      refine ⟨(), funext fun i => ULift.ext _ _ (funext fun j => Fin.ext ?_)⟩
      exact congrFun (congrFun ((init _ z hz ()).trans hx.symm) i) j
    · rintro ⟨u, rfl⟩
      exact ⟨init _ _ hz u, trivial⟩
  | succ k ih =>
    have hb (u : (b.decision a μ d m z).choice) (i) :
        b.after a μ d m z u i + k * rateBound a m ≤ R := by
      have ht := b.after_bound a μ d m room hm hd z u i
      have hh := hz i
      rw [Nat.succ_mul] at hh
      unfold rateBound at hh ⊢
      omega
    constructor
    · rintro ⟨hx, hs, ht⟩
      rw [hx, b.checks_iff] at hs
      obtain ⟨u, ⟨hu, hu'⟩, _⟩ := hs
      obtain ⟨v, hv⟩ := (ih _ (hb u) _).mp ⟨hu', ht⟩
      let j : b.Path a μ d m (k + 1) z := ⟨u, v⟩
      refine ⟨j, funext fun i => Prod.ext ?_ (Prod.ext (congrFun hu i) (congrFun hv i))⟩
      exact funext fun y => Fin.ext (congrFun (congrFun ((init _ z hz j).trans hx.symm) i) y)
    · rintro ⟨u, rfl⟩
      have ht := (ih _ (hb u.1) _).mpr ⟨u.2, rfl⟩
      refine ⟨init _ _ hz u, ?_, ht.2⟩
      rw [init _ _ hz u, b.checks_iff]
      exact ⟨u.1, ⟨rfl, ht.1⟩, fun _ h => b.record_injective a _ m h.1⟩

end Market
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Local allocation of copies

A request is held at the same home by all its users. Their common
ordering is given by the list of neighbors at that home.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Market
open Spectral Finset
open scoped Classical

variable {I S K : Type} [Fintype I] [DecidableEq I] [Field K] [Fintype S] [DecidableEq S]
  {N t M : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)} {b : Market I N}

namespace Ports

variable (g : b.Ports t)

def key (x i : I) : ℕ := ∑ j ∈ g.use x, if g.addr j x = i then j.val else 0

theorem key_addr (x : I) (j : Fin (2 ^ t)) (hj : j ∈ g.use x) :
    g.key x (g.addr j x) = j.val := by
  unfold key
  rw [sum_eq_single j]
  · simp
  · intro k hk hne
    exact ite_eq_right (fun he => hne (g.distinct x hk hj he))
  · exact fun h => (h hj).elim

theorem key_inj (x : I) : Set.InjOn (g.key x) (b.neighbors x) := by
  rw [← g.image]
  intro i hi j hj hk
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hi
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hj
  rw [key_addr _ _ _ hu, key_addr _ _ _ hv] at hk
  rw [Fin.ext hk]

end Ports

variable (b) (a : Atlas N A M ρ) (p : b.Request A → ℝ) (m : ℕ)

theorem core_owner (j : b.active a p) (h : (b.localMove a p m j).choice) (e : b.Edge)
    (he : (b.localMove a p m j).core h e ≠ 0) : j.val = e.1 := by
  obtain ⟨i, hi⟩ := (b.moveAt a p j).trade_edge _ _ _ _ _ he
  rcases i with x | y
  · contradiction
  · exact congrArg Sigma.fst (Sum.inr.inj hi)

variable [Nonempty S] (g : b.Ports t)

def position (x : b.Request A) (j : b.active a p) : ℕ := g.key (b.home A x) j

theorem ordered (x : b.Request A) (v : b.active a p → ℕ)
    (hv : ∀ j, v j ≠ 0 → (b.localMove a p m j).affects x) :
    Ordered v (b.position a p g x) := by
  have hn (j : b.active a p) (hj : v j ≠ 0) : j.val ∈ b.neighbors (b.home A x) := by
    obtain ⟨k, hk⟩ := (b.moveAt a p j).flex_support _ _ _ (hv j hj)
    refine mem_biUnion.mpr ⟨b.home A x, mem_map.mpr ⟨_, mem_univ _, b.origin _⟩, ?_⟩
    exact mem_filter.mpr ⟨mem_univ _, b.home_mem A _ _ _ hk⟩
  exact fun i j hi hj he => Subtype.ext (g.key_inj _ (hn i hi) (hn j hj) he)

def allocation : Protocol.Allocation (b.localMove a p m) where
  take x := (pack (fun j => (b.localMove a p m j).take x) (b.position a p g x)
    (b.ordered a p m g x _ (fun _ h => .inl h))).symm
  put h x := (pack (fun j => (b.localMove a p m j).put (h j) x) (b.position a p g x)
    (b.ordered a p m g x _ (fun _ e => .inr ⟨_, e⟩))).symm
  core h e := (pack (fun j => (b.localMove a p m j).core (h j) e) (fun _ => 0)
    (fun i j hi hj _ => Subtype.ext
      ((b.core_owner a p m i _ _ hi).trans (b.core_owner a p m j _ _ hj).symm))).symm

end OAI.LinearAlgebra.MatrixExponent.Routing.Market
end

/-!
# Designating one supplier per request

Use the first center in the common order at the request's home.
After this choice the route itself is fixed by the local shape.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Finset
open scoped Classical
variable {K S I : Type} [Field K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  {N t : ℕ} (A : Finset (Tensor K S)) (d M : ℕ)

namespace Shape
variable (s : Shape N) (x : s.Req A)

def priceCap := if x = none then d else M

def route : s.2.edges → ℕ :=
  if h : s.2.Direct K (s.2.tensor A (.inl x)) (s.priceCap A d M x) then h.choose else 0

theorem route_spec (h : s.2.Direct K (s.2.tensor A (.inl x)) (s.priceCap A d M x)) :
    (∑ e, s.route A d M x e) ≤ s.priceCap A d M x ∧
    s.2.tensor A (.inl x) ≤ Stock.bundle (s.2.wire K) (s.route A d M x) := by
  rw [route, dite_eq_left h]
  exact h.choose_spec

end Shape

namespace Market
variable (b : Market I N)

omit [Fintype I] [DecidableEq I] in
theorem local_route (h : b.ready A d) (hc : UniformCap N A M)
    (i : I) (x : (b.code i).Req A) :
    (b.shape i).Direct K ((b.shape i).tensor A (.inl x)) ((b.code i).priceCap A d M x) := by
  cases x with
  | none => exact h i
  | some u => exact hc (b.code i) (.inl (some u))

omit [Fintype I] [DecidableEq I] [DecidableEq S] in
theorem priceCap_eq (i : I) (x : (b.code i).Req A) :
    ((b.code i).priceCap A d M x : ℝ) = b.cap A d M (b.request A i x) := by
  rcases x with _ | ⟨z, j⟩ <;> rfl

variable [Nonempty S] (g : b.Ports t)

abbrev Source := Σ i, (b.code i).Req A

def requestOf (u : b.Source A) := b.request A u.1 u.2

def earliest (x : b.Request A) (u : b.Source A) : Prop :=
  b.requestOf A u = x ∧ ∀ v : b.Source A, b.requestOf A v = x →
    g.key (b.home A x) u.1 ≤ g.key (b.home A x) v.1

theorem depot_exists (x : b.Request A) : ∃! u, b.earliest A g x u := by
  let key (u : b.Source A) := g.key (b.home A x) u.1
  let P (n : ℕ) := ∃ u : b.Source A, b.requestOf A u = x ∧ key u = n
  have h : ∃ n, P n := by
    obtain ⟨i, j, h⟩ := b.request_surj A x
    exact ⟨_, ⟨i, j⟩, h, rfl⟩
  obtain ⟨u, hu, hk⟩ := Nat.find_spec h
  have min' (v : b.Source A) (hv : b.requestOf A v = x) : key u ≤ key v :=
    hk.le.trans (Nat.find_min' h ⟨v, hv, rfl⟩)
  refine ⟨u, ⟨hu, min'⟩, fun v hv => ?_⟩
  have hn (w : b.Source A) (hw : b.requestOf A w = x) : w.1 ∈ b.neighbors (b.home A x) := by
    refine mem_biUnion.mpr ⟨b.home A x, mem_map.mpr ⟨_, mem_univ _, b.origin _⟩, ?_⟩
    exact mem_filter.mpr ⟨mem_univ _, b.home_mem A _ (.inl w.2) _ (congrArg Sum.inl hw)⟩
  have he := g.key_inj _ (hn v hv.1) (hn u hu) (le_antisymm (hv.2 u hu) (min' v hv.1))
  rcases u with ⟨i, u⟩
  rcases v with ⟨j, v⟩
  change j = i at he
  subst j
  have e : b.assign A i (.inl v) = b.assign A i (.inl u) := congrArg Sum.inl (hv.1.trans hu.symm)
  rw [Sum.inl.inj (b.assign_injective A i e)]

def depot (x : b.Request A) := (b.depot_exists A g x).exists.choose

theorem depot_spec (x : b.Request A) : b.earliest A g x (b.depot A g x) :=
  (b.depot_exists A g x).exists.choose_spec

theorem depot_iff (u : b.Source A) :
    b.depot A g (b.requestOf A u) = u ↔
      ∀ j ∈ b.neighbors u.1, ∀ v, b.request A j v = b.requestOf A u →
        g.key (b.home A (b.requestOf A u)) u.1 ≤ g.key (b.home A (b.requestOf A u)) j := by
  constructor
  · intro h j _ v hv
    have he := (b.depot_spec A g (b.requestOf A u)).2 ⟨j, v⟩ hv
    rwa [h] at he
  · intro h
    refine (b.depot_exists A g _).unique (b.depot_spec A g _) ⟨rfl, fun v hv => ?_⟩
    exact h _ (b.overlap_neighbor A _ _ _ _ hv.symm) _ hv

def tally (x : b.Request A) : b.Edge → ℕ :=
  let u := b.depot A g x
  Stock.collect (fun e => ⟨u.1, e⟩) ((b.code u.1).route A d M u.2)

theorem tally_cost (h : b.ready A d) (hc : UniformCap N A M) (x : b.Request A) :
    (∑ e, b.tally A d M g x e : ℕ) ≤ b.cap A d M x := by
  let u := b.depot A g x
  have he := ((b.code u.1).route_spec A d M u.2 (b.local_route A d M h hc u.1 u.2)).1
  change (↑(∑ e, Stock.collect (fun t => (⟨u.1, t⟩ : b.Edge)) ((b.code u.1).route A d M u.2) e) : ℝ) ≤ _
  rw [show (∑ e, Stock.collect _ _ e) = ∑ e, (b.code u.1).route A d M u.2 e
    from sum_fiberwise _ _ _]
  exact (Nat.cast_le.mpr he).trans_eq ((b.priceCap_eq A d M u.1 u.2).trans
    (congrArg _ (b.depot_spec A g x).1))

end Market
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Computing allocation keys from local orbit observations
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral
open scoped Classical Pointwise
variable {G K S : Type} [Group G] [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  {H : Finset G} {r t : ℕ} (w : Fin (2 ^ t) → G)

namespace Root

def index (a b : G) (x : Root G) : ℕ :=
  ∑ i ∈ first w (x.shift a), if x.see (w i * a) b then i.val else 0

theorem index_local (a b : G) : Local (index w a b) := by
  have h : Local (fun x : Root G => fun j => x.see (w j * a) b) :=
    local_pi (fun j => local_see _ _)
  exact (((local_first w).shift a).pair h).map
    (fun y => ∑ i ∈ y.1, if y.2 i then i.val else 0)

end Root

variable (A : Finset (Tensor K S))

def Board.home (b : Board H r) : b.1.Req A → G
  | none => 1
  | some (z, _) => b.word (z (Classical.arbitrary S))

variable (H) (hH : 1 ∈ H) (r) (g : G) (hg : g ∈ H ^ r)

def keys (x : Root G) (j : Fin (2 ^ t)) (u : Key (H ^ r).card A) : ℕ :=
  let b := Board.choose H r hH g hg x
  if h : u.1 = b.1 then x.index w (b.home A (h ▸ u.2)) (w j) else 0

omit [DecidableEq S] in
theorem local_keys : Root.Local (keys H r w A hH g hg) := by
  have h : Root.Local (fun x : Root G => fun (b : Board H r) (v : b.1.Req A) (j : Fin (2 ^ t)) =>
      x.index w (b.home A v) (w j)) :=
    Root.local_pi fun _ => Root.local_pi fun _ => Root.local_pi fun _ => Root.index_local _ _ _
  exact ((Board.local_choose H r hH g hg).pair h).map
    (fun y j (u : Key (H ^ r).card A) => if h : u.1 = y.1.1 then y.2 y.1 (h ▸ u.2) j else 0)

variable {I : Type} [MulAction G I] [Fintype I] [DecidableEq I] (hw : Set.range w = offsets H r)

theorem index_eq (i : I) (a b : G) :
    Root.index w a b ⟨I, i⟩ = (marketPorts H r hH g hg w hw).key (a • i) (b • i) := by
  unfold Root.index Market.Ports.key
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Root.see, decide_eq_true_eq]
  change (if (w j * a) • i = b • i then j.val else 0) = _
  simp only [mul_smul, marketPorts]
  congr

omit [DecidableEq S] in
theorem keys_eq (i : I) (j : Fin (2 ^ t)) (u : ((market H hH r g hg).code i).Req A) :
    let b := market H hH r g hg
    keys H r w A hH g hg ⟨I, i⟩ j ⟨b.code i, u⟩ =
      (marketPorts H r hH g hg w hw).key (b.home A (b.request A i u)) (w j • i) := by
  let b := market (I := I) H hH r g hg
  let x := board H hH r g hg i
  have he : x.home A u • i = b.home A (b.request A i u) := by
    rcases u with _ | ⟨z, k⟩
    · exact one_smul _ _
    · rfl
  dsimp only [keys]
  rw [dite_eq_left (show b.code i = x.1 from rfl)]
  exact (index_eq H r w hH g hg hw i (x.home A u) (w j)).trans
    (congrArg (fun y => (marketPorts H r hH g hg w hw).key y (w j • i)) he)

end OAI.LinearAlgebra.MatrixExponent.Routing
end
