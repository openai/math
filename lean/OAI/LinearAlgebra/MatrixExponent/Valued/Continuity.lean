import OAI.LinearAlgebra.MatrixExponent.Valued.Extension
import OAI.LinearAlgebra.MatrixExponent.Valued.Extra
import OAI.LinearAlgebra.MatrixExponent.Prices.Fields
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.ScaleSlope
import OAI.LinearAlgebra.MatrixExponent.Valued.Uniform
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryComparison
import Mathlib.Analysis.MeanInequalities

/-!
# Assignments of added sites at fixed scale

A placement preserving every old name necessarily preserves full
diagonal prices. Its multiplicative evaluation is then additive by the
binomial expansion. Assignments can consequently be restricted or
duplicated without changing the scale.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open ITensor Spectral

variable {K S U V W : Type} [Field K] {O : Subring K}
  [Fintype S] [Nonempty S] {f : ITensor O S →+* ℝ}

structure Assignment (f : ITensor O S →+* ℝ) (U : Type) [Fintype U] where
  val : ITensor O (S ⊕ U) →+* ℝ
  mono : Monotone val
  old : ∀ A, val (pad U A) = f A

namespace Assignment

variable [Fintype U] [Fintype V] [Fintype W]

theorem exists_iff {I : Type*} (hf : Monotone f) (A : I → ITensor O (S ⊕ U)) (p : I → ℝ) :
    (∃ g : Assignment f U, ∀ i, g.val (A i) ≤ p i) ↔
      ∀ w : List I, Prices.assisted (pad U) f (w.map A).prod ≤ (w.map p).prod := by
  refine Iff.trans ?_ ((extensionData f hf).assisted_extension_iff A p)
  exact ⟨fun ⟨g, h⟩ => ⟨g.val, g.mono, g.old, h⟩, fun ⟨g, hg, he, h⟩ => ⟨⟨g, hg, he⟩, h⟩⟩

theorem nonneg (g : Assignment f U) (A : ITensor O (S ⊕ U)) : 0 ≤ g.val A := by
  simpa using g.mono (zero_le A)

variable [DecidableEq S] [DecidableEq U] [DecidableEq V] [DecidableEq W]

private theorem place_nat {X Y : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (x : X → Y) (n : ℕ) : place x (n : ITensor O X) ≤ n := by
  induction n with
  | zero => rw [Nat.cast_zero, Nat.cast_zero, place_zero]; exact le_rfl
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ]
    refine (place_add_le x _ _).trans ?_
    rw [place_one]
    exact ITensor.add_le_add_right _ _ _ ih

theorem place_pad (x : U → V) (A : ITensor O S) : place (Sum.map id x) (pad U A) = pad V A := by
  rw [← place_inl, ← place_comp, show Sum.map (id : S → S) x ∘ Sum.inl = Sum.inl from rfl, place_inl]

private theorem pull_add (g : Assignment f V) (x : U → V) (A B : ITensor O (S ⊕ U)) :
    g.val (place (Sum.map id x) (A + B)) =
      g.val (place (Sum.map id x) A) + g.val (place (Sum.map id x) B) := by
  let e := Sum.map (id : S → S) x
  let p : ITensor O (S ⊕ U) →* ℝ :=
    { toFun := fun X => g.val (place e X)
      map_one' := by rw [place_one, map_one]
      map_mul' := fun X Y => by rw [place_mul, map_mul] }
  have hp : Monotone p := g.mono.comp (place_mono e)
  have hn (n : ℕ) : p n = (n : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    apply le_antisymm
    · exact (g.mono (place_nat e n)).trans_eq (map_natCast g.val n)
    · have h := hp (place_nat (Sum.inl : S → S ⊕ U) n)
      change g.val (place (Sum.map id x) (place Sum.inl (n : ITensor O S))) ≤ p n at h
      rwa [place_inl, place_pad, g.old, map_natCast] at h
  obtain ⟨q, _, eq⟩ := Tensor.normalize_hom ITensor.add_le_add_right zero_le p hp
    (by change g.val (place e 0) = _; rw [place_zero, map_zero])
    (fun a b => (g.mono (place_add_le _ _ _)).trans_eq (g.val.map_add _ _)) zero_lt_one hn
  simp only [inv_one, Real.rpow_one] at eq
  exact (eq _).symm.trans ((q.map_add A B).trans (congrArg₂ (· + ·) (eq A) (eq B)))

def pull (g : Assignment f V) (x : U → V) : Assignment f U where
  val :=
    { toFun := fun A => g.val (place (Sum.map id x) A)
      map_zero' := by rw [place_zero, map_zero]
      map_one' := by rw [place_one, map_one]
      map_mul' := fun A B => by rw [place_mul, map_mul]
      map_add' := pull_add g x }
  mono := g.mono.comp (place_mono _)
  old A := (congrArg g.val (place_pad x A)).trans (g.old A)

theorem pull_apply (g : Assignment f V) (x : U → V) (A : ITensor O (S ⊕ U)) :
    (g.pull x).val A = g.val (place (Sum.map id x) A) := rfl

theorem pull_comp (g : Assignment f W) (x : U → V) (y : V → W) (A : ITensor O (S ⊕ U)) :
    ((g.pull y).pull x).val A = (g.pull (y ∘ x)).val A := by
  simp only [pull_apply, ← place_comp]
  rw [show Sum.map (id : S → S) y ∘ Sum.map id x = Sum.map id (y ∘ x) by funext z; cases z <;> rfl]

theorem pull_id (g : Assignment f U) (A : ITensor O (S ⊕ U)) : (g.pull id).val A = g.val A := by
  rw [pull_apply, show Sum.map id id = (id : S ⊕ U → S ⊕ U) by funext z; cases z <;> rfl, place_id]

private abbrev unassoc (S U V : Type) := (Equiv.sumAssoc S U V).symm

def chain (g : Assignment f U) (k : Assignment g.val V) : Assignment f (U ⊕ V) where
  val := k.val.comp (group (unassoc S U V) (unassoc S U V).surjective)
  mono := k.mono.comp (group_mono _ _)
  old A := by
    change k.val (place (unassoc S U V) (pad _ A)) = _
    rw [← place_inl, ← place_comp,
      show unassoc S U V ∘ Sum.inl = Sum.inl ∘ Sum.inl from rfl, place_comp,
      place_inl, place_inl, k.old, g.old]

theorem chain_left (g : Assignment f U) (k : Assignment g.val V) (A : ITensor O (S ⊕ U)) :
    ((g.chain k).pull Sum.inl).val A = g.val A := by
  change k.val (place (unassoc S U V) (place (Sum.map id Sum.inl) A)) = _
  rw [← place_comp, show unassoc S U V ∘ Sum.map id Sum.inl = Sum.inl by
    funext z; cases z <;> rfl, place_inl, k.old]

theorem chain_right (g : Assignment f U) (k : Assignment g.val V) (A : ITensor O (S ⊕ V)) :
    ((g.chain k).pull Sum.inr).val A = k.val (place (Sum.map Sum.inl id) A) := by
  change k.val (place (unassoc S U V) (place (Sum.map id Sum.inr) A)) = _
  rw [← place_comp, show unassoc S U V ∘ Sum.map id Sum.inr = Sum.map Sum.inl id by
    funext z; cases z <;> rfl]

private theorem place_prod (e : U → V) (w : List (ITensor O U)) :
    place e w.prod = (w.map (place e)).prod := by
  induction w with
  | nil => exact place_one e
  | cons i w ih => rw [List.prod_cons, place_mul, ih]; rfl

/-- Keep one assignment, bounding every price on the added copy by
its value at the competing assignment. -/
theorem combine (g : Assignment f U) (h : Assignment f V) :
    ∃ k : Assignment f (U ⊕ V), (∀ A, (k.pull Sum.inl).val A = g.val A) ∧
      ∀ B, (k.pull Sum.inr).val B ≤ h.val B := by
  let e : S ⊕ V → (S ⊕ U) ⊕ V := Sum.map Sum.inl id
  have tests (w : List (ITensor O (S ⊕ V))) (A : ITensor O (S ⊕ U))
      (hA : pad V A ≤ (w.map (place e)).prod) : g.val A ≤ (w.map h.val).prod := by
    rw [← place_prod] at hA
    obtain ⟨B, hB, hC⟩ := close_extra hA
    rw [← map_list_prod]
    exact (g.mono hB).trans ((g.old B).trans_le ((h.old B).symm.trans_le (h.mono hC)))
  obtain ⟨k, hk, ek, hle⟩ := (extension_iff g.val g.mono (place e) h.val).mpr tests
  let k' : Assignment g.val V := ⟨k, hk, ek⟩
  exact ⟨g.chain k', g.chain_left k', fun A => (g.chain_right k' A).trans_le (hle A)⟩

end Assignment
end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-! # Geodesic interpolation of valued assignments -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.Assignment
open ITensor Spectral Routing

variable {F K S U V W : Type} [Field F] [Field K] [Algebra F K] {O : Subring K}
  [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {f : ITensor O S →+* ℝ}

omit [DecidableEq S] [DecidableEq U] in
theorem ext {g k : Assignment f U} (h : ∀ A, g.val A = k.val A) : g = k := by
  cases g
  cases k
  congr
  exact RingHom.ext h

theorem pull_pull (g : Assignment f W) (x : U → V) (y : V → W) :
    (g.pull y).pull x = g.pull (y ∘ x) := ext (g.pull_comp x y)

def atSite (g : Assignment f U) (x : U) : Assignment f Unit := g.pull (fun _ => x)

theorem pull_atSite (g : Assignment f V) (x : U → V) (i : U) :
    (g.pull x).atSite i = g.atSite (x i) := g.pull_pull _ _

theorem atUnit (g : Assignment f Unit) : g.atSite () = g := ext g.pull_id

variable (hO : constants F K ≤ O)

def point (g : Assignment f U) : Tensor F (S ⊕ U) →+* ℝ := g.val.comp (fromBase hO)

omit [DecidableEq S] [DecidableEq U] in
theorem point_mono (g : Assignment f U) : Monotone (g.point hO) := g.mono.comp (fromBase_mono hO)

def dist (g : Assignment f U) : S ⊕ U → S ⊕ U → ℝ := Tensor.dist (g.point hO)

def radius (o : S) (g : Assignment f Unit) : ℝ := dist hO g (.inl o) (.inr ())

theorem dist_pull (g : Assignment f V) (x : U → V) (i j : S ⊕ U) :
    dist hO (g.pull x) i j = dist hO g (Sum.map id x i) (Sum.map id x j) := by
  unfold dist Tensor.dist
  change Real.log (g.val (place (Sum.map id x) (wire hO i j 2))) / _ = _
  rw [place_wire]
  rfl

theorem radius_atSite (o : S) (g : Assignment f U) (x : U) :
    radius hO o (g.atSite x) = dist hO g (.inl o) (.inr x) :=
  dist_pull hO _ _ _ _

theorem dist_nonneg (g : Assignment f U) (i j) : 0 ≤ dist hO g i j :=
  Tensor.dist_nonneg _ (g.point_mono hO) _ _

theorem dist_self (g : Assignment f U) (i) : dist hO g i i = 0 := Tensor.dist_self _ _

theorem price_wire (g : Assignment f U) (i j : S ⊕ U) :
    g.val (wire hO i j 2) = (2 : ℝ) ^ dist hO g i j := by
  exact Tensor.price_wire _ (g.point_mono hO) _ _ (by decide)

theorem pull_eq (g : Assignment f V) (x y : U → V)
    (h : ∀ i, dist hO g (.inr (x i)) (.inr (y i)) = 0) : g.pull x = g.pull y := by
  refine ext fun A => price_place_eq hO _ g.mono _ _ ?_ A
  rintro (i | i)
  · exact dist_self _ _ _
  · exact h i

private def fold (g : Assignment f U) (a : U) : Assignment g.val Unit where
  val := g.val.comp (group (Sum.elim id (fun _ : Unit => Sum.inr a)) (fun b => ⟨.inl b, rfl⟩))
  mono := g.mono.comp (group_mono _ _)
  old B := congrArg g.val (group_pad _ _ (fun _ => rfl) B)

private theorem fold_apply (g : Assignment f U) (a : U) (B : ITensor O (S ⊕ Unit)) :
    (fold g a).val (place (Sum.map Sum.inl id) B) = (g.atSite a).val B := by
  let e : (S ⊕ U) ⊕ Unit → S ⊕ U := Sum.elim id (fun _ => Sum.inr a)
  change g.val (place e (place (Sum.map Sum.inl id) B)) = _
  rw [← place_comp, show e ∘ Sum.map Sum.inl id = Sum.map id (fun _ => a) by funext i; cases i <;> rfl]
  rfl

/-- All evaluated tensors interpolate from above; radii satisfy the
squared-distance comparison with its strict convexity term. -/
theorem segment (hc : SpectralComparison F) (g : Assignment f U) (o : S) (a b : U) (t : Fraction) :
    ∃ p : Assignment f Unit,
      (∀ B, p.val B ≤ (g.atSite a).val B ^ (1 - t.val) * (g.atSite b).val B ^ t.val) ∧
      radius hO o p ^ 2 ≤ (1 - t.val) * radius hO o (g.atSite a) ^ 2 + t.val * radius hO o (g.atSite b) ^ 2 -
        t.val * (1 - t.val) * dist hO g (.inr a) (.inr b) ^ 2 := by
  let A := fold g a
  let B := fold g b
  obtain ⟨p, hp, ep, hu⟩ := (extensionData g.val g.mono).interpolate B.val A.val B.mono A.mono
    B.old A.old t.2.1 t.2.2
  let k : Assignment g.val Unit := ⟨p, hp, ep⟩
  have hdist (i j : S ⊕ U) : dist hO k (.inl i) (.inl j) = dist hO g i j := by
    unfold dist Tensor.dist
    change Real.log (p (wire hO (.inl i) (.inl j) 2)) / _ = _
    rw [← place_wire hO Sum.inl, place_inl, ep]
    rfl
  have ev (i : S ⊕ U) (c : U) :
      (fold g c).val (wire hO (.inl i) (.inr ()) 2) = g.val (wire hO i (.inr c) 2) := by
    change g.val (place _ (wire hO _ _ _)) = _
    rw [place_wire]
    rfl
  have hd (i : S ⊕ U) : dist hO k (.inl i) (.inr ()) ≤
      (1 - t.val) * dist hO g i (.inr a) + t.val * dist hO g i (.inr b) := by
    have h := hu (wire hO (.inl i) (.inr ()) 2)
    change k.val _ ≤ (fold g b).val _ ^ _ * (fold g a).val _ ^ _ at h
    rw [ev, ev, price_wire, price_wire, price_wire] at h
    have hz : 0 < (2 : ℝ) := by norm_num
    rw [← Real.rpow_mul hz.le, ← Real.rpow_mul hz.le, ← Real.rpow_add hz] at h
    linarith only [(Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h]
  have hm : Tensor.Between (k.point hO) (.inl (.inr a)) (.inr ()) (.inl (.inr b)) t := by
    apply Tensor.between_of_le _ (k.point_mono hO)
    · change dist hO k _ _ ≤ _ * dist hO k _ _
      simpa [hdist, dist_self] using hd (.inr a)
    · rw [Tensor.dist_comm _ (Sum.inr ())]
      change dist hO k _ _ ≤ _ * dist hO k _ _
      have e : dist hO g (.inr b) (.inr a) = dist hO g (.inr a) (.inr b) := Tensor.dist_comm _ _ _
      simpa [hdist, dist_self, e] using hd (.inr b)
  let P := (g.chain k).pull Sum.inr
  refine ⟨P, ?_, ?_⟩
  · intro X
    rw [show P.val X = k.val _ from g.chain_right k X]
    exact (hu _).trans_eq (by rw [mul_comm, fold_apply, fold_apply])
  · have hx : radius hO o P = dist hO k (.inl (.inl o)) (.inr ()) := by
      unfold radius dist Tensor.dist
      change Real.log (P.val (wire hO (.inl o) (.inr ()) 2)) / _ = _
      rw [show P.val _ = k.val _ from g.chain_right k _, place_wire]
      rfl
    have h := hc _ _ (k.point_mono hO) _ _ _ _ hm (.inl (.inl o))
    simp only [Tensor.dist_comm _ _ (Sum.inl (Sum.inl o))] at h
    rw [hx, radius_atSite, radius_atSite, ← hdist, ← hdist, ← hdist]
    exact h

end OAI.LinearAlgebra.MatrixExponent.Valued.Assignment
end

/-!
# Pinning by the distance to an anchor

Feasibility is given by upper bounds on individual tensor evaluations.
Within a common assignment, two feasible sites minimizing the distance
to an anchor must coincide by geodesic comparison. Duplicating sites
then yields uniqueness of all joint prices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.Assignment
open ITensor Spectral Routing

variable {F K S U V : Type} [Field F] [Field K] [Algebra F K] {O : Subring K}
  [Fintype S] [Nonempty S] [DecidableEq S] [Fintype U] [DecidableEq U]
  [Fintype V] [DecidableEq V] {f : ITensor O S →+* ℝ}

def Supports {I : Type*} (g : Assignment f U) (A : I → ITensor O (S ⊕ U)) (p : I → ℝ) : Prop :=
  ∀ i, g.val (A i) ≤ p i

/-- Constraints at distinct new sites can be imposed independently. -/
theorem separate {I : Type*} (hf : Monotone f) (A : U → I → ITensor O (S ⊕ Unit))
    (p : U → I → ℝ) (hp : ∀ u, ∃ g : Assignment f Unit, g.Supports (A u) (p u)) :
    ∃ g : Assignment f U, ∀ u, (g.atSite u).Supports (A u) (p u) := by
  have H (t : Finset U) : ∃ g : Assignment f U, ∀ u ∈ t, (g.atSite u).Supports (A u) (p u) := by
    induction t using Finset.induction_on with
    | empty =>
      obtain ⟨g, hg, he⟩ := (extensionData (U := U) f hf).exists_extension
      exact ⟨⟨g, hg, he⟩, by simp⟩
    | @insert u t hu ih =>
      obtain ⟨g, hg⟩ := ih
      obtain ⟨k, hk⟩ := hp u
      obtain ⟨q, h₁, h₂⟩ := g.combine k
      let x (v : U) : U ⊕ Unit := if v = u then .inr () else .inl v
      refine ⟨q.pull x, fun v hv => ?_⟩
      rw [pull_atSite]
      rcases Finset.mem_insert.mp hv with hv | hv
      · subst v
        rw [show x u = .inr () from ite_eq_left rfl, ← pull_atSite, atUnit]
        exact fun i => (h₂ _).trans (hk i)
      · rw [show x v = .inl v from ite_eq_right (fun e : v = u => hu (e ▸ hv)), ← pull_atSite, ext h₁]
        exact hg v hv
  obtain ⟨g, hg⟩ := H Finset.univ
  exact ⟨g, fun u => hg u (Finset.mem_univ u)⟩

variable (hO : constants F K ≤ O) (o : S) {I : Type*}

/-- Combine tensor constraints with an upper bound on the anchor distance. -/
def pinned (A : I → ITensor O (S ⊕ Unit)) : Option I → ITensor O (S ⊕ Unit)
  | none => wire hO (.inl o) (.inr ()) 2
  | some i => A i

def bounds (p : I → ℝ) (r : ℝ) : Option I → ℝ
  | none => (2 : ℝ) ^ r
  | some i => p i

theorem pinned_iff (g : Assignment f Unit) (A : I → ITensor O (S ⊕ Unit)) (p : I → ℝ) (r : ℝ) :
    g.Supports (pinned hO o A) (bounds p r) ↔ g.Supports A p ∧ radius hO o g ≤ r := by
  have H : g.val (pinned hO o A none) ≤ bounds p r none ↔ radius hO o g ≤ r := by
    rw [pinned, bounds, price_wire, Real.rpow_le_rpow_left_iff (by norm_num)]
    rfl
  exact ⟨fun h => ⟨fun i => h (some i), H.mp (h none)⟩,
    fun h i => by cases i with
      | none => exact H.mpr h.2
      | some i => exact h.1 i⟩

theorem pin_exists {J : Type*} [Nonempty J] (hf : Monotone f)
    (A : J → I → ITensor O (S ⊕ Unit)) (p : I → ℝ)
    (hp : ∀ j, ∃ g : Assignment f Unit, g.Supports (A j) p) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1, IsLeast
      {v | ∀ j, ∃ g : Assignment f Unit, g.Supports (pinned hO o (A j)) (bounds p v)} r := by
  let R := {v | ∀ j, ∃ g : Assignment f Unit, g.Supports (pinned hO o (A j)) (bounds p v)}
  have hi : 1 ∈ R := fun j => by
    obtain ⟨g, hg⟩ := hp j
    exact ⟨g, (pinned_iff _ _ _ _ _ _).mpr ⟨hg, Tensor.dist_le_one _ (g.point_mono hO) _ _⟩⟩
  have lo : 0 ∈ lowerBounds R := by
    intro r h
    obtain ⟨g, hg⟩ := h (Classical.arbitrary J)
    exact (dist_nonneg hO g _ _).trans ((pinned_iff _ _ _ _ _ _).mp hg).2
  have hb (i : Option I) : Continuous (fun v => bounds p v i) := by
    cases i with
    | none => simp only [bounds, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; fun_prop
    | some _ => exact continuous_const
  have hw (w : List (Option I)) : Continuous (fun v => (w.map (bounds p v)).prod) := by
    induction w with
    | nil => exact continuous_const
    | cons i w ih => exact (hb i).mul ih
  have hc : IsClosed R := by
    unfold R Supports
    simp only [exists_iff hf, Set.ofPred_forall]
    exact isClosed_iInter fun _ => isClosed_iInter fun w => isClosed_le continuous_const (hw w)
  have hs := hc.isLeast_csInf ⟨1, hi⟩ ⟨0, lo⟩
  exact ⟨_, ⟨lo hs.1, hs.2 hi⟩, hs⟩

theorem mix_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ c) (k : b ≤ c)
    (t : Fraction) : a ^ (1 - t.val) * b ^ t.val ≤ c := by
  have hc := ha.trans h
  have ht := sub_nonneg.mpr t.2.2
  calc
    _ ≤ c ^ (1 - t.val) * c ^ t.val :=
      mul_le_mul (Real.rpow_le_rpow ha h ht) (Real.rpow_le_rpow hb k t.2.1)
        (Real.rpow_nonneg hb _) (Real.rpow_nonneg hc _)
    _ = c := by rw [← Real.rpow_add_of_nonneg hc ht t.2.1, sub_add_cancel, Real.rpow_one]

theorem pin_unique (hc : SpectralComparison F) (g : Assignment f U)
    {A : I → ITensor O (S ⊕ Unit)} {p : I → ℝ} {r : ℝ}
    (hlo : ∀ h : Assignment f Unit, h.Supports A p → r ≤ radius hO o h)
    {x y : U} (hx : (g.atSite x).Supports (pinned hO o A) (bounds p r))
    (hy : (g.atSite y).Supports (pinned hO o A) (bounds p r)) :
    dist hO g (.inr x) (.inr y) = 0 := by
  obtain ⟨hx, hr⟩ := (pinned_iff _ _ _ _ _ _).mp hx
  obtain ⟨hy, hr'⟩ := (pinned_iff _ _ _ _ _ _).mp hy
  let t : Fraction := ⟨1 / 2, by norm_num⟩
  obtain ⟨k, hk, hd⟩ := segment hO hc g o x y t
  have hb := hlo k fun i => (hk _).trans (mix_le ((g.atSite x).nonneg _) ((g.atSite y).nonneg _)
    (hx i) (hy i) t)
  rw [le_antisymm hr (hlo _ hx), le_antisymm hr' (hlo _ hy)] at hd
  have hz : 0 ≤ r := (dist_nonneg hO (g.atSite x) _ _).trans hr
  have hw := pow_le_pow_left₀ hz hb 2
  dsimp only [t] at hd
  nlinarith only [hd, hw]

theorem pins_equal (hc : SpectralComparison F) {g h : Assignment f U}
    {A : U → I → ITensor O (S ⊕ Unit)} {p : I → ℝ} {r : ℝ}
    (hlo : ∀ i (h : Assignment f Unit), h.Supports (A i) p → r ≤ radius hO o h)
    (hg : ∀ i, (g.atSite i).Supports (pinned hO o (A i)) (bounds p r))
    (hh : ∀ i, (h.atSite i).Supports (pinned hO o (A i)) (bounds p r)) : g = h := by
  have cmp (g h : Assignment f U)
      (hg : ∀ i, (g.atSite i).Supports (pinned hO o (A i)) (bounds p r))
      (hh : ∀ i, (h.atSite i).Supports (pinned hO o (A i)) (bounds p r)) :
      ∀ B, g.val B ≤ h.val B := by
    obtain ⟨k, hl, hr⟩ := g.combine h
    have e : k.pull Sum.inl = k.pull Sum.inr := by
      apply pull_eq hO
      intro i
      apply pin_unique hO o hc k (hlo i)
      · rw [← k.pull_atSite Sum.inl, ext hl]
        exact hg i
      · rw [← k.pull_atSite Sum.inr]
        exact fun j => (hr _).trans (hh i j)
    rw [← ext hl, e]
    exact hr
  exact ext fun B => le_antisymm (cmp g h hg hh B) (cmp h g hh hg B)

end OAI.LinearAlgebra.MatrixExponent.Valued.Assignment
end

/-!
# Pinning a finite system of polynomial inequalities

Use distance to an anchor as the objective. The minimal uniform
radius on the closed unit disk is also pointwise minimal at generic
parameters. We retain strict slack for continuity on smaller disks.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral Prices Motion K0 ITensor Assignment Filter

variable (F E S I : Type) [Field F] [Field E] [Algebra F (K0 E)]
  [Fintype S] [DecidableEq S] [Nonempty S]

structure Problem where
  inc : constants F (K0 E) ≤ RingOf E
  f : ITensor (RingOf E) S →+* ℝ
  mono : Monotone f
  scal : ∀ (x : K0 E) (r : ℚ), val E x = ↑r → f (scalar _ _ x) = Real.exp (-(r : ℝ))
  o : S
  A : I → K0 E → ITensor (RingOf E) (S ⊕ Unit)
  poly : ∀ i, ∃ d, Family (A i) d
  p : I → ℝ
  q : I → ℝ
  slack : ∀ i, p i < q i
  feasible : ∀ x ∈ RingOf E, ∃ g : Assignment f Unit, g.Supports (fun i => A i x) p
  r : ℝ
  bound : 0 ≤ r ∧ r ≤ 1
  least : IsLeast
    {v | ∀ x ∈ RingOf E, ∃ g : Assignment f Unit,
      g.Supports (pinned inc o (fun i => A i x)) (bounds q v)} r

namespace Problem
variable {F E S I} (H : Problem F E S I) {U : Type} [Fintype U] [DecidableEq U]

def pin (j : Option I) (x : K0 E) := pinned H.inc H.o (fun i => H.A i x) j

theorem poly_pin (j : Option I) : ∃ d, Family (H.pin j) d := by
  cases j with
  | none => exact Family.constant _
  | some i => exact H.poly i

def cap := bounds H.q H.r

def minimal (x : K0 E) : Prop :=
  ∀ g : Assignment H.f Unit, g.Supports (fun i => H.A i x) H.q → H.r ≤ radius H.inc H.o g

def Joint (z : U → K0 E) (g : Assignment H.f U) : Prop :=
  ∀ i, (g.atSite i).Supports (fun j => H.pin j (z i)) H.cap

theorem joint_exists (z : U → K0 E) (hz : ∀ i, z i ∈ RingOf E) :
    ∃ g, H.Joint z g := separate H.mono _ _ (fun i => H.least.1 _ (hz i))

theorem joint_unique {z : U → K0 E} (hz : ∀ i, H.minimal (z i))
    {g k : Assignment H.f U} (hg : H.Joint z g) (hk : H.Joint z k) : g = k :=
  pins_equal H.inc H.o (Routing.spectralComparison F) hz hg hk

theorem joint_pull {V : Type} [Fintype V] [DecidableEq V] {z : U → K0 E}
    {g : Assignment H.f U} (hg : H.Joint z g) (e : V → U) : H.Joint (z ∘ e) (g.pull e) := by
  intro i
  rw [pull_atSite]
  exact hg (e i)

theorem generic_minimal [Fintype I] (z : K0 E) (hz : z ∈ RingOf E) :
    ∀ᶠ c : E in cocountable, H.minimal (z + C c) := by
  have := cocountable_countable E
  let A (w : List (Option I)) (x : K0 E) := (w.map (fun i => H.pin i (z + x))).prod
  have hA (w : List (Option I)) : ∃ d, Family (A w) d := by
    obtain ⟨d, h⟩ := Family.list_prod H.pin H.poly_pin w
    simpa only [one_mul] using h.affine z 1
  have ht : ∀ᶠ c : E in cocountable, ∀ w, ∀ x ∈ RingOf E,
      assisted (pad Unit) H.f (A w x) ≤ assisted (pad Unit) H.f (A w (C c)) :=
    eventually_countable_forall.mpr fun w => (hA w).choose_spec.assisted_max H.f H.mono
  refine ht.mono fun c hc g hg => H.least.2 fun x hx => ?_
  let r := radius H.inc H.o g
  have hv := (pinned_iff H.inc H.o g _ _ r).mpr ⟨hg, le_rfl⟩
  have hs := (Assignment.exists_iff H.mono _ _).mp ⟨g, hv⟩
  refine (Assignment.exists_iff H.mono _ _).mpr fun w => ?_
  have hd := hc w (x - z) ((RingOf E).sub_mem hx hz)
  simp only [A, add_sub_cancel] at hd
  exact hd.trans (hs w)

end Problem
end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-!
# Generic joint profiles

For each finite list of shifts, attach the original constraints at each
site and admit every ordinary tensor as a probe. There are only countably
many words of tests over the countable ground field. Outside a countable
set of translations the closed-power tests are simultaneously maximal.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.Problem
open Spectral ITensor Prices Motion K0 Assignment Filter

variable {F E S I U V : Type} [Field F] [Field E] [Algebra F (K0 E)]
    [Fintype S] [Nonempty S] [DecidableEq S] [Fintype U] [DecidableEq U]
    (H : Problem F E S I)

abbrev Test (F S I U : Type) [Field F] [Fintype S] [Fintype U] :=
  (U × Option I) ⊕ Tensor F (S ⊕ U)

def test (z : U → K0 E) : Test F S I U → ITensor (RingOf E) (S ⊕ U)
  | .inl (i, j) => ITensor.place (Sum.map id (fun _ => i)) (H.pin j (z i))
  | .inr A => fromBase H.inc A

def scores (p : Tensor F (S ⊕ U) → ℝ) : Test F S I U → ℝ
  | .inl (_, j) => H.cap j
  | .inr A => p A

def measure (z : U → K0 E) (w : List (Test F S I U)) : ℝ :=
  assisted (pad U) H.f (w.map (H.test z)).prod

theorem supports_iff (z : U → K0 E) (p : Tensor F (S ⊕ U) → ℝ) :
    (∃ g : Assignment H.f U, H.Joint z g ∧ ∀ A, g.point H.inc A ≤ p A) ↔
      ∀ w, H.measure z w ≤ (w.map (H.scores p)).prod := by
  refine Iff.trans ?_ (Assignment.exists_iff H.mono (H.test z) (H.scores p))
  constructor
  · rintro ⟨g, hg, hp⟩
    exact ⟨g, fun j => match j with
      | .inl (i, j) => hg i j
      | .inr A => hp A⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, fun i j => hg (.inl (i, j)), fun A => hg (.inr A)⟩

theorem test_family (a b : U → K0 E) (w : List (Test F S I U)) :
    ∃ d, Family (fun x => (w.map (H.test (fun i => a i + b i * x))).prod) d := by
  refine Family.list_prod (fun j x => H.test (fun i => a i + b i * x) j) ?_ w
  rintro (⟨i, j⟩|B)
  · obtain ⟨d, h⟩ := H.poly_pin j
    obtain ⟨e, h⟩ := h.affine (a i) (b i)
    exact h.place (Sum.map id (fun _ => i))
  · exact Family.constant _

def translate (z : U → K0 E) (x : K0 E) := fun i => z i + x

def Peak (z : U → K0 E) (x : K0 E) : Prop :=
  (∀ i, H.minimal (translate z x i)) ∧
  ∀ w y, y ∈ RingOf E → H.measure (translate z y) w ≤ H.measure (translate z x) w

theorem controls {z : U → K0 E} {x y : K0 E} (hx : H.Peak z x)
    (g : Assignment H.f U) (hg : H.Joint (translate z x) g) (hy : y ∈ RingOf E) :
    ∃ h : Assignment H.f U, H.Joint (translate z y) h ∧ ∀ A, h.point H.inc A ≤ g.point H.inc A := by
  refine (H.supports_iff _ _).mpr fun w => (hx.2 w y hy).trans ?_
  exact (H.supports_iff _ _).mp ⟨g, hg, fun _ => le_rfl⟩ w

variable [Fintype I] [Countable F]

theorem generic_peak (z : U → K0 E) (hz : ∀ i, z i ∈ RingOf E) :
    ∀ᶠ c : E in cocountable, H.Peak z (C c) := by
  have := cocountable_countable E
  have := countable_tensor (K := F) (S := S ⊕ U)
  have hmin := eventually_all.mpr (fun i => H.generic_minimal (z i) (hz i))
  have hw (w : List (Test F S I U)) : ∀ᶠ c : E in cocountable,
      ∀ y ∈ RingOf E, H.measure (translate z y) w ≤ H.measure (translate z (C c)) w := by
    obtain ⟨d, hd⟩ := H.test_family z (fun _ => 1) w
    simp only [one_mul] at hd
    exact hd.assisted_max H.f H.mono
  exact hmin.and (eventually_countable_forall.mpr hw)

variable [Uncountable E]

private theorem model_exists (z : U → K0 E) (hz : ∀ i, z i ∈ RingOf E) :
    ∃ (g : Assignment H.f U) (x : K0 E), x ∈ RingOf E ∧ H.Peak z x ∧ H.Joint (translate z x) g := by
  have := cocountable_neBot E
  obtain ⟨c, hc⟩ := (H.generic_peak z hz).exists
  obtain ⟨g, hg⟩ := H.joint_exists _ (fun i => (RingOf E).add_mem (hz i) (C_mem c))
  exact ⟨g, C c, C_mem c, hc, hg⟩

/-- A chosen joint evaluation. Only integral shifts are used. -/
def model (z : U → K0 E) : Assignment H.f U := by
  have : Nonempty (Assignment H.f U) :=
    ⟨(H.joint_exists (fun _ => 0) (fun _ => (RingOf E).zero_mem)).choose⟩
  exact Classical.epsilon (fun g => ∃ x ∈ RingOf E, H.Peak z x ∧ H.Joint (translate z x) g)

theorem model_peak (z : U → K0 E) (hz : ∀ i, z i ∈ RingOf E) :
    ∃ x ∈ RingOf E, H.Peak z x ∧ H.Joint (translate z x) (H.model z) :=
  Classical.epsilon_spec (H.model_exists z hz)

def price (z : U → K0 E) := (H.model z).point H.inc

theorem price_controls (z : U → K0 E) (hz : ∀ i, z i ∈ RingOf E) {y : K0 E}
    (hy : y ∈ RingOf E) :
    ∃ g : Assignment H.f U, H.Joint (translate z y) g ∧ ∀ A, g.point H.inc A ≤ H.price z A := by
  obtain ⟨x, _, hx, hg⟩ := H.model_peak z hz
  exact H.controls hx _ hg hy

theorem price_eq (z : U → K0 E) (hz : ∀ i, z i ∈ RingOf E) {x : K0 E} (hx : x ∈ RingOf E)
    (hp : H.Peak z x) (g : Assignment H.f U) (hg : H.Joint (translate z x) g) :
    H.price z = g.point H.inc := by
  obtain ⟨h, hh, hb⟩ := H.price_controls z hz hx
  rw [H.joint_unique hp.1 hh hg] at hb
  obtain ⟨y, hy, hyp, hm⟩ := H.model_peak z hz
  obtain ⟨k, hk, he⟩ := H.controls hp g hg hy
  rw [H.joint_unique hyp.1 hk hm] at he
  exact RingHom.ext fun A => le_antisymm (he A) (hb A)

theorem price_pull [Fintype V] [DecidableEq V]
    (z : U → K0 E) (hz : ∀ i, z i ∈ RingOf E) (e : V → U) (A : Tensor F (S ⊕ V)) :
    H.price (z ∘ e) A = H.price z (Tensor.place (Sum.map id e) A) := by
  have := cocountable_neBot E
  have hy (i) : (z ∘ e) i ∈ RingOf E := hz _
  obtain ⟨c, h₁, h₂⟩ := ((H.generic_peak z hz).and (H.generic_peak _ hy)).exists
  obtain ⟨g, hg, _⟩ := H.price_controls z hz (C_mem c)
  rw [H.price_eq z hz _ h₁ g hg, H.price_eq (z ∘ e) hy _ h₂ (g.pull e) (H.joint_pull hg e)]
  · exact congrArg g.val (place_fromBase H.inc _ A)
  all_goals exact C_mem _

theorem price_shift (z : U → K0 E) (hz : ∀ i, z i ∈ RingOf E) {x : K0 E} (hx : x ∈ RingOf E) :
    H.price (translate z x) = H.price z := by
  have hh i : translate z x i ∈ RingOf E := (RingOf E).add_mem (hz i) hx
  obtain ⟨c, hc, hp, hg⟩ := H.model_peak z hz
  have he (y : K0 E) : translate (translate z x) y = translate z (x + y) := by
    funext i; exact add_assoc _ _ _
  have he' : translate (translate z x) (c - x) = translate z c := by rw [he, add_sub_cancel]
  refine H.price_eq _ hh ((RingOf E).sub_mem hc hx) ?_ _ (by rw [he']; exact hg)
  unfold Peak
  rw [he']
  exact ⟨hp.1, fun w y hy => by rw [he]; exact hp.2 w _ ((RingOf E).add_mem hx hy)⟩

end OAI.LinearAlgebra.MatrixExponent.Valued.Problem
end

/-!
# Submean estimates for pinned prices

Genericity is needed uniformly over words of probes. For a given
word take the supremum over the common translation first. Rational
thresholds reduce this extra supremum to countably many comparisons.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.Problem
open Spectral ITensor Prices Motion K0 Assignment Filter

variable {F E S I U : Type} [Field F] [Field E] [Algebra F (K0 E)]
    [Fintype S] [Nonempty S] [DecidableEq S] [Fintype U] [DecidableEq U]
    (H : Problem F E S I)

def aff (a b : U → K0 E) (x : K0 E) := fun i => a i + b i * x

theorem affine_family (a b : U → K0 E) (w : List (Test F S I U)) (y : K0 E) :
    ∃ d, Family (fun x => (w.map (H.test (translate (aff a b x) y))).prod) d := by
  have e (x) : translate (aff a b x) y = fun i => (a i + y) + b i * x := by
    funext i
    exact add_right_comm _ _ _
  simp_rw [e]
  exact H.test_family _ _ w

theorem cap_pos (j : Option I) : 0 < H.cap j := by
  cases j with
  | none => exact Real.rpow_pos_of_pos (by norm_num) _
  | some i =>
    obtain ⟨g, hg⟩ := H.feasible 0 (RingOf E).zero_mem
    exact ((g.nonneg _).trans (hg i)).trans_lt (H.slack i)

variable [Fintype I] [Countable F] [Uncountable E]

def charge (z : U → K0 E) : Test F S I U → ℝ
  | .inl (_, i) => Real.log (H.cap i)
  | .inr A => Real.log (H.price z A)

private theorem word_bound (z : U → K0 E) (hz : ∀ i, z i ∈ RingOf E)
    (w : List (Test F S I U)) (y : K0 E) (hy : y ∈ RingOf E) :
    H.measure (translate z y) w ≤ Real.exp (w.map (H.charge z)).sum := by
  let p (A : Tensor F (S ⊕ U)) := Real.exp (Real.log (H.price z A))
  obtain ⟨g, hg, hp⟩ := H.price_controls z hz hy
  have h (A) : g.point H.inc A ≤ p A := by
    by_cases ha : A = 0
    · simp [ha, p]
    unfold p
    have hpos : 0 < H.price z A := zero_lt_one.trans_le (Tensor.value_one_le ((H.model z).point_mono H.inc) ha)
    rw [Real.exp_log hpos]
    exact hp A
  have he (i : Test F S I U) : H.scores p i = Real.exp (H.charge z i) := by
    rcases i with ⟨j, i⟩ | A
    · exact (Real.exp_log (H.cap_pos i)).symm
    · rfl
  refine ((H.supports_iff _ p).mp ⟨g, hg, h⟩ w).trans_eq ?_
  induction w with
  | nil => simp
  | cons i w ih => simp only [List.map_cons, List.sum_cons, List.prod_cons, Real.exp_add, he, ih]

private theorem generic_affine (a b : U → K0 E)
    (hz : ∀ x ∈ RingOf E, ∀ i, aff a b x i ∈ RingOf E) :
    ∀ᶠ c : E in cocountable, ∀ w, ∀ x ∈ RingOf E, ∀ y ∈ RingOf E,
      H.measure (translate (aff a b x) y) w ≤ Real.exp (w.map (H.charge (aff a b (C c)))).sum := by
  have := countable_tensor (K := F) (S := S ⊕ U)
  let A (w : List (Test F S I U)) (y : RingOf E) (x : K0 E) :=
    (w.map (H.test (translate (aff a b x) y))).prod
  have hA w y : ∃ d, Family (A w y) d := H.affine_family a b w y.val
  refine (generic_bounds H.f H.mono A hA).mono fun c hc w x hx y hy => ?_
  exact hc w _ (fun j => H.word_bound _ (hz _ (C_mem c)) w _ j.2) ⟨y, hy⟩ x hx

private theorem profile_bound {J : Type} [Fintype J] (w : J → ℝ) (hw : ∑ j, w j = 1)
    (z : U → K0 E) (hz : ∀ i, z i ∈ RingOf E) (v : J → U → K0 E)
    (h : ∀ l, ∀ y ∈ RingOf E, H.measure (translate z y) l ≤
      Real.exp (∑ j, w j * (l.map (H.charge (v j))).sum)) (A : Tensor F (S ⊕ U)) :
    Real.log (H.price z A) ≤ ∑ j, w j * Real.log (H.price (v j) A) := by
  let p (A : Tensor F (S ⊕ U)) := Real.exp (∑ j, w j * Real.log (H.price (v j) A))
  have e (i : Test F S I U) : Real.exp (∑ j, w j * H.charge (v j) i) = H.scores p i := by
    rcases i with ⟨j, i⟩ | B
    · simp only [charge, scores, ← Finset.sum_mul, hw, one_mul, Real.exp_log (H.cap_pos i)]
    · rfl
  have e' (l : List (Test F S I U)) :
      Real.exp (∑ j, w j * (l.map (H.charge (v j))).sum) = (l.map (H.scores p)).prod := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons, mul_add, Finset.sum_add_distrib,
        Real.exp_add, e, ih]
  obtain ⟨x, hx, hp, _⟩ := H.model_peak z hz
  obtain ⟨g, hg, he⟩ := (H.supports_iff _ _).mpr fun l => (h l x hx).trans_eq (e' l)
  by_cases ha : A = 0
  · simp [ha]
  rw [H.price_eq z hz hx hp g hg, Real.log_le_iff_le_exp
    (zero_lt_one.trans_le (Tensor.value_one_le (g.point_mono H.inc) ha))]
  exact he A

theorem star (a b : U → K0 E) (x : K0 E) (hx : x ∈ RingOf E) {n : ℕ}
    (c : Fin n → K0 E) (r : Option (Fin n) → ℚ)
    (hc : ∀ j, 0 ≤ val E (c j)) (hd : ∀ i j, i ≠ j → val E (c i - c j) = 0)
    (hr : ∀ j, 0 < r j) (hz : ∀ i, aff a b x i ∈ RingOf E)
    (he : ∀ j y, y ∈ RingOf E → ∀ i, aff a b (armEnd c r y j) i ∈ RingOf E) :
    ∀ᶠ u : E in cocountable, ∀ A : Tensor F (S ⊕ U),
      Real.log (H.price (aff a b x) A) ≤
        ∑ j, weight r j * Real.log (H.price (aff a b (armEnd c r (C u) j)) A) := by
  let e j y := aff a b (armEnd c r y j)
  have affine (j) : ∃ a' b', e j = aff a' b' := by
    cases j with
    | none =>
      refine ⟨a, fun i => b i * t (-r none), ?_⟩
      funext y i
      simp [e, aff, armEnd, mul_assoc]
    | some j =>
      refine ⟨(fun i => a i + b i * c j), fun i => b i * t (r (some j)), ?_⟩
      funext y i
      simp [e, aff, armEnd, mul_add, mul_assoc, add_assoc]
  have ends (j) : ∀ᶠ u : E in cocountable, ∀ w,
      ∀ y ∈ RingOf E, ∀ z ∈ RingOf E, H.measure (translate (e j y) z) w ≤
        Real.exp (w.map (H.charge (e j (C u)))).sum := by
    obtain ⟨v, w, eq⟩ := affine j
    have h : ∀ y ∈ RingOf E, ∀ i, e j y i ∈ RingOf E := he j
    rw [eq] at h ⊢
    exact H.generic_affine v w h
  refine (eventually_all.mpr ends).mono fun u hu => H.profile_bound _ (weight_sum hr) _ hz _ ?_
  intro l y hy
  obtain ⟨d, h⟩ := H.affine_family a b l y
  let R j := (l.map (H.charge (e j (C u)))).sum
  let μ := ∑ j, weight r j * R j
  refine h.assisted_star H.f H.mono H.scal c hc hd r hr R (fun j z hz => hu j l z hz y hy)
    μ ?_ x hx
  have eq : (∑ j, (μ - R j) / (r j : ℝ)) = 0 := by
    have hp : 0 < ∑ j, (r j : ℝ)⁻¹ :=
      Finset.sum_pos (fun j _ => inv_pos.mpr (Rat.cast_pos.mpr (hr j))) Finset.univ_nonempty
    have h : μ * (∑ j, (r j : ℝ)⁻¹) = ∑ j, (r j : ℝ)⁻¹ * R j := by
      simp only [μ, weight, div_mul_eq_mul_div, ← Finset.sum_div, div_mul_cancel₀ _ hp.ne']
    simp only [sub_mul, Finset.sum_sub_distrib, div_eq_mul_inv, ← Finset.mul_sum, h,
      mul_comm (R _), sub_self]
  exact eq.ge

end OAI.LinearAlgebra.MatrixExponent.Valued.Problem
end

/-!
# Continuity of minimizing sites

The midpoint of two separated minimizers saves squared radius. A
small interpolation towards a strictly feasible site uses part of
that saving to absorb the change in the polynomial constraints.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.Problem
open Spectral Prices Motion K0 ITensor Assignment Routing

variable {F E S I : Type} [Field F] [Field E] [Algebra F (K0 E)]
  [Fintype S] [DecidableEq S] [Nonempty S] [Fintype I] (H : Problem F E S I)

omit [Fintype I] in
private theorem absorb (x : K0 E) (hx : x ∈ RingOf E) (t : Fraction)
    (k : Assignment H.f Unit)
    (hk : ∀ i, k.val (H.A i x) ≤ H.q i + t.val * (H.q i - H.p i)) (h : H.minimal x) :
    H.r ^ 2 ≤ radius H.inc H.o k ^ 2 + t.val := by
  obtain ⟨p, hp⟩ := H.feasible x hx
  obtain ⟨b, b₁, b₂⟩ := k.combine p
  let q := b.atSite (.inr ())
  have hq : q.Supports (fun i => H.A i x) H.p := by
    unfold q
    rw [← b.pull_atSite Sum.inr, atUnit]
    exact fun i => (b₂ _).trans (hp i)
  obtain ⟨c, hc, hr⟩ := segment H.inc (spectralComparison F) b H.o (.inl ()) (.inr ()) t
  rw [← b.pull_atSite Sum.inl, atUnit, Assignment.ext b₁] at hc hr
  have ht := t.property.1
  have ht' := sub_nonneg.mpr t.property.2
  have hcost : c.Supports (fun i => H.A i x) H.q := by
    intro i
    let A := H.A i x
    have hg := Real.geom_mean_le_arith_mean2_weighted ht' ht (k.nonneg A) (q.nonneg A)
      (sub_add_cancel 1 t.val)
    have h₁ := mul_le_mul_of_nonneg_left (hk i) ht'
    have h₂ := mul_le_mul_of_nonneg_left (hq i) ht
    have h₃ := mul_nonneg (sq_nonneg t.val) (sub_nonneg.mpr (H.slack i).le)
    change c.val A ≤ H.q i
    unfold A at *
    linarith only [(hc _).trans hg, h₁, h₂, h₃]
  have hr' := pow_le_pow_left₀ H.bound.1 (h c hcost) 2
  have h₁ : radius H.inc H.o q ≤ 1 := Tensor.dist_le_one _ (q.point_mono H.inc) _ _
  have h₂ : 0 ≤ radius H.inc H.o q := Assignment.dist_nonneg H.inc _ _ _
  have h₃ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h₂ h₁ 2) ht
  have h₄ := mul_nonneg ht (sq_nonneg (radius H.inc H.o k))
  have h₅ := mul_nonneg (mul_nonneg ht ht')
    (sq_nonneg (dist H.inc b (.inr (.inl ())) (.inr (.inr ()))))
  unfold q at h₃
  linarith only [hr', hr, h₃, h₄, h₅]

theorem continuity (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℚ, 0 < N ∧ ∀ (z : Bool → K0 E) (g : Assignment H.f Bool),
      (∀ i, z i ∈ RingOf E) → ↑N ≤ val E (z true - z false) →
      (∀ i, H.minimal (z i)) → H.Joint z g → dist H.inc g (.inr true) (.inr false) ≤ ε := by
  let t : Fraction := ⟨min (ε ^ 2 / 8) 1, le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have ht : 0 < t.val := lt_min (by positivity) zero_lt_one
  let δ i := t.val * (H.q i - H.p i)
  have hd i : 0 < δ i := mul_pos ht (sub_pos.mpr (H.slack i))
  choose m _ hm using fun i => (H.poly i).choose_spec.uniform_continuous (hd i)
  obtain ⟨N, hN⟩ := (Set.finite_range m).bddAbove
  refine ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z g hz hv hl hp => ?_⟩
  have hb (b : Bool) := (pinned_iff H.inc H.o (g.atSite b) _ _ _).mp (hp b)
  have hr (b : Bool) : radius H.inc H.o (g.atSite b) = H.r :=
    le_antisymm (hb b).2 (hl b _ (hb b).1)
  let u : Fraction := ⟨1 / 2, by norm_num⟩
  obtain ⟨k, hk, hr'⟩ := segment H.inc (spectralComparison F) g H.o true false u
  rw [hr, hr] at hr'
  have hq (i : I) : k.val (H.A i (z true)) ≤ H.q i + δ i := by
    let j := g.atSite false
    have hv' : ↑(m i) ≤ val E (z true - z false) :=
      (WithTop.coe_le_coe.mpr ((hN ⟨i, rfl⟩).trans (le_max_left _ _))).trans hv
    have he (a : K0 E) (r : ℚ) (ha : val E a = ↑r) :
        j.val (scalar (RingOf E) _ a) = Real.exp (-(r : ℝ)) := by
      rw [← pad_scalar, j.old, H.scal _ _ ha]
    have hdiff := (abs_sub_le_iff.mp (hm i j.val j.mono he _ _ (hz true) (hz false) hv')).1
    have h₁ := (hb true).1 i
    have h₂ := (hb false).1 i
    refine (hk _).trans (mix_le ((g.atSite true).nonneg _) ((g.atSite false).nonneg _) ?_ ?_ u)
    · exact h₁.trans (le_add_of_nonneg_right (hd i).le)
    · unfold j at hdiff
      exact (sub_le_iff_le_add'.mp hdiff).trans (add_le_add_left h₂ _)
  have hk' := H.absorb (z true) (hz true) t k hq (hl true)
  have hh : t.val ≤ ε ^ 2 / 8 := min_le_left _ _
  dsimp only [u] at hr'
  nlinarith only [hk', hr', hh, hε]

end OAI.LinearAlgebra.MatrixExponent.Valued.Problem
end
