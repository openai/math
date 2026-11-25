import OAI.LinearAlgebra.MatrixExponent.Routing.Partitions
import Mathlib.LinearAlgebra.Projection
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryJets
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OAI.LinearAlgebra.MatrixExponent.Routing.Packets
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

section
/-! A motion along a subspace may freely permute the auxiliary labels. -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {k V J : Type} [Field k] [AddCommGroup V] [Module k V]

abbrev Labels (V : Type) (I A : J → Type) (j : J) := (I j → V) × A j

def motion (I A : J → Type) (S : Submodule k V) :
    Subgroup (∀ j, Equiv.Perm (Labels V I A j)) where
  carrier := {g | ∀ j x i, (g j x).1 i - x.1 i ∈ S}
  one_mem' := by simp
  mul_mem' {g h} hg hh j x i := by
    simpa using S.add_mem (hg j (h j x) i) (hh j x i)
  inv_mem' {g} hg j x i := by
    simpa using S.neg_mem (hg j ((g j).symm x) i)

theorem motion_mono (I A : J → Type) {S T : Submodule k V} (h : S ≤ T) :
    motion I A S ≤ motion I A T :=
  fun _ hg j x i => h (hg j x i)

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Flags of projective points and lines

An ordered basis in each vector plane identifies its directions with the
same slope parameters used by the affine graph.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

abbrev Flat (d : ℕ) := { S : Submodule K V // Module.finrank K S = d }
abbrev VPoint := Flat K V 1
abbrev VPlane := Flat K V 2
abbrev VFlag := VPlane K V × Option K

instance [Finite V] (d : ℕ) : Fintype (Flat K V d) := by
  haveI : Finite (Submodule K V) :=
    Finite.of_injective (fun S : Submodule K V => (S : Set V)) SetLike.coe_injective
  exact Fintype.ofFinite _

variable {K V}

theorem flat_nonempty {d : ℕ} (h : d ≤ Module.finrank K V) : Nonempty (Flat K V d) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank h
  exact ⟨⟨_, (finrank_span_eq_card hf).trans (Fintype.card_fin _)⟩⟩

variable [Finite V]

def planeChart (P : VPlane K V) : (Fin 2 → K) ≃ₗ[K] P.1 :=
  LinearEquiv.ofFinrankEq _ _ (by simp [P.2])

private def ray : Option K → Fin 2 → K
  | none => ![0, 1]
  | some t => ![1, t]

private theorem ray_ne_zero (d : Option K) : ray d ≠ 0 := by
  intro h
  cases d with
  | none => simpa [ray] using congrFun h 1
  | some t => simpa [ray] using congrFun h 0

def dir (P : VPlane K V) (d : Option K) : VPoint K V :=
  ⟨Submodule.span K {((planeChart P (ray d) : P.1) : V)}, finrank_span_singleton (by
    simpa using (planeChart P).map_ne_zero_iff.mpr (ray_ne_zero d))⟩

def flagPoint (i : VFlag K V) : VPoint K V := dir i.1 i.2

theorem dir_le (P : VPlane K V) (d : Option K) : (dir P d).1 ≤ P.1 :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr (planeChart P (ray d)).2

theorem mem_dir (P : VPlane K V) (d : Option K) (w : Fin 2 → K) :
    (planeChart P w : V) ∈ (dir P d).1 ↔ projection w d = 0 := by
  change (planeChart P w : V) ∈ Submodule.span K {(planeChart P (ray d) : V)} ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have eq : c • ray d = w := (planeChart P).injective (by
      rw [map_smul]
      exact Subtype.ext hc)
    rw [← eq]
    cases d <;> simp [projection, ray, mul_comm]
  · intro h
    suffices ∃ c : K, c • ray d = w by
      obtain ⟨c, rfl⟩ := this
      exact ⟨c, by simp⟩
    cases d with
    | none =>
      refine ⟨w 1, ?_⟩
      funext i
      fin_cases i <;> simp [ray, show w 0 = 0 from h]
    | some s =>
      refine ⟨w 0, ?_⟩
      funext i
      have hh : w 1 = s * w 0 := sub_eq_zero.mp h
      fin_cases i <;> simp [ray, hh, mul_comm]

theorem dir_injective (P : VPlane K V) : Function.Injective (dir P) := by
  intro d e he
  have h := (mem_dir P e (ray d)).mp (he ▸ Submodule.mem_span_singleton_self _)
  cases d <;> cases e <;> simp [projection, ray, sub_eq_zero] at *
  assumption

theorem exists_dir (P : VPlane K V) (p : VPoint K V) (h : p.1 ≤ P.1) :
    ∃ d, dir P d = p := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank K p.1 by rw [p.2]; decide)
  let w := (planeChart P).symm ⟨v, h v.2⟩
  have hw : (planeChart P w : V) = v := by simp [w]
  have zero_proj : ∃ d : Option K, projection w d = 0 := by
    by_cases h0 : w 0 = 0
    · exact ⟨none, h0⟩
    · exact ⟨some (w 1 / w 0), by simp [projection, h0]⟩
  obtain ⟨d, hd⟩ := zero_proj
  have hdir : (v : V) ∈ (dir P d).1 := hw ▸ (mem_dir P d w).mpr hd
  have hv' : (v : V) ≠ 0 := fun he => hv (Subtype.ext he)
  have unique (q : VPoint K V) (hq : (v : V) ∈ q.1) : Submodule.span K {(v : V)} = q.1 :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hq)
      ((finrank_span_singleton hv').trans q.2.symm)
  exact ⟨d, Subtype.ext ((unique _ hdir).symm.trans (unique p v.2))⟩

private def planesAt (p : VPoint K V) :
    {i : VFlag K V // flagPoint i = p} ≃
      {S : Submodule K V // Module.finrank K S = 2 ∧ p.1 ≤ S} := by
  let f (i : {i : VFlag K V // flagPoint i = p}) :
      {S : Submodule K V // Module.finrank K S = 2 ∧ p.1 ≤ S} :=
    ⟨i.1.1.1, i.1.1.2, (congrArg Subtype.val i.2).symm.le.trans (dir_le i.1.1 i.1.2)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨⟨P, d⟩, hd⟩ ⟨⟨Q, e⟩, he⟩ h
    have hpq := congrArg Subtype.val h
    have hPQ : P = Q := Subtype.ext hpq
    subst Q
    have hde : d = e := dir_injective P (hd.trans he.symm)
    subst e
    rfl
  · rintro ⟨S, hs, h⟩
    obtain ⟨d, hd⟩ := exists_dir ⟨S, hs⟩ p h
    exact ⟨⟨(⟨S, hs⟩, d), hd⟩, rfl⟩

private theorem same_degree (p q : VPoint K V) :
    Nonempty ({i : VFlag K V // flagPoint i = p} ≃ {i : VFlag K V // flagPoint i = q}) := by
  let f := LinearEquiv.ofFinrankEq p.1 q.1 (p.2.trans q.2.symm)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  let e := Submodule.orderIsoMapComap g
  have he (S : Submodule K V) : Module.finrank K (e S) = Module.finrank K S :=
    g.finrank_map_eq S
  have hm : e p.1 = q.1 := by
    apply Submodule.eq_of_le_of_finrank_eq _ ((he _).trans (p.2.trans q.2.symm))
    rintro _ ⟨x, hx, rfl⟩
    change g x ∈ q.1
    rw [← hg ⟨x, hx⟩]
    exact (f ⟨x, hx⟩).2
  refine ⟨(planesAt p).trans ((e.toEquiv.subtypeEquiv ?_).trans (planesAt q).symm)⟩
  intro S
  change (_ ∧ _) ↔ Module.finrank K (e S) = 2 ∧ q.1 ≤ e S
  rw [he, ← hm, e.le_iff_le]

theorem surjective_flagPoint (h : 2 ≤ Module.finrank K V) :
    Function.Surjective (flagPoint (K := K) (V := V)) := by
  intro p
  obtain ⟨P⟩ := flat_nonempty h
  let i : VFlag K V := (P, none)
  obtain ⟨e⟩ := same_degree (flagPoint i) p
  exact ⟨_, (e ⟨i, rfl⟩).2⟩

variable (K V)

def projectiveDegree := Nat.card (VFlag K V) / Nat.card (VPoint K V)

variable {K V} [Fintype K]

theorem projective_point_degree [DecidableEq (VPoint K V)] (p : VPoint K V) :
    #{i : VFlag K V | flagPoint i = p} = projectiveDegree K V := by
  have eqn (q : VPoint K V) : #{i : VFlag K V | flagPoint i = q} =
      #{i : VFlag K V | flagPoint i = p} := by
    obtain ⟨e⟩ := same_degree q p
    simpa only [Fintype.card_subtype] using Fintype.card_congr e
  have h := sum_fiberwise univ (flagPoint (K := K) (V := V)) (fun _ => 1 : VFlag K V → ℕ)
  simp only [card_univ, eqn, sum_const, smul_eq_mul, mul_one] at h
  have : Nonempty (VPoint K V) := ⟨p⟩
  rw [projectiveDegree, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← h,
    Nat.mul_div_cancel_left _ Fintype.card_pos]

theorem projective_plane_degree [DecidableEq (VPlane K V)] (P : VPlane K V) :
    #{i : VFlag K V | i.1 = P} = Fintype.card K + 1 := by
  rw [← Fintype.card_subtype, ← Fintype.card_option]
  apply Fintype.card_congr
  exact { toFun := fun i => i.1.2
          invFun := fun d => ⟨(P, d), rfl⟩
          left_inv := fun i => Subtype.ext (Prod.ext i.2.symm rfl)
          right_inv := fun _ => rfl }

theorem projective_incidence [DecidableEq (VPlane K V)] {Y : Type*} [MetricSpace Y]
    (C : Comparison Y) (x : VPoint K V → Y) (y : VPlane K V → Y) (o : Y)
    (hq : 100 ≤ Fintype.card K)
    (h : SecantBound flagPoint Prod.fst x o (projectiveDegree K V - 1)) :
    9 * (∑ i, (dist o (x (flagPoint i)) ^ 2 + dist o (y i.1) ^ 2)) ≤
      10 * ∑ i, dist (x (flagPoint i)) (y i.1) ^ 2 := by
  classical
  refine incidence_bound C flagPoint Prod.fst x y o (Nat.succ_pos _)
    projective_point_degree projective_plane_degree ?_ h
  rw [Nat.mul_comm 100]
  exact Nat.mul_le_mul (Nat.sub_le _ _) (le_trans hq (Nat.le_succ _))

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# Affine partitions from independent evaluations

The linear map is an auxiliary address coordinate and varies independently
in every fiber. Independence of the parameters makes the joint name map
surjective. Its kernel supplies the residual product coordinate.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped Classical

variable {J : Type} (k V : Type) (X C U R : J → Type)
  [Field k] [AddCommGroup V] [Module k V]
  [∀ i, AddCommGroup (U i)] [∀ i, Module k (U i)]

private abbrev Point (V : Type) := Fin 2 → V

private abbrev AddressFromPartitionsAffine (k V W : Type) [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] := Point W × (V →ₗ[k] W)

/-- Coordinates for a plane, with base, plane position, linear map and spare label. -/
abbrev PlaneChart := ∀ i, X i ≃ C i × (AddressFromPartitionsAffine k V (U i) × R i)

namespace PlaneChart

variable {k V X C U R} (s : PlaneChart k V X C U R)

def base (i : J) (x : X i) := (s i x).1

def origin (i : J) (x : X i) : C i × (Fin 2 → U i) := (s.base i x, (s i x).2.1.1)

/-- The inverse shear evaluates the affine name at a given address. -/
def shear (p : Fin 2 → V) (i : J) : Equiv.Perm (X i) :=
  (s i).symm.permCongr ((Equiv.refl _).prodCongr
    ((Equiv.prodCongrLeft (fun u : V →ₗ[k] U i => Equiv.subRight (fun j => u (p j)))).prodCongr
      (Equiv.refl _)))

theorem shear_mem (p : Fin 2 → V) : s.shear p ∈ preserving s.base := by
  intro i x
  simp [shear, base]

private theorem origin_shear (p : Point V) (i : J) (x : X i) :
    s.origin i ((s.shear p i).symm x) =
      (s.base i x, fun j => (s i x).2.1.1 j + (s i x).2.1.2 (p j)) := by
  let y := s i x
  change s.origin i ((s i).symm
    (y.1, ((fun j => y.2.1.1 j + y.2.1.2 (p j)), y.2.1.2), y.2.2)) = _
  simp only [origin, base, Equiv.apply_symm_apply, y]

def projected (t : Option k) (i : J) (x : X i) :=
  (s.base i x, projection (s i x).2.1.1 t)

theorem shear_line (p q : Fin 2 → V) (t : Option k) (h : projection p t = projection q t) :
    (s.shear p)⁻¹ * s.shear q ∈ preserving (s.projected t) := by
  intro i x
  have aux (r : Point V) (y : X i) :
      s.projected t i ((s.shear r i).symm y) =
        (s.base i y, projection (s i y).2.1.1 t + (s i y).2.1.2 (projection r t)) := by
    change ((s.origin i _).1, projection (s.origin i _).2 t) = _
    rw [origin_shear]
    cases t with
    | none => rfl
    | some t =>
      simp only [projection, smul_add, map_sub, map_smul]
      congr 1
      abel
  change s.projected t i ((s.shear p i).symm (s.shear q i x)) = _
  rw [aux, h, ← aux, Equiv.symm_apply_apply]

private abbrev Draw (d : ℕ) (W : Type) := Fin d → Point W
private abbrev Sample (d : ℕ) := (Fin d ⊕ Fin d) × Fin 2

variable {d : ℕ}

private def coordinates : Draw d V × Draw d V ≃ (Sample d → V) :=
  (Equiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin d => Point V)).symm.trans
    (Equiv.curry _ _ _).symm

variable {W : Type} [AddCommGroup W] [Module k W]

private def names (p : Draw d V) : AddressFromPartitionsAffine k V W →+ Draw d W where
  toFun x i j := x.1 j + x.2 (p i j)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [add_add_add_comm]

private def joint (p : Draw d V × Draw d V) : AddressFromPartitionsAffine k V W →+ Draw d W × Draw d W :=
  (names p.1).prod (names p.2)

private theorem joint_surj (p : Draw d V × Draw d V)
    (h : LinearIndependent k (coordinates p)) :
    Function.Surjective (joint (k := k) (W := W) p) := by
  intro y
  let b := Module.Basis.span h
  obtain ⟨f, hf⟩ := (b.constr k (coordinates y)).exists_extend
  have he (i : Sample d) : f (coordinates p i) = coordinates y i := by
    have hi := DFunLike.congr_fun hf (b i)
    rw [b.constr_basis] at hi
    simpa [b] using hi
  refine ⟨(0, f), Prod.ext ?_ ?_⟩
  · funext i j
    change 0 + f (p.1 i j) = y.1 i j
    rw [zero_add]
    exact he (.inl i, j)
  · funext i j
    change 0 + f (p.2 i j) = y.2 i j
    rw [zero_add]
    exact he (.inr i, j)

private noncomputable def split {A B : Type} [AddGroup A] [AddGroup B]
    (f : A →+ B) (hf : Function.Surjective f) : A ≃ B × f.ker :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (AddMonoidHom.fiberEquivKerOfSurjective hf))

variable [Fintype V] [∀ i, Fintype (U i)] [∀ i, Fintype (R i)]

variable {G : Type} [Group G] (M : PermSystem X G)

private theorem independent_bridges (p : Draw d V × Draw d V)
    (h : LinearIndependent k (coordinates p)) :
    Bridges (M.pull (preserving s.origin)) (M.pull (preserving s.base)) (M.fixed ∘ s.shear ∘ p.1) (M.fixed ∘ s.shear ∘ p.2) := by
  let A i := Draw d (U i)
  let B i := A i × ((joint (k := k) (W := U i) p).ker × R i)
  have (i : J) : Finite (V →ₗ[k] U i) :=
    Finite.of_injective (fun f : V →ₗ[k] U i => (f : V → U i)) DFunLike.coe_injective
  let (i : J) : Fintype (B i) := Fintype.ofFinite _
  let e (i : J) : X i ≃ C i × (A i × B i) := (s i).trans ((Equiv.refl _).prodCongr
    ((((split _ (joint_surj (W := U i) p h)).prodCongr (Equiv.refl _)).trans
      (Equiv.prodAssoc _ _ _)).trans (Equiv.prodAssoc _ _ _)))
  apply M.bridges_of_product s.base s.origin _ _ e (fun _ _ => rfl)
  · intro j i x y hb ha
    simp only [Function.comp_apply, origin_shear]
    exact Prod.ext hb (congrFun ha j)
  · intro j i x y hb ha
    simp only [Function.comp_apply, origin_shear]
    exact Prod.ext hb (congrFun (congrArg Prod.fst ha) j)

/-- At least half of all pairs of lists can be matched with a third list.
The same affine parameters work for every instance and every base fiber. -/
theorem half_bridges [Fintype k] (hd : 4 * d < Module.finrank k V) :
    Fintype.card ((Fin d → Fin 2 → V) × (Fin d → Fin 2 → V)) ≤
      2 * (Finset.univ.filter fun p : (Fin d → Fin 2 → V) × (Fin d → Fin 2 → V) =>
        Bridges (M.pull (preserving s.origin)) (M.pull (preserving s.base)) (M.fixed ∘ s.shear ∘ p.1) (M.fixed ∘ s.shear ∘ p.2)).card := by
  have hdim : Fintype.card (Sample d) < Module.finrank k V := by
    simp only [Sample, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
    omega
  rw [Fintype.card_congr (coordinates (d := d) (V := V))]
  refine (half_independent k V _ hdim).trans (Nat.mul_le_mul_left 2 ?_)
  apply Finset.card_le_card_of_injOn (coordinates (d := d) (V := V)).symm
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact independent_bridges s M _ (by simpa using hv)
  · exact (coordinates (d := d) (V := V)).symm.injective.injOn

theorem half_bridges_one [Fintype k] (hd : 4 < Module.finrank k V) :
    Fintype.card ((Fin 2 → V) × (Fin 2 → V)) ≤
      2 * (Finset.univ.filter fun p : (Fin 2 → V) × (Fin 2 → V) =>
        Bridges (M.pull (preserving s.origin)) (M.pull (preserving s.base))
          (fun _ : Fin 1 => M.fixed (s.shear p.1)) (fun _ => M.fixed (s.shear p.2))).card := by
  let u := Equiv.funUnique (Fin 1) (Fin 2 → V)
  rw [← Fintype.card_congr (u.prodCongr u)]
  refine (s.half_bridges M (d := 1) hd).trans (Nat.mul_le_mul_left 2 ?_)
  apply Finset.card_le_card_of_injOn (u.prodCongr u)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have he (x : Fin 1 → Fin 2 → V) : M.fixed ∘ s.shear ∘ x = fun _ => M.fixed (s.shear (u x)) := by
      funext i
      rw [Subsingleton.elim i default]
      rfl
    rw [he, he] at hp
    exact hp
  · exact (u.prodCongr u).injective.injOn

end PlaneChart
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# A secant-preserving affine chart of finite projective space

Choose three linear functionals successively, avoiding finitely many
hyperplanes at each step. The first does not vanish on representatives,
the second separates their normalized first coordinates, and the third
rules out spurious incidences.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite V]

private theorem point_le_point {p q : VPoint K V} (h : p.1 ≤ q.1) : p = q :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_eq h (p.2.trans q.2.symm))

private theorem sup_rank (p q : VPoint K V) (h : p ≠ q) :
    Module.finrank K ↥(p.1 ⊔ q.1) = 2 := by
  have hlt : p.1 ⊓ q.1 < p.1 :=
    lt_of_le_of_ne inf_le_left (fun e => h (point_le_point (e.symm.le.trans inf_le_right)))
  have hint := Submodule.finrank_lt_finrank_of_lt hlt
  have he := Submodule.finrank_sup_add_finrank_inf_eq p.1 q.1
  rw [p.2] at hint he
  rw [q.2] at he
  omega

theorem joining_plane (p q : VPoint K V) (h : p ≠ q) :
    ∃! P : VPlane K V, p.1 ≤ P.1 ∧ q.1 ≤ P.1 := by
  have hr := sup_rank p q h
  refine ⟨⟨_, hr⟩, ⟨le_sup_left, le_sup_right⟩, fun P hP => ?_⟩
  exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq (sup_le hP.1 hP.2) (hr.trans P.2.symm)).symm

private theorem exists_rep (p : VPoint K V) :
    ∃ v : V, v ≠ 0 ∧ Submodule.span K {v} = p.1 := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank K p.1 by rw [p.2]; decide)
  have hv' : (v : V) ≠ 0 := fun e => hv (Subtype.ext e)
  exact ⟨v, hv', Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem _ _).mpr v.2) ((finrank_span_singleton hv').trans p.2.symm)⟩

private def rep (p : VPoint K V) : V := (exists_rep p).choose

private theorem rep_mem (p : VPoint K V) (S : Submodule K V) :
    rep p ∈ S ↔ p.1 ≤ S := by
  rw [← (exists_rep p).choose_spec.2, Submodule.span_singleton_le_iff_mem]
  rfl

variable (F : Type*) [Field F] [Algebra K F]

private def evalRep (p : VPoint K V) : Module.Dual F (V →ₗ[K] F) where
  toFun f := f (rep p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem separate (p : VPoint K V) (S : Submodule K V) (h : ¬ p.1 ≤ S) :
    ∃ f : V →ₗ[K] F, evalRep F p f ≠ 0 ∧ S ≤ f.ker := by
  have hn := mt (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S (rep p)).mp
    (mt (rep_mem p S).mp h)
  push Not at hn
  obtain ⟨f, hf, hne⟩ := hn
  refine ⟨(Algebra.linearMap K F).comp f, ?_, ?_⟩
  · exact (map_ne_zero (algebraMap K F)).mpr hne
  · intro v hv
    change algebraMap K F (f v) = 0
    rw [(Submodule.mem_dualAnnihilator f).mp hf v hv, map_zero]

variable [Infinite F]

private theorem chart_abscissa :
    ∃ f g : V →ₗ[K] F, (∀ p : VPoint K V, f (rep p) ≠ 0) ∧
      Function.Injective (fun p : VPoint K V => g (rep p) / f (rep p)) := by
  have hn (p : VPoint K V) : ∃ f, evalRep F p f ≠ 0 := by
    obtain ⟨f, hf, _⟩ := separate F p ⊥ (fun h =>
      (exists_rep p).choose_spec.1 ((rep_mem p ⊥).mpr h))
    exact ⟨f, hf⟩
  obtain ⟨f, hf⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists (evalRep F) hn
  let u (p : VPoint K V) := (f (rep p))⁻¹ • evalRep F p
  have hu (p : VPoint K V) (a : V →ₗ[K] F) : u p a = a (rep p) / f (rep p) := by
    simp [u, evalRep, div_eq_inv_mul]
  let D := {pq : VPoint K V × VPoint K V // pq.1 ≠ pq.2}
  let m (i : D) := u i.1.1 - u i.1.2
  have hm (i : D) : ∃ a, m i a ≠ 0 := by
    obtain ⟨⟨p, q⟩, hpq⟩ := i
    obtain ⟨a, ha, hz⟩ := separate F p q.1 (fun h => hpq (point_le_point h))
    have hz' : a (rep q) = 0 := hz ((rep_mem q _).mpr le_rfl)
    refine ⟨a, ?_⟩
    change u p a - u q a ≠ 0
    rw [hu, hu, hz', zero_div, sub_zero]
    exact div_ne_zero ha (hf p)
  obtain ⟨g, hg⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists m hm
  refine ⟨f, g, hf, fun p q h => ?_⟩
  by_contra hn
  apply hg ⟨(p, q), hn⟩
  exact sub_eq_zero.mpr ((hu p g).trans (h.trans (hu q g).symm))

/-- A generic affine chart containing all the marked points. -/
theorem projective_chart :
    ∃ (a : VPoint K V → Fin 2 → F) (l : VPlane K V → Option F × F),
      Function.Injective a ∧ Function.Injective l ∧
      ∀ p P, projection (a p) (l P).1 = (l P).2 ↔ p.1 ≤ P.1 := by
  obtain ⟨f, g, hf, hg⟩ := chart_abscissa (K := K) (V := V) F
  let u (p : VPoint K V) := g (rep p) / f (rep p)
  let v (p : VPoint K V) := (f (rep p))⁻¹ • evalRep F p
  have hv (p : VPoint K V) (h : V →ₗ[K] F) : v p h = h (rep p) / f (rep p) := by
    simp [v, evalRep, div_eq_inv_mul]
  let p₀ (P : VPlane K V) := dir P none
  let p₁ (P : VPlane K V) := dir P (some 0)
  have ne (P : VPlane K V) : p₀ P ≠ p₁ P := (dir_injective P).ne (by simp)
  let s (P : VPlane K V) := (u (p₀ P) - u (p₁ P))⁻¹ • (v (p₀ P) - v (p₁ P))
  let b (P : VPlane K V) := v (p₀ P) - u (p₀ P) • s P
  let test (p : VPoint K V) (P : VPlane K V) := v p - u p • s P - b P
  let D := {i : VPoint K V × VPlane K V // ¬ i.1.1 ≤ i.2.1}
  have ht (i : D) : ∃ h, test i.1.1 i.1.2 h ≠ 0 := by
    obtain ⟨⟨p, P⟩, hn⟩ := i
    obtain ⟨h, hp, hP⟩ := separate F p P.1 hn
    have h₀ : h (rep (p₀ P)) = 0 := hP ((rep_mem _ _).mpr (dir_le P none))
    have h₁ : h (rep (p₁ P)) = 0 := hP ((rep_mem _ _).mpr (dir_le P (some 0)))
    refine ⟨h, ?_⟩
    simpa [test, b, s, hv, h₀, h₁] using div_ne_zero (show h (rep p) ≠ 0 from hp) (hf p)
  obtain ⟨h, hh⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun i : D => test i.1.1 i.1.2) ht
  have eqn (p : VPoint K V) (P : VPlane K V) :
      v p h - s P h * u p = b P h ↔ p.1 ≤ P.1 := by
    constructor
    · intro he
      by_contra hn
      apply hh ⟨(p, P), hn⟩
      change v p h - u p * s P h - b P h = 0
      rw [mul_comm (u p), he, sub_self]
    · intro hp
      let k := h - s P h • g - b P h • f
      have iff_ker (q : VPoint K V) :
          v q h - s P h * u q = b P h ↔ q.1 ≤ k.ker := by
        rw [← rep_mem, hv]
        change h (rep q) / f (rep q) - s P h * (g (rep q) / f (rep q)) = b P h ↔
          h (rep q) - s P h * g (rep q) - b P h * f (rep q) = 0
        rw [← mul_div_assoc, ← sub_div, div_eq_iff (hf q), sub_eq_zero]
      have h₀ : (p₀ P).1 ≤ k.ker := (iff_ker _).mp (by simp [b, mul_comm])
      have h₁ : (p₁ P).1 ≤ k.ker := by
        apply (iff_ker _).mp
        have he : (u (p₀ P) - u (p₁ P)) * s P h = v (p₀ P) h - v (p₁ P) h := by
          have hn : u (p₀ P) - u (p₁ P) ≠ 0 := sub_ne_zero.mpr (hg.ne (ne P))
          simp [s, hn]
        change v (p₁ P) h - s P h * u (p₁ P) = v (p₀ P) h - u (p₀ P) * s P h
        linear_combination he
      apply (iff_ker _).mpr
      have hs : (p₀ P).1 ⊔ (p₁ P).1 = P.1 :=
        Submodule.eq_of_le_of_finrank_eq (sup_le (dir_le P none) (dir_le P (some 0)))
          ((sup_rank _ _ (ne P)).trans P.2.symm)
      rw [← hs] at hp
      exact hp.trans (sup_le h₀ h₁)
  let a (p : VPoint K V) := ![u p, v p h]
  let l (P : VPlane K V) := (some (s P h), b P h)
  have iff_mem (p : VPoint K V) (P : VPlane K V) :
      projection (a p) (l P).1 = (l P).2 ↔ p.1 ≤ P.1 := eqn p P
  refine ⟨a, l, fun _ _ he => hg (congrFun he 0), ?_, iff_mem⟩
  intro P Q he
  have hm (d : Option K) : (dir P d).1 ≤ Q.1 := by
    rw [← iff_mem, ← he, iff_mem]
    exact dir_le P d
  exact (joining_plane _ _ (ne P)).unique ⟨dir_le P none, dir_le P (some 0)⟩
    ⟨hm none, hm (some 0)⟩

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Plane actions on address families

Write ordinary addresses as lists of vectors. For each vector plane,
choose a complement and express every vector in the associated coordinates.
The partition names then recover the motion subgroups for the plane,
the zero subspace, and its individual directions.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {J : Type} (k W : Type) [Field k] [AddCommGroup W] [Module k W]
  (I R : J → Type)

abbrev Aux (j : J) := (W →ₗ[k] I j → k) × R j

instance auxFintype [Fintype k] [Fintype W] [∀ j, Fintype (I j)]
    [∀ j, Fintype (R j)] (j : J) : Fintype (Aux k W I R j) := by
  haveI : Finite (W →ₗ[k] I j → k) :=
    Finite.of_injective (fun f : W →ₗ[k] I j → k => (f : W → I j → k)) DFunLike.coe_injective
  exact Fintype.ofFinite _

variable {k W} {V : Type} [AddCommGroup V] [Module k V] [Fintype V]

private def planeCoords (P : VPlane k V) (T : Submodule k V) (hT : IsCompl T P.1) :
    V ≃ₗ[k] T × (Fin 2 → k) :=
  (T.prodEquivOfIsCompl P.1 hT).symm.trans
    ((LinearEquiv.refl k T).prodCongr (planeChart P).symm)

private theorem plane_mem (P : VPlane k V) (T : Submodule k V) (hT : IsCompl T P.1)
    (x y : V) : (planeCoords P T hT x).1 = (planeCoords P T hT y).1 ↔ x - y ∈ P.1 := by
  rw [← sub_eq_zero, ← Prod.fst_sub, ← map_sub]
  exact Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero T P.1 hT

private def chartLabels {T : Type} (c : V ≃ T × (Fin 2 → k)) :
    PlaneChart k W (Labels V I (Aux k W I R)) (fun j => I j → T) (fun j => I j → k) R :=
  fun j =>
    { toFun := fun x => (fun i => (c (x.1 i)).1, ((fun t i => (c (x.1 i)).2 t), x.2.1), x.2.2)
      invFun := fun y => (fun i => c.symm (y.1 i, fun t => y.2.1.1 t i), y.2.1.2, y.2.2)
      left_inv := by intro x; simp
      right_inv := by intro x; simp }

theorem PermSystem.motion_plane_action [Fintype k] [Fintype W] [∀ j, Fintype (I j)]
    [∀ j, Fintype (R j)] {G : Type} [Group G]
    (M : PermSystem (Labels V I (Aux k W I R)) G) (P : VPlane k V) (hW : 4 < Module.finrank k W) :
    ∃ σ, PlaneAction (M.pull (motion I (Aux k W I R) (⊥ : Submodule k V)))
      (M.pull (motion I (Aux k W I R) P.1)) (fun t => M.pull (motion I (Aux k W I R) (dir P t).1))
      (affineGraph (K := k) (V := W)) σ := by
  classical
  obtain ⟨T, hT⟩ := P.1.exists_isCompl
  let c := planeCoords P T hT.symm
  let s := chartLabels (W := W) I R c.toEquiv
  have hP : preserving s.base = motion I (Aux k W I R) P.1 := by
    ext g
    constructor
    · intro hg j x i
      exact (plane_mem P T hT.symm _ _).mp (congrFun (hg j x) i)
    · intro hg j x
      funext i
      exact (plane_mem P T hT.symm _ _).mpr (hg j x i)
  have h0 : preserving s.origin = motion I (Aux k W I R) (⊥ : Submodule k V) := by
    ext g
    constructor
    · intro hg j x i
      rw [Submodule.mem_bot, sub_eq_zero]
      apply c.injective
      exact Prod.ext (congrFun (congrArg Prod.fst (hg j x)) i)
        (funext fun t => congrFun (congrFun (congrArg Prod.snd (hg j x)) t) i)
    · intro hg j x
      have hx : (g j x).1 = x.1 := funext fun i => sub_eq_zero.mp (hg j x i)
      exact congrArg (fun y => (fun i => (c (y i)).1, fun t i => (c (y i)).2 t)) hx
  have hL (t : Option k) : preserving (s.projected t) ≤ motion I (Aux k W I R) (dir P t).1 := by
    intro g hg j x i
    let u := (g j x).1 i
    let v := x.1 i
    have hm := (plane_mem P T hT.symm u v).mp (congrFun (congrArg Prod.fst (hg j x)) i)
    let z : P.1 := ⟨u - v, hm⟩
    have hz : (c (u - v)).2 = (planeChart P).symm z := by
      change (planeChart P).symm ((T.prodEquivOfIsCompl P.1 hT.symm).symm (z : V)).2 = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
    have hp : projection (c u).2 t = projection (c v).2 t := by
      have hp := congrFun (congrArg Prod.snd (hg j x)) i
      cases t <;> exact hp
    have h : projection ((planeChart P).symm z) t = 0 := by
      rw [← hz, map_sub, Prod.snd_sub]
      cases t <;> simp only [projection, Pi.sub_apply, smul_sub] at hp ⊢
      · exact sub_eq_zero.mpr hp
      · linear_combination hp
    simpa only [LinearEquiv.apply_symm_apply] using (mem_dir P t _).mpr h
  refine ⟨M.fixed ∘ s.shear, ?_, ?_, ?_⟩
  · intro a t
    rw [Function.comp_apply, M.read_fixed, ← hP]
    exact s.shear_mem a
  · intro a a' d d' h
    obtain ⟨rfl, hp⟩ := Prod.mk.inj h
    refine ⟨rfl, fun t => ?_⟩
    simp only [map_mul, map_inv, Function.comp_apply, M.read_fixed]
    exact hL d (s.shear_line a a' d hp)
  · rw [← h0, ← hP]
    exact s.half_bridges_one M hW

theorem motion_plane_action [Fintype k] [Fintype W] [∀ j, Fintype (I j)]
    [∀ j, Fintype (R j)] (P : VPlane k V) (hW : 4 < Module.finrank k W) :
    ∃ σ, PlaneAction (motion I (Aux k W I R) (⊥ : Submodule k V))
      (motion I (Aux k W I R) P.1) (fun t => motion I (Aux k W I R) (dir P t).1)
      (affineGraph (K := k) (V := W)) σ := by
  simpa only [PermSystem.full_pull] using
    PermSystem.motion_plane_action I R (PermSystem.full (Labels V I (Aux k W I R))) P hW

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-! Incidence of affine points with lines in the base-field directions. -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private def affineParam (k : Option K × V) (v : V) : Fin 2 → V :=
  match k.1 with
  | none => ![k.2, v]
  | some s => ![v, k.2 + s • v]

private def affineCoord (a : Fin 2 → V) : Option K → V
  | none => a 1
  | some _ => a 0

private def affineFiber (k : Option K × V) :
    V ≃ {i : (Fin 2 → V) × Option K // affineGraph i = k} where
  toFun v := ⟨(affineParam k v, k.1), by
    rcases k with ⟨_ | s, b⟩ <;> simp [affineGraph, projection, affineParam]⟩
  invFun i := affineCoord i.1.1 i.1.2
  left_inv v := by rcases k with ⟨_ | s, b⟩ <;> rfl
  right_inv i := by
    rcases i with ⟨⟨a, d⟩, rfl⟩
    refine Subtype.ext (Prod.ext ?_ rfl)
    funext j
    cases d <;> fin_cases j <;> simp [affineParam, affineGraph, projection, affineCoord]

variable [Fintype K] [Fintype V] [DecidableEq K] [DecidableEq V]

theorem affine_line_degree (k : Option K × V) :
    #{i | affineGraph i = k} = Fintype.card V := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (affineFiber k).symm

omit [Field K] [AddCommGroup V] [Module K V] [DecidableEq K] in
theorem affine_point_degree (a : Fin 2 → V) :
    #{i : (Fin 2 → V) × Option K | i.1 = a} = Fintype.card K + 1 := by
  rw [← Fintype.card_subtype, ← Fintype.card_option]
  apply Fintype.card_congr
  exact { toFun := fun i => i.1.2
          invFun := fun d => ⟨(a, d), rfl⟩
          left_inv := fun i => Subtype.ext (Prod.ext i.2.symm rfl)
          right_inv := fun _ => rfl }

theorem affine_incidence {Y : Type*} [MetricSpace Y] (C : Comparison Y)
    (x : (Fin 2 → V) → Y) (y : Option K × V → Y) (o : Y)
    (hq : 100 ≤ Fintype.card K)
    (h : SecantBound Prod.fst (affineGraph (K := K)) x o (Fintype.card V)) :
    9 * (∑ i, (dist o (x i.1) ^ 2 + dist o (y (affineGraph i)) ^ 2)) ≤
      10 * ∑ i, dist (x i.1) (y (affineGraph i)) ^ 2 := by
  refine incidence_bound C Prod.fst affineGraph x y o Fintype.card_pos
    affine_point_degree affine_line_degree ?_ h
  exact Nat.mul_le_mul_right _ (le_trans hq (Nat.le_add_right _ _))

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! Both incidence estimates follow from the same secant bound. -/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset
open scoped Classical

variable {K : Type} [Field K] [Fintype K]
variable {F Y : Type*} [Field F] [MetricSpace Y]

theorem Secants.projective_widths {V : Type} [AddCommGroup V] [Module K V] [Finite V]
    [Infinite F] [Algebra K F] (S : Secants F Y) (x : VPoint K V → Y) (o : Y)
    (ho : Bary x o) : SecantBound flagPoint Prod.fst x o (projectiveDegree K V - 1) := by
  obtain ⟨a, k, ha, hk, hc⟩ := projective_chart (K := K) (V := V) F
  have hmem (P : VPlane K V) : k P ∈ secantLines a := by
    apply (mem_secantLines ha _).mpr
    exact ⟨dir P none, dir P (some 0), (dir_injective P).ne (by simp),
      (hc _ _).mpr (dir_le _ _), (hc _ _).mpr (dir_le _ _)⟩
  have hfull (b : Option F × F) (hb : b ∈ secantLines a) : ∃ P, k P = b := by
    obtain ⟨i, j, hij, hi, hj⟩ := (mem_secantLines ha b).mp hb
    obtain ⟨P, ⟨hiP, hjP⟩, _⟩ := joining_plane i j hij
    refine ⟨P, ?_⟩
    rw [eq_through (ha.ne hij) hi hj]
    exact eq_through (ha.ne hij) ((hc _ _).mpr hiP) ((hc _ _).mpr hjP)
  have hi (p : VPoint K V) (P : VPlane K V) :
      projection (a p) (k P).1 = (k P).2 ↔ ∃ i, flagPoint i = p ∧ i.1 = P := by
    rw [hc]
    constructor
    · intro h
      obtain ⟨d, hd⟩ := exists_dir P p h
      exact ⟨(P, d), hd, rfl⟩
    · rintro ⟨⟨P, d⟩, rfl, rfl⟩
      exact dir_le _ _
  have hn (p : VPoint K V) : (pointSecants a p).card ≤ projectiveDegree K V - 1 + 1 := by
    let T := ({i : VFlag K V | flagPoint i = p} : Finset _)
    have hT : pointSecants a p ⊆ T.image (fun i => k i.1) := by
      intro b hb
      obtain ⟨hb, hp⟩ := mem_filter.mp hb
      obtain ⟨P, rfl⟩ := hfull b hb
      obtain ⟨i, hip, rfl⟩ := (hi p P).mp hp
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hip⟩, rfl⟩
    have ht := (card_le_card hT).trans card_image_le
    rw [show T.card = _ from projective_point_degree p] at ht
    omega
  have he : Function.Injective (fun i : VFlag K V => (flagPoint i, i.1)) := by
    rintro ⟨P, d⟩ ⟨Q, e⟩ h
    have hPQ : P = Q := congrArg Prod.snd h
    subst Q
    have hde : d = e := dir_injective P (congrArg Prod.fst h)
    exact Prod.ext rfl hde
  exact S.widths a k ha hk hn hmem flagPoint Prod.fst he hi x o ho

theorem Secants.projective {V : Type} [AddCommGroup V] [Module K V] [Finite V]
    [Infinite F] [Algebra K F] (S : Secants F Y) (C : Comparison Y)
    (hq : 100 ≤ Fintype.card K) : Incidence Y (flagPoint (K := K) (V := V)) Prod.fst := by
  exact fun x y o ho => projective_incidence C x y o hq (S.projective_widths x o ho)

theorem Secants.affine_widths {W : Type} [Field W] [Fintype W] [Algebra K W] [Algebra W F]
    (S : Secants F Y) (x : (Fin 2 → W) → Y) (o : Y) (ho : Bary x o) :
    SecantBound Prod.fst (affineGraph (K := K)) x o (Fintype.card W) := by
  let f := algebraMap W F
  let g := algebraMap K W
  let a (w : Fin 2 → W) (i : Fin 2) := f (w i)
  let k (l : Option K × W) := (l.1.map (f ∘ g), f l.2)
  have ha : Function.Injective a := fun _ _ h => funext fun i => f.injective (congrFun h i)
  have hk : Function.Injective k := by
    intro i j h
    have hd : i.1.map (f ∘ g) = j.1.map (f ∘ g) := congrArg Prod.fst h
    have hi : f i.2 = f j.2 := congrArg Prod.snd h
    exact Prod.ext (Option.map_injective (f.injective.comp g.injective) hd) (f.injective hi)
  have hc (w : Fin 2 → W) (d : Option K) :
      projection (a w) (d.map (f ∘ g)) = f (projection w d) := by
    cases d <;> simp [a, g, projection, Algebra.smul_def]
  have hi (p : Fin 2 → W) (l : Option K × W) :
      projection (a p) (k l).1 = (k l).2 ↔
        ∃ i, i.1 = p ∧ affineGraph i = l := by
    change projection (a p) (l.1.map (f ∘ g)) = f l.2 ↔ _
    rw [hc, f.injective.eq_iff]
    constructor
    · exact fun h => ⟨(p, l.1), rfl, Prod.ext rfl h⟩
    · rintro ⟨⟨p, d⟩, rfl, rfl⟩
      rfl
  have he : Function.Injective (fun i : (Fin 2 → W) × Option K => (i.1, affineGraph i)) := by
    intro i j h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg (fun v => v.2.1) h
    exact Prod.ext h₁ h₂
  have hmem (l : Option K × W) : k l ∈ secantLines a := by
    have hm : 1 < #{i | affineGraph i = l} := by
      rw [affine_line_degree]
      exact Fintype.one_lt_card
    obtain ⟨i, hi', j, hj, hij⟩ := one_lt_card.mp hm
    replace hi' := (mem_filter.mp hi').2
    replace hj := (mem_filter.mp hj).2
    exact (mem_secantLines ha _).mpr ⟨i.1, j.1,
      fun h => hij (he (Prod.ext h (hi'.trans hj.symm))),
      (hi _ _).mpr ⟨i, rfl, hi'⟩, (hi _ _).mpr ⟨j, rfl, hj⟩⟩
  have hd (u v : Fin 2 → W) : (through (a u) (a v)).1 = (through u v).1.map f := by
    by_cases h : u 0 = v 0
    · simp [through, a, h]
    · simp [through, a, h, f.injective.ne h]
  have hn (p : Fin 2 → W) : (pointSecants a p).card ≤ Fintype.card W + 1 := by
    let line (d : Option W) := (d.map f, projection (a p) (d.map f))
    have hs : pointSecants a p ⊆ univ.image line := by
      intro l hl
      obtain ⟨hl, hp⟩ := mem_filter.mp hl
      obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_image.mp hl
      refine mem_image.mpr ⟨(through i j).1, mem_univ _, ?_⟩
      dsimp only [line]
      rw [← hd, hp]
    simpa using (card_le_card hs).trans card_image_le
  exact S.widths a k ha hk hn hmem Prod.fst affineGraph he hi x o ho

theorem Secants.affine {W : Type} [Field W] [Fintype W] [Algebra K W] [Algebra W F]
    (S : Secants F Y) (C : Comparison Y) (hq : 100 ≤ Fintype.card K) :
    Incidence Y Prod.fst (affineGraph (K := K) (V := W)) := by
  exact fun x y o ho => affine_incidence C x y o hq (S.affine_widths x o ho)

end OAI.LinearAlgebra.MatrixExponent.Routing
end
