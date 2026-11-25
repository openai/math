import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.System
import OAI.LinearAlgebra.MatrixExponent.Routing.PartitionsPlane
import Mathlib.LinearAlgebra.Projection
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometrySharp
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Recipe
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryEfficient
import Mathlib.Tactic.DeriveCountable
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Blueprint
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Padding
import OAI.LinearAlgebra.MatrixExponent.Routing.Dual
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Relabelling the three finite alphabets of a product chart -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open scoped Classical

variable {M : ℕ} {C A D : Type}

private def dim [Fintype C] (f : Fin M → C) (hf : Function.Surjective f) : Fin (M + 1) :=
  ⟨Fintype.card C, Nat.lt_succ_of_le (by simpa using Fintype.card_le_of_surjective _ hf)⟩

def ProductChart.ofEquiv [NeZero M] [Fintype C] [Fintype A] [Fintype D]
    (e : Fin M ≃ C × A × D) : ProductChart M where
  c := dim (fun i => (e i).1) (fun x => ⟨e.symm (x, (e 0).2), by simp⟩)
  a := dim (fun i => (e i).2.1) (fun x => ⟨e.symm ((e 0).1, x, (e 0).2.2), by simp⟩)
  b := dim (fun i => (e i).2.2) (fun x => ⟨e.symm ((e 0).1, (e 0).2.1, x), by simp⟩)
  split := e.trans ((Fintype.equivFin C).prodCongr ((Fintype.equivFin A).prodCongr (Fintype.equivFin D)))

namespace System
variable {G : Type} [Group G] (S : System M G)

def keep (name : Fin M → C) : Subgroup G where
  carrier := {g | ∀ h σ x i, name ((S.read h σ g x).1 i) = name (x.1 i)}
  one_mem' := by simp
  mul_mem' hu hv h σ x i := by rw [map_mul]; exact (hu h σ _ i).trans (hv h σ x i)
  inv_mem' {g} hg h σ x i := by simpa using (hg h σ ((S.read h σ g).symm x) i).symm

theorem factors [NeZero M] [Fintype C] [Fintype A] [Fintype D]
    (e : Fin M ≃ C × A × D) (g : G) (hg : g ∈ S.keep (fun x => (e x).1)) :
    ∃ u v w : G, g = u * v * w ∧
      u ∈ S.keep (fun x => ((e x).1, (e x).2.1)) ∧
      v ∈ S.keep (fun x => ((e x).1, (e x).2.2)) ∧
      w ∈ S.keep (fun x => ((e x).1, (e x).2.1)) := by
  let p := ProductChart.ofEquiv e
  obtain ⟨u, v, w, he, hu, hv, hw⟩ := S.factor p g (fun h σ x =>
    funext fun i => congrArg (Fintype.equivFin C) (hg h σ x i))
  have outer (z : G)
      (hz : ∀ h σ x, (p.apply h (S.read h σ z x)).1 = (p.apply h x).1 ∧
        (p.apply h (S.read h σ z x)).2.1 = (p.apply h x).2.1) :
      z ∈ S.keep (fun x => ((e x).1, (e x).2.1)) := fun h σ x i =>
    Prod.ext ((Fintype.equivFin C).injective (congrFun (hz h σ x).1 i))
      ((Fintype.equivFin A).injective (congrFun (hz h σ x).2 i))
  refine ⟨u, v, w, he, outer u hu, fun h σ x i => ?_, outer w hw⟩
  exact Prod.ext ((Fintype.equivFin C).injective (congrFun (hv h σ x).1 i))
    ((Fintype.equivFin D).injective (congrFun (congrArg Prod.fst (hv h σ x).2) i))

theorem conjugate_keep (name : Fin M → C) (p : Equiv.Perm (Fin M)) (g : G)
    (hg : g ∈ S.keep (name ∘ p.symm)) : (S.fixed p)⁻¹ * (g * S.fixed p) ∈ S.keep name := by
  intro h σ x i
  rw [map_mul, map_mul, map_inv, S.read_fixed]
  have he := hg h σ (digitPerm p h x) i
  change name (p.symm ((S.read h σ g (digitPerm p h x)).1 i)) = name (p.symm (p (x.1 i))) at he
  rw [Equiv.symm_apply_apply] at he
  exact he

end System
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

/-!
# A static affine product chart

Split the joint evaluation map on one finite alphabet. Its residual
kernel is another finite alphabet. Thus no fiber representatives or
linear sections depend on the word length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform

open scoped Classical

abbrev Point (W : Type) := Fin 2 → W

abbrev Face (k W : Type) [Field k] [AddCommGroup W] [Module k W] :=
  Point k × (W →ₗ[k] k)

abbrev Facet (M : ℕ) (k W C : Type) [Field k] [AddCommGroup W] [Module k W] :=
  Fin M ≃ C × Face k W

namespace Facet
variable {M : ℕ} {G k W C : Type} [Group G] [Field k] [AddCommGroup W] [Module k W]
  (s : Facet M k W C)

def base (x : Fin M) := (s x).1
def origin (x : Fin M) := (s.base x, (s x).2.1)
def projected (t : Option k) (x : Fin M) := (s.base x, projection (s x).2.1 t)

def shear (p : Point W) : Equiv.Perm (Fin M) :=
  s.symm.permCongr ((Equiv.refl C).prodCongr
    (Equiv.prodCongrLeft (fun u : W →ₗ[k] k => Equiv.subRight (fun j => u (p j)))))

theorem shear_mem (p : Point W) (x : Fin M) : s.base (s.shear p x) = s.base x := by
  simp [shear, base]

private def names (p : Point W) : Face k W →+ Point k where
  toFun x j := x.1 j + x.2 (p j)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [add_add_add_comm]

private theorem origin_shear (p : Point W) (x : Fin M) :
    s.origin ((s.shear p).symm x) = (s.base x, names p (s x).2) := by
  let y := s x
  change s.origin (s.symm (y.1, (fun j => y.2.1 j + y.2.2 (p j)), y.2.2)) = _
  simp only [origin, base, Equiv.apply_symm_apply, y]
  rfl

theorem shear_line (p q : Point W) (t : Option k) (hp : projection p t = projection q t)
    (x : Fin M) : s.projected t ((s.shear p).symm (s.shear q x)) = s.projected t x := by
  have aux (r : Point W) (y : Fin M) :
      s.projected t ((s.shear r).symm y) =
        (s.base y, projection (s y).2.1 t + (s y).2.2 (projection r t)) := by
    change ((s.origin _).1, projection (s.origin _).2 t) = _
    rw [origin_shear]
    cases t with
    | none => rfl
    | some t =>
      change (_, projection (fun j => (s y).2.1 j + (s y).2.2 (r j)) (some t)) = _
      simp only [projection, smul_add, map_sub, map_smul]
      congr 1
      abel
  rw [aux, hp, ← aux, Equiv.symm_apply_apply]

private def coordinates {A : Type} : Point A × Point A ≃ (Fin 2 ⊕ Fin 2 → A) :=
  (Equiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => A)).symm

private def joint (p : Point W × Point W) : Face k W →+ Point k × Point k :=
  (names p.1).prod (names p.2)

private theorem joint_surj (p : Point W × Point W) (h : LinearIndependent k (coordinates p)) :
    Function.Surjective (joint (k := k) p) := by
  intro y
  let b := Module.Basis.span h
  obtain ⟨f, hf⟩ := (b.constr k (coordinates y)).exists_extend
  have he (i : Fin 2 ⊕ Fin 2) : f (coordinates p i) = coordinates y i := by
    have hi := DFunLike.congr_fun hf (b i)
    rw [b.constr_basis] at hi
    simpa [b] using hi
  refine ⟨(0, f), Prod.ext ?_ ?_⟩
  · funext j
    change 0 + f (p.1 j) = y.1 j
    rw [zero_add]
    exact he (.inl j)
  · funext j
    change 0 + f (p.2 j) = y.2 j
    rw [zero_add]
    exact he (.inr j)

private def split {A B : Type} [AddGroup A] [AddGroup B]
    (f : A →+ B) (hf : Function.Surjective f) : A ≃ B × f.ker :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (AddMonoidHom.fiberEquivKerOfSurjective hf))

variable [NeZero M] [Fintype k] [Fintype W] [Fintype C] (U : System M G)

private theorem independent_bridges (p : Point W × Point W) (h : LinearIndependent k (coordinates p)) :
    Bridges (U.keep s.origin) (U.keep s.base)
      (fun _ : Fin 1 => U.fixed (s.shear p.1)) (fun _ => U.fixed (s.shear p.2)) := by
  have : Finite (W →ₗ[k] k) :=
    Finite.of_injective (fun f : W →ₗ[k] k => (f : W → k)) DFunLike.coe_injective
  let : Fintype (joint (k := k) p).ker := Fintype.ofFinite _
  let e := s.trans ((Equiv.refl C).prodCongr
    ((split _ (joint_surj p h)).trans (Equiv.prodAssoc _ _ _)))
  apply bridges_of_factor
  intro g hg
  obtain ⟨u, v, w, he, hu, hv, hw⟩ := U.factors e g hg
  have outer (z : G) (hz : z ∈ U.keep (fun x => ((e x).1, (e x).2.1))) :
      (U.fixed (s.shear p.1))⁻¹ * (z * U.fixed (s.shear p.1)) ∈ U.keep s.origin := by
    apply U.conjugate_keep
    intro n σ x i
    simp only [Function.comp_apply, origin_shear]
    exact hz n σ x i
  refine ⟨u, v, w, he, fun _ => outer u hu, fun _ => ?_, fun _ => outer w hw⟩
  apply U.conjugate_keep
  intro n σ x i
  simp only [Function.comp_apply, origin_shear]
  exact congrArg (fun a => (a.1, a.2.1)) (hv n σ x i)

theorem half_bridges (hW : 4 < Module.finrank k W) :
    Fintype.card (Point W × Point W) ≤
      2 * (Finset.univ.filter fun p : Point W × Point W =>
        Bridges (U.keep s.origin) (U.keep s.base)
          (fun _ : Fin 1 => U.fixed (s.shear p.1)) (fun _ => U.fixed (s.shear p.2))).card := by
  have hdim : Fintype.card (Fin 2 ⊕ Fin 2) < Module.finrank k W := by simpa using hW
  rw [Fintype.card_congr (coordinates (A := W))]
  refine (half_independent k W _ hdim).trans (Nat.mul_le_mul_left 2 ?_)
  apply Finset.card_le_card_of_injOn (coordinates (A := W)).symm
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact independent_bridges s U _ (by simpa using hv)
  · exact (coordinates (A := W)).symm.injective.injOn

end Facet
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

/-! # Generating the group with motions on static digit charts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.System

open scoped Classical
variable {M : ℕ} {G k V E : Type} [Group G] [Field k] [AddCommGroup V] [Module k V]
  (U : System M G) (d : Fin M ≃ V × E)

def motion (S : Submodule k V) : Subgroup G where
  carrier := {g | ∀ h σ x i, (d ((U.read h σ g x).1 i)).1 - (d (x.1 i)).1 ∈ S}
  one_mem' := by simp
  mul_mem' {g l} hg hl h σ x i := by
    simpa using S.add_mem (hg h σ (U.read h σ l x) i) (hl h σ x i)
  inv_mem' {g} hg h σ x i := by
    simpa using S.neg_mem (hg h σ ((U.read h σ g).symm x) i)

theorem motion_mono {S T : Submodule k V} (h : S ≤ T) : U.motion d S ≤ U.motion d T :=
  fun _ hg n σ x i => h (hg n σ x i)

private def sumChart (S T : Submodule k V) (h : Disjoint S T) :
    S × T ≃ ↥(S ⊔ T) :=
  Equiv.ofBijective (fun p => ⟨p.1 + p.2, Submodule.add_mem_sup p.1.2 p.2.2⟩) (by
    constructor
    · intro x y he
      have eqn : (x.1 : V) + x.2 = (y.1 : V) + y.2 := congrArg Subtype.val he
      have hx : (x.1 : V) - y.1 = (y.2 : V) - x.2 := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm (y.2 : V)]
        exact eqn
      have hz := Submodule.disjoint_def.mp h _ (S.sub_mem x.1.2 y.1.2)
        (hx.symm ▸ T.sub_mem y.2.2 x.2.2)
      exact Prod.ext (Subtype.ext (sub_eq_zero.mp hz))
        (Subtype.ext (sub_eq_zero.mp (hx.symm.trans hz)).symm)
    · intro z
      obtain ⟨s, t, he⟩ := Submodule.mem_sup'.mp z.2
      exact ⟨(s, t), Subtype.ext he⟩)

variable [NeZero M] [Fintype V] [Fintype E]

private theorem motion_sup (S T : Submodule k V) (h : Disjoint S T) :
    U.motion d (S ⊔ T) ≤ U.motion d S ⊔ U.motion d T := by
  obtain ⟨D, hd⟩ := (S ⊔ T).exists_isCompl
  let e := (D.prodEquivOfIsCompl (S ⊔ T) hd.symm).symm
  let f := e.toEquiv.trans ((Equiv.refl D).prodCongr (sumChart S T h).symm)
  let c : Fin M ≃ D × S × (T × E) :=
    d.trans (((f.prodCongr (Equiv.refl E)).trans (Equiv.prodAssoc _ _ _)).trans
      ((Equiv.refl D).prodCongr (Equiv.prodAssoc _ _ _)))
  have read (x : Fin M) : (d x).1 = ((c x).1 : V) + (((c x).2.1 : V) + ((c x).2.2.1 : V)) :=
    (f.symm_apply_apply (d x).1).symm
  intro g hg
  have fixed : g ∈ U.keep (fun x => (c x).1) := by
    intro n σ x i
    change (e (d ((U.read n σ g x).1 i)).1).1 = (e (d (x.1 i)).1).1
    have hz : (e ((d ((U.read n σ g x).1 i)).1 - (d (x.1 i)).1)).1 = 0 :=
      (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero _ _ hd.symm).mpr (hg n σ x i)
    simpa only [map_sub, Prod.fst_sub, sub_eq_zero] using hz
  obtain ⟨u, v, w, he, hu, hv, hw⟩ := U.factors c g fixed
  have outer (z : G) (hz : z ∈ U.keep (fun x => ((c x).1, (c x).2.1))) :
      z ∈ U.motion d T := by
    intro n σ x i
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (hz n σ x i)
    rw [read, read, h₁, h₂, add_sub_add_left_eq_sub, add_sub_add_left_eq_sub]
    exact T.sub_mem ((c _).2.2.1).2 ((c _).2.2.1).2
  have middle : v ∈ U.motion d S := by
    intro n σ x i
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (hv n σ x i)
    rw [read, read, h₁, h₂, add_sub_add_left_eq_sub, add_sub_add_right_eq_sub]
    exact S.sub_mem ((c _).2.1).2 ((c _).2.1).2
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (outer u hu))
    (Subgroup.mem_sup_left middle)) (Subgroup.mem_sup_right (outer w hw))

/-- Plane motions generate any group closed under the required factorizations. -/
theorem motion_generate (h : 2 ≤ Module.finrank k V) :
    (⨆ P : VPlane k V, U.motion d P.1) = ⊤ := by
  classical
  let H := ⨆ P : VPlane k V, U.motion d P.1
  have plane (P : VPlane k V) : U.motion d P.1 ≤ H := le_iSup (fun P => U.motion d P.1) P
  have spans (s : Finset V) : U.motion d (Submodule.span k (s : Set V)) ≤ H := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨P⟩ := flat_nonempty h
      rw [Finset.coe_empty, Submodule.span_empty]
      exact (U.motion_mono d bot_le).trans (plane P)
    | @insert x s _ ih =>
      rw [Finset.coe_insert, Submodule.span_insert]
      by_cases hx : x ∈ Submodule.span k (s : Set V)
      · rwa [sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hx)]
      · have hn : x ≠ 0 := fun he => hx (he.symm ▸ Submodule.zero_mem _)
        let p : VPoint k V := ⟨_, finrank_span_singleton hn⟩
        obtain ⟨⟨P, b⟩, hd⟩ := surjective_flagPoint h p
        have hl : p.1 ≤ P.1 := by rw [← hd]; exact dir_le P b
        exact (motion_sup U d _ _ (Submodule.disjoint_span_singleton_of_notMem hx).symm).trans
          (sup_le ((U.motion_mono d hl).trans (plane P)) ih)
  have ht := spans Finset.univ
  rw [Finset.coe_univ, Submodule.span_univ] at ht
  exact top_unique fun g _ => ht (fun _ _ _ _ => Submodule.mem_top)

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.System
end

/-! # Plane rigidity using only static digit charts and shears -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open scoped Classical

abbrev Digit (k V W : Type) [Field k] [AddCommGroup W] [Module k W] := V × (W →ₗ[k] k)

variable {k V W : Type} [Field k] [AddCommGroup W] [Module k W]
  [AddCommGroup V] [Module k V] [Fintype V]

private def planeCoords (P : VPlane k V) (T : Submodule k V) (hT : IsCompl T P.1) :
    V ≃ₗ[k] T × (Fin 2 → k) :=
  (T.prodEquivOfIsCompl P.1 hT).symm.trans
    ((LinearEquiv.refl k T).prodCongr (planeChart P).symm)

private theorem plane_mem (P : VPlane k V) (T : Submodule k V) (hT : IsCompl T P.1)
    (x y : V) : (planeCoords P T hT x).1 = (planeCoords P T hT y).1 ↔ x - y ∈ P.1 := by
  rw [← sub_eq_zero, ← Prod.fst_sub, ← map_sub]
  exact Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero T P.1 hT

namespace System
variable {M : ℕ} {G : Type} [Group G] (U : System M G) (d : Fin M ≃ Digit k V W)

def planes (P : VPlane k V) : Subgroup G := U.motion d P.1

variable [NeZero M] [Fintype k] [Fintype W]

theorem plane_action (P : VPlane k V) (hW : 4 < Module.finrank k W) :
    ∃ σ, PlaneAction (U.motion d (⊥ : Submodule k V))
      (U.planes d P) (fun t => U.motion d (dir P t).1) (affineGraph (K := k) (V := W)) σ := by
  obtain ⟨T, hT⟩ := P.1.exists_isCompl
  let c := planeCoords P T hT.symm
  let s : Facet M k W T :=
    d.trans ((c.toEquiv.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
  have hP : U.keep s.base = U.planes d P := by
    ext g
    constructor
    · intro hg h σ x i
      exact (plane_mem P T hT.symm _ _).mp (hg h σ x i)
    · intro hg h σ x i
      exact (plane_mem P T hT.symm _ _).mpr (hg h σ x i)
  have h0 : U.keep s.origin = U.motion d (⊥ : Submodule k V) := by
    ext g
    constructor
    · intro hg h σ x i
      rw [Submodule.mem_bot, sub_eq_zero]
      exact c.injective (hg h σ x i)
    · intro hg h σ x i
      exact congrArg c (sub_eq_zero.mp (hg h σ x i))
  have hL (t : Option k) : U.keep (s.projected t) ≤ U.motion d (dir P t).1 := by
    intro g hg h σ x i
    let u := (d ((U.read h σ g x).1 i)).1
    let v := (d (x.1 i)).1
    have hf := congrArg Prod.fst (hg h σ x i)
    have hm : u - v ∈ P.1 := (plane_mem P T hT.symm u v).mp hf
    let z : P.1 := ⟨u - v, hm⟩
    have hz : (c (u - v)).2 = (planeChart P).symm z := by
      change (planeChart P).symm ((T.prodEquivOfIsCompl P.1 hT.symm).symm (z : V)).2 = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
    have hp : projection (c u).2 t = projection (c v).2 t := congrArg Prod.snd (hg h σ x i)
    have hz' : projection ((planeChart P).symm z) t = 0 := by
      rw [← hz, map_sub, Prod.snd_sub]
      cases t <;> simp only [projection, Pi.sub_apply, smul_sub] at hp ⊢
      · exact sub_eq_zero.mpr hp
      · linear_combination hp
    simpa only [LinearEquiv.apply_symm_apply] using (mem_dir P t _).mpr hz'
  refine ⟨U.fixed ∘ s.shear, ?_, ?_, ?_⟩
  · intro a
    rw [← hP]
    intro h σ x i
    rw [Function.comp_apply, U.read_fixed]
    exact s.shear_mem a (x.1 i)
  · intro a a' t t' he
    obtain ⟨rfl, hp⟩ := Prod.mk.inj he
    refine ⟨rfl, hL t ?_⟩
    intro h σ x i
    rw [map_mul, map_inv, Function.comp_apply, Function.comp_apply, U.read_fixed, U.read_fixed]
    exact s.shear_line a a' t hp (x.1 i)
  · rw [← h0, ← hP]
    exact s.half_bridges U hW

theorem rigid [Fintype (W →ₗ[k] k)] (hV : 2 ≤ Module.finrank k V) (hW : 4 < Module.finrank k W) :
    Rigid (hops (U.planes d)) (flagPoint (K := k) (V := V)) Prod.fst
      Prod.fst (affineGraph (K := k) (V := W)) := by
  intro Y _ _ _ _ C hi ha x hx
  have : Nonempty (VPlane k V) := flat_nonempty hV
  have : Nonempty (VPoint k V) := flat_nonempty (le_trans (by decide) hV)
  let f := fun s : Submodule k V => U.motion d s
  exact (uniform_displacement C flagPoint (surjective_flagPoint hV) affineGraph hi ha
    (f ⊥) (fun i => f i.val) (U.planes d)
    (fun _ => U.motion_mono d bot_le) (fun e => U.motion_mono d (dir_le e.1 e.2))
    (U.motion_generate d hV) (fun p => U.plane_action d p hW) x
    (fun p g hg => hx g (Set.mem_iUnion.mpr ⟨p, hg⟩))).2

end System
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

/-! # The countable group of height-independent permutation recipes -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform

open Coloring Equiv
open scoped Classical

deriving instance Countable for Recipe

variable {M : ℕ} (hM : 1 < M)

abbrev Behaviors (M : ℕ) := Coloring.Family (Words M)

def Supported (g : Behaviors M) : Prop :=
  ∃ r : Recipe M, ∀ h σ,
    r.eval hM h (Coloring.pack (embed hM h) σ) = Coloring.pack (embed hM h) (g h σ)

def programs : Subgroup (Behaviors M) where
  carrier := {g | Supported hM g}
  one_mem' := by
    refine ⟨.id, ?_⟩
    intro h σ
    simp only [Recipe.eval, Pi.one_apply, Coloring.pack, map_one]
    rfl
  mul_mem' := by
    intro x y hx hy
    obtain ⟨r, hr⟩ := hx
    obtain ⟨s, hs⟩ := hy
    refine ⟨.mul r s, ?_⟩
    intro h σ
    rw [Recipe.eval, hr h σ, hs h σ]
    simp only [Pi.mul_apply, Coloring.pack, map_mul]
    rfl
  inv_mem' := by
    intro g hg
    obtain ⟨r, hr⟩ := hg
    refine ⟨.inv r, ?_⟩
    intro h σ
    rw [Recipe.eval, hr h σ]
    have inverse (q : Equiv.Perm (B (h + 1))) : (⇑q⁻¹ : ArrayOf (h + 1)) = ⇑q.symm := rfl
    simp only [Coloring.pack, Pi.inv_apply, map_inv, inverse]
    exact invert_perm _

def recipe (g : programs hM) : Recipe M :=
  Classical.choose (show Supported hM g.val from g.property)

theorem recipe_spec (g : programs hM) (h : ℕ) (σ : Equiv.Perm (Words M h)) :
    (recipe hM g).eval hM h (Coloring.pack (embed hM h) σ) = Coloring.pack (embed hM h) (g.val h σ) :=
  Classical.choose_spec (show Supported hM g.val from g.property) h σ

instance : Countable (programs hM) := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat (Recipe M)
  refine ⟨⟨e ∘ recipe hM, he.comp ?_⟩⟩
  intro g g' hyp
  apply Subtype.ext
  funext h σ
  apply Equiv.Perm.viaEmbeddingHom_injective (embed hM h)
  apply Equiv.ext
  intro i
  have eqEval := congrArg (fun r : Recipe M => r.eval hM h (Coloring.pack (embed hM h) σ)) hyp
  have same := ((recipe_spec hM g h σ).symm.trans eqEval).trans (recipe_spec hM g' h σ)
  exact congrFun same i

def target : programs hM :=
  ⟨fun _ σ => σ, .target, fun _ _ => rfl⟩

def constant (p : Equiv.Perm (Fin M)) : programs hM :=
  ⟨fun h _ => digitPerm p h, .digit p, fun h _ => packDigit_eq hM p h⟩

private theorem clean_eq (h : ℕ) {f : ArrayOf (h + 1)} (σ : Equiv.Perm (Words M h))
    (hf : ∀ v, f (embed hM h v) = embed hM h (σ v)) :
    Recipe.clean M h f = Coloring.pack (embed hM h) σ := by
  funext i
  change Recipe.clean M h f i = σ.viaEmbedding (embed hM h) i
  by_cases hi : i.val < count M h
  · obtain ⟨x, rfl⟩ := (embed_range hM h i).mp hi
    rw [Recipe.clean, ite_eq_left hi, Equiv.Perm.viaEmbedding_apply]
    exact hf x
  · rw [Recipe.clean, ite_eq_right hi, Equiv.Perm.viaEmbedding_apply_of_notMem]
    exact mt (embed_range hM h i).mpr hi

private theorem pick_zero {α : Type} (x : α × α × α) : Recipe.pick 0 x = x.1 := by
  simp [Recipe.pick]

private theorem pick_one {α : Type} (x : α × α × α) : Recipe.pick 1 x = x.2.1 := by
  simp [Recipe.pick]

private theorem pick_two {α : Type} (x : α × α × α) : Recipe.pick 2 x = x.2.2 := by
  simp [Recipe.pick]

private theorem split_program (p : ProductChart M) (g : programs hM)
    (hg : ∀ h σ x, (p.apply h (g.val h σ x)).1 = (p.apply h x).1) :
    ∃ u v w : programs hM, g = u * v * w ∧
      (∀ h σ x, (p.apply h (u.val h σ x)).1 = (p.apply h x).1 ∧
        (p.apply h (u.val h σ x)).2.1 = (p.apply h x).2.1) ∧
      (∀ h σ x, (p.apply h (v.val h σ x)).1 = (p.apply h x).1 ∧
        (p.apply h (v.val h σ x)).2.2 = (p.apply h x).2.2) ∧
      (∀ h σ x, (p.apply h (w.val h σ x)).1 = (p.apply h x).1 ∧
        (p.apply h (w.val h σ x)).2.1 = (p.apply h x).2.1) := by
  have possible (h : ℕ) (σ : Equiv.Perm (Words M h)) :=
    chart_exists hM p h invert invert_perm (g.val h σ) (hg h σ)
      (Coloring.pack (embed hM h) (g.val h σ))
      (Equiv.Perm.viaEmbedding_apply (g.val h σ) (embed hM h))
  choose u v w hprod hu hv hw h₁ h₂ h₃ using possible
  have rep₁ : Supported hM u := by
    refine ⟨.factor p 0 (recipe hM g), ?_⟩
    intro h σ
    rw [Recipe.eval, recipe_spec, pick_zero]
    exact clean_eq hM h (u h σ) (h₁ h σ)
  have rep₂ : Supported hM v := by
    refine ⟨.factor p 1 (recipe hM g), ?_⟩
    intro h σ
    rw [Recipe.eval, recipe_spec, pick_one]
    exact clean_eq hM h (v h σ) (h₂ h σ)
  have rep₃ : Supported hM w := by
    refine ⟨.factor p 2 (recipe hM g), ?_⟩
    intro h σ
    rw [Recipe.eval, recipe_spec, pick_two]
    exact clean_eq hM h (w h σ) (h₃ h σ)
  refine ⟨⟨u, rep₁⟩, ⟨v, rep₂⟩, ⟨w, rep₃⟩, ?_, hu, hv, hw⟩
  exact Subtype.ext (funext fun h => funext fun σ => hprod h σ)

def system : System M (programs hM) where
  read h σ := {toFun := fun g => g.val h σ, map_one' := rfl, map_mul' := fun _ _ => rfl}
  fixed := constant hM
  read_fixed _ _ _ := rfl
  factor := split_program hM

theorem system_read_target (h : ℕ) (σ : Equiv.Perm (Words M h)) :
    (system hM).read h σ (target hM) = σ := rfl

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# Metered generation, execution and port data

The two counters of the blueprint charge separately for preparing
the arithmetic tables and emitting the instructions. Group labels
are materialized for each port. All bounds use a fixed blueprint.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Generation
open Coloring Algorithm
variable {M t p q l n : ℕ}

private abbrev size (h d : ℕ) := 2 ^ (h + 1) * (100 + Blueprint.bits h) ^ d

private def Near (f : ℕ → ℕ) : Prop :=
  ∃ K d, ∀ h, f h ≤ K * size h d

namespace Near
variable {f g : ℕ → ℕ}

private theorem of_bound {d : ℕ} (hf : ∀ h, f h ≤ size h d) : Near f :=
  ⟨1, d, fun h => by rw [one_mul]; exact hf h⟩

private theorem budget (d : ℕ) : Near (fun h => size h d) := of_bound (fun _ => le_rfl)

private theorem sites : Near (fun h => 2 ^ (h + 1)) := by simpa [size] using budget 0

private theorem one : Near (fun _ => 1) :=
  of_bound (d := 0) (fun h => by simp only [size, pow_zero, mul_one]; exact Nat.two_pow_pos _)

private theorem add (hf : Near f) (hg : Near g) : Near (fun h => f h + g h) := by
  obtain ⟨K, d, hf⟩ := hf
  obtain ⟨L, e, hg⟩ := hg
  refine ⟨K + L, max d e, fun h => ?_⟩
  rw [add_mul]
  exact Nat.add_le_add
    ((hf h).trans (Nat.mul_le_mul_left _ (budget_mono _ _ (le_max_left ..))))
    ((hg h).trans (Nat.mul_le_mul_left _ (budget_mono _ _ (le_max_right ..))))

private theorem scale (hf : Near f) (k : ℕ) : Near (fun h => k * f h) := by
  obtain ⟨K, d, hf⟩ := hf
  exact ⟨k * K, d, fun h => (Nat.mul_le_mul_left k (hf h)).trans_eq (mul_assoc ..).symm⟩

private theorem right (hf : Near f) (k : ℕ) : Near (fun h => f h * k) := by
  simpa only [mul_comm k] using hf.scale k

private theorem constant (k : ℕ) : Near (fun _ => k) := by
  simpa only [mul_one] using one.scale k

private theorem withAllowance (hf : Near f) :
    Near (fun h => 128 * allowance (Blueprint.bits h) * f h) := by
  obtain ⟨K, d, hf⟩ := hf
  refine ⟨128 * K, 5 + d, fun h => ?_⟩
  calc
    _ ≤ 128 * allowance (Blueprint.bits h) * (K * size h d) := Nat.mul_le_mul_left _ (hf h)
    _ = _ := by unfold size allowance; rw [pow_add (100 + Blueprint.bits h)]; ac_rfl

private theorem sum {I : Type} [Fintype I] {f : I → ℕ → ℕ} (hf : ∀ i, Near (f i)) :
    Near (fun h => ∑ i, f i h) := by
  classical
  suffices H : ∀ s : Finset I, Near (fun h => ∑ i ∈ s, f i h) from H Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using (hf i).add ih

private theorem absorb (hf : Near f) : ∃ c, ∀ h, f h ≤ 2 ^ h * (100 + h) ^ c := by
  obtain ⟨K, d, hf⟩ := hf
  refine ⟨Nat.clog 2 (2 * K) + 2 * d, fun h => ?_⟩
  have hk : 2 * K ≤ (100 + h) ^ Nat.clog 2 (2 * K) :=
    (Nat.le_pow_clog (by decide : 1 < 2) _).trans (Nat.pow_le_pow_left (by omega) _)
  have hw : (100 + Blueprint.bits h) ^ d ≤ (100 + h) ^ (2 * d) := by
    rw [pow_mul]
    apply Nat.pow_le_pow_left
    unfold Blueprint.bits
    nlinarith
  calc
    _ ≤ K * size h d := hf h
    _ = 2 ^ h * (2 * K * (100 + Blueprint.bits h) ^ d) := by unfold size; rw [pow_succ]; ac_rfl
    _ ≤ 2 ^ h * ((100 + h) ^ Nat.clog 2 (2 * K) * (100 + h) ^ (2 * d)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hk hw)
    _ = _ := by rw [← pow_add]

end Near

private theorem charge_near (a : Blueprint M t p q l n) : Near a.charge := by
  have arr {k : ℕ} (r : B k → Recipe M) : Near (fun h => Recipe.menuCost r h (Blueprint.bits h)) :=
    ((Near.budget (Recipe.rates r)).add Near.one).scale (2 ^ k)
  have menus := ((arr a.watch).add (arr a.hop)).add Near.one
  have paths := (Near.one.add (Near.sites.right 3)).add menus
  exact ((Near.one.add paths).add Near.one).add (Near.sites.right (dispatchCost t p n))

private theorem numeric (h d : ℕ) : 2 ^ (h + 1) * (100 + h) ^ d ≤ size h d :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold Blueprint.bits; omega) _)

private def setup (hM : 1 < M) (f : B t → Recipe M) (h : ℕ) :=
  64 + (Work.dtab (fun i => (f i).generate hM h (w := Blueprint.bits h) le_rfl)).steps

private theorem setup_near (hM : 1 < M) (f : B t → Recipe M) : Near (setup hM f) := by
  have child (i : B t) : Near (fun h => ((f i).generate hM h (w := Blueprint.bits h) le_rfl).steps) := by
    obtain ⟨d, hd⟩ := (f i).steps hM
    exact Near.of_bound (d := d) (fun h => (hd h _ le_rfl).trans (numeric h d))
  have each := Near.sum (fun i => (Near.constant 64).add (child i))
  have H := (Near.constant 64).add ((Near.constant 64).add each)
  unfold setup
  simpa only [Work.dtab_steps] using H

/-- One exponent covers the instrumented generator, the execution
charge and the static per-port data. The exponent is independent of
the height and the requested block size. -/
theorem uniform (a : Blueprint M t p q l n) (hM : 1 < M) :
    ∃ c, ∀ h b (hh : Blueprint.limit t p q l ≤ h),
      (a.generate hM h b hh).steps + 32 * a.charge h + 2 ^ (h + 1) * (64 + 32 * 2 ^ p) ≤ 2 ^ h * (100 + h) ^ c := by
  obtain ⟨d, hd⟩ := Materialize.bounds M
  have group : Near (fun h => 64 + 2 ^ p * (64 + size h d)) :=
    (Near.constant 64).add (((Near.constant 64).add (Near.budget d)).scale (2 ^ p))
  have prepare := ((Near.constant 128).add (setup_near hM a.watch)).add (setup_near hM a.hop)
  have program := charge_near a
  have total := (((Near.constant 64).add prepare).add program.withAllowance).add group
  obtain ⟨c, hc⟩ := ((total.add (program.scale 32)).add (Near.sites.right (64 + 32 * 2 ^ p))).absorb
  refine ⟨c, fun h b hh => le_trans ?_ (hc h)⟩
  have groups := Work.tab_le (fun i => Materialize.group (a.chart i) h b) (size h d)
    (fun i => ((hd hM h).2.2.1 (a.chart i) b).trans (numeric h d))
  have emit := (a.compile hM h hh).built
  have build : (a.build hM h hh).steps = 128 + setup hM a.watch h + setup hM a.hop h := rfl
  change 64 + (a.build hM h hh).steps + (a.compile hM h hh).made.steps +
    (Work.tab (fun i => Materialize.group (a.chart i) h b)).steps +
    32 * a.charge h + 2 ^ (h + 1) * (64 + 32 * 2 ^ p) ≤ _
  rw [build]
  dsimp only
  omega

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Generation
end

/-!
# A routing layout whose port partitions have a fixed digit description

Each core element has one chart, independent of the height and input.
All other data used in the partition are computed from the height.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring
open scoped Classical

variable {M : ℕ} {G : Type} [Group G]

structure Geometry (F : Type) [Field F] (m : ℕ) (U : System M G) (g : G) where
  J : Type
  moves : J → Subgroup G
  params : Parameters F moves g⁻¹
  overhead : ℕ
  chart : params.core → ProductChart M
  capacity : ∀ x h, (chart x).degree h ≤ 2 ^ (h / m + overhead)
  row : ∀ x h σ i, ((chart x).grid h (U.read h σ x.val i)).1 = ((chart x).grid h i).1

abbrev System.action (U : System M G) (hM : 1 < M) (h : ℕ) (σ : Equiv.Perm (B h)) :
    MulAction G (B (h + 1)) :=
  MulAction.compHom _ ((Equiv.Perm.viaEmbeddingHom (embed hM h)).comp
    (U.read h (σ.viaEmbedding (base hM h))))

theorem pack_eq (hM : 1 < M) (h : ℕ) (π : Equiv.Perm (B h)) :
    ⇑((π.viaEmbedding (base hM h)).viaEmbedding (embed hM h)) = inflate h π := by
  have eb (i : B h) : embed hM h (base hM h i) = lowerHalf h i := Fin.ext (initial hM h i)
  funext a
  unfold inflate
  split
  · rename_i ha
    let i : B h := ⟨a, ha⟩
    have eq : a = embed hM h (base hM h i) := (Fin.ext (initial hM h i)).symm
    change _ = lowerHalf h (π i)
    rw [eq, Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply, eb]
  · rename_i ha
    by_cases he : a ∈ Set.range (embed hM h)
    · obtain ⟨v, rfl⟩ := he
      have hb : v ∉ Set.range (base hM h) := by
        rintro ⟨i, rfl⟩
        exact ha ((initial hM h i).trans_lt i.isLt)
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hb]
    · exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ he

namespace Geometry
variable {F : Type} [Field F] {m : ℕ} {U : System M G} {g : G}
  (S : Geometry F m U g) (hM : 1 < M)

theorem same (x : S.params.core) (h b : ℕ) (hb : h / m + S.overhead ≤ b)
    (σ : Equiv.Perm (B h)) (i : B (h + 1)) :
    (S.chart x).position h ((U.action hM h σ).smul x.val i) / 2 ^ b =
      (S.chart x).position h i / 2 ^ b := by
  let t := σ.viaEmbedding (base hM h)
  change (S.chart x).position h ((U.read h t x.val).viaEmbedding (embed hM h) i) / 2 ^ b = _
  by_cases he : i ∈ Set.range (embed hM h)
  · obtain ⟨j, rfl⟩ := he
    rw [Equiv.Perm.viaEmbedding_apply]
    exact (S.chart x).position_group h hM b
      ((S.capacity x h).trans (Nat.pow_le_pow_right (by decide) hb)) _ _ (S.row x h t j)
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ he]

def layout (hg : ∀ h σ, U.read h σ g = σ) : Algorithm.Layout F m where
  G := G
  J := S.J
  U := S.moves
  g := g
  params := S.params
  action := U.action hM
  target h σ i := by
    change (U.read h (σ.viaEmbedding (base hM h)) g).viaEmbedding (embed hM h) i = _
    rw [hg]
    exact congrFun (pack_eq hM h σ) i
  overhead := S.overhead
  grouping {x} hx h b hb hb' :=
    ⟨(S.chart ⟨x, hx⟩).packing h hM b hb', fun σ i => Fin.ext (S.same hM ⟨x, hx⟩ h b hb σ i)⟩

end Geometry
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

/-!
# Finite geometry for fixed digit operations

For a requested block-size exponent choose one digit alphabet. Generation
and rigidity then hold for any group admitting the static operations
of System. In particular no height-dependent permutations are required
as generators.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open scoped Classical

private theorem degree_bound {M q v w m : ℕ} (hq : 2 ≤ q) (hm : 0 < m)
    (hv : m * (2 + w) ≤ v + w) (he : M = q ^ (v + w)) (hM : 1 < M) (h : ℕ) :
    (q ^ (2 + w)) ^ (length M h) * spare M h ≤ 2 ^ (h / m + (1 + Nat.clog 2 M)) := by
  let r := length M h
  have hlo : M ^ r ≤ 2 ^ h := Nat.pow_log_le_self M (Nat.two_pow_pos h).ne'
  have hs : q ^ ((2 + w) * r) ≤ 2 ^ (h / m + 1) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) hm.ne').mp
    rw [← pow_mul, ← pow_mul]
    calc
      q ^ ((2 + w) * r * m) = q ^ ((m * (2 + w)) * r) := by ring
      _ ≤ q ^ ((v + w) * r) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right r hv)
      _ ≤ 2 ^ h := by rw [pow_mul, ← he]; exact hlo
      _ ≤ 2 ^ ((h / m + 1) * m) := Nat.pow_le_pow_right (by decide)
        ((Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self _)).le
  rw [← pow_mul, ← Nat.add_assoc, pow_add]
  exact Nat.mul_le_mul hs ((spare_le hM h).trans (Nat.le_pow_clog (by decide) M))

variable {F k V W : Type} [Field F] [Field k] [Fintype k]
  [AddCommGroup V] [Module k V] [Fintype V] [AddCommGroup W] [Module k W] [Fintype W]

private theorem card_digit [Fintype (W →ₗ[k] k)] :
    Fintype.card (Digit k V W) = Fintype.card k ^ (Module.finrank k V + Module.finrank k W) := by
  rw [Fintype.card_prod, Module.card_eq_pow_finrank (K := k) (V := V),
    Module.card_eq_pow_finrank (K := k) (V := W →ₗ[k] k),
    Module.finrank_linearMap, Module.finrank_self, mul_one, pow_add]

private theorem plane_partition {M : ℕ} [NeZero M] [Fintype (W →ₗ[k] k)]
    {G : Type} [Group G] (U : System M G) (d : Fin M ≃ Digit k V W) (P : VPlane k V) :
    ∃ p : ProductChart M, p.b.val = Fintype.card k ^ (2 + Module.finrank k W) ∧
      ∀ g ∈ U.planes d P, ∀ h σ x, (p.grid h (U.read h σ g x)).1 = (p.grid h x).1 := by
  obtain ⟨T, hT⟩ := P.1.exists_isCompl
  let e := (T.prodEquivOfIsCompl P.1 hT.symm).symm
  let f : Fin M ≃ T × Unit × Digit k P.1 W :=
    { toFun := fun x => ((e (d x).1).1, (), (e (d x).1).2, (d x).2)
      invFun := fun y => d.symm (e.symm (y.1, y.2.2.1), y.2.2.2)
      left_inv := by intro x; simp
      right_inv := by rintro ⟨t, ⟨⟩, u, v⟩; simp }
  let p := ProductChart.ofEquiv f
  refine ⟨p, ?_, fun g hg h σ x => ?_⟩
  · change Fintype.card (Digit k P.1 W) = _
    rw [card_digit, P.2]
  · let y := U.read h σ g x
    have he (i : Fin (length M h)) : (f (y.1 i)).1 = (f (x.1 i)).1 := by
      change (e (d (y.1 i)).1).1 = (e (d (x.1 i)).1).1
      rw [← sub_eq_zero, ← Prod.fst_sub, ← map_sub]
      exact (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero _ _ hT.symm).mpr (hg h σ x i)
    have hc : (p.apply h y).1 = (p.apply h x).1 :=
      funext fun i => congrArg (Fintype.equivFin T) (he i)
    have ha : (p.apply h y).2.1 = (p.apply h x).2.1 := rfl
    exact congrArg (p.row h) (Prod.ext hc ha)

private theorem make_geometry
    (hmod : HasModels F (flagPoint (K := k) (V := V)) Prod.fst Prod.fst
      (affineGraph (K := k) (V := W))) (hV : 2 ≤ Module.finrank k V) (hW : 4 < Module.finrank k W)
    (m : ℕ) (hm : 0 < m) (hd : m * (2 + Module.finrank k W) ≤ Module.finrank k V + Module.finrank k W) :
    ∃ M : ℕ, 1 < M ∧ ∀ (G : Type) [Group G] (U : System M G) (g : G),
      Nonempty (Geometry F m U g) := by
  have : Finite (W →ₗ[k] k) :=
    Finite.of_injective (fun f : W →ₗ[k] k => (f : W → k)) DFunLike.coe_injective
  let : Fintype (W →ₗ[k] k) := Fintype.ofFinite _
  let M := Fintype.card (Digit k V W)
  have he : M = Fintype.card k ^ (Module.finrank k V + Module.finrank k W) := card_digit
  have hM : 1 < M := by rw [he]; exact one_lt_pow₀ Fintype.one_lt_card (by omega)
  have : NeZero M := ⟨by omega⟩
  have : Nonempty (VPlane k V) := flat_nonempty hV
  have : Nonempty (VPoint k V) := flat_nonempty (le_trans (by decide) hV)
  let d := (Fintype.equivFin (Digit k V W)).symm
  refine ⟨M, hM, fun G _ U g => ?_⟩
  have gen : iSup (U.planes d) = ⊤ := U.motion_generate d hV
  obtain ⟨params⟩ := Rigid.parameters gen (U.rigid d hV hW) hmod g⁻¹
  have chart (x : params.core) : ∃ p : ProductChart M,
      (∀ h, p.degree h ≤ 2 ^ (h / m + (1 + Nat.clog 2 M))) ∧
      ∀ h σ i, (p.grid h (U.read h σ x.val i)).1 = (p.grid h i).1 := by
    obtain ⟨P, hp⟩ := Set.mem_iUnion.mp (params.hop x.property)
    obtain ⟨p, hs, hr⟩ := plane_partition U d P
    refine ⟨p, fun h => ?_, hr _ hp⟩
    rw [ProductChart.degree, hs]
    exact degree_bound Fintype.one_lt_card hm hd he hM h
  choose p hp hr using chart
  exact ⟨⟨VPlane k V, U.planes d, params, 1 + Nat.clog 2 M, p, hp, hr⟩⟩

theorem geometry_of_shared_price [Finite F]
    (hs : Prices.SharedPrice (AlgebraicClosure F))
    (m : ℕ) (hm : 0 < m) : ∃ M : ℕ, 1 < M ∧
      ∀ (G : Type) [Group G] (U : System M G) (g : G), Nonempty (Geometry F m U g) := by
  let p := ringChar F
  have : Fact p.Prime := ⟨CharP.char_is_prime F _⟩
  let k := FiniteField.Extension F p 7
  have : CharP k p := charP_of_injective_algebraMap' F p
  let W := FiniteField.Extension k p 5
  let V := Fin (7 * m) → k
  let L := AlgebraicClosure F
  let : Algebra k L := (IsAlgClosed.lift : k →ₐ[F] L).toRingHom.toAlgebra
  let : Algebra W L := (IsAlgClosed.lift : W →ₐ[k] L).toRingHom.toAlgebra
  let : Fintype k := Fintype.ofFinite k
  let : Fintype W := Fintype.ofFinite W
  have hq : 100 ≤ Fintype.card k := by
    rw [Fintype.card_eq_nat_card, show Nat.card k = Nat.card F ^ 7 from
      FiniteField.natCard_extension F p 7]
    exact le_trans (show 100 ≤ 2 ^ 7 by decide) (Nat.pow_le_pow_left Finite.one_lt_card _)
  have hw : Module.finrank k W = 5 := FiniteField.finrank_extension k p 5
  have hv : Module.finrank k V = 7 * m := by simp [V]
  exact make_geometry (V := V) (W := W) (models_of_shared_price hs hq)
    (by omega) (by omega) m hm (by rw [hv, hw]; omega)

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end
