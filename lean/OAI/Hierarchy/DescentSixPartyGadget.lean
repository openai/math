import OAI.Hierarchy.DescentSixParty
import OAI.Hierarchy.DescentSixPartySeed
import OAI.ThreeFlat.Diagonal.MotifKernel

namespace OAI
/-! # The six-party powered gadget and its common-layout contraction -/

namespace Hierarchy.DescentSixParty

open Computability.VPVNP Computability.VPVNP.WireTensor
open ThreeFlat.Diagonal.MotifKernel
open scoped BigOperators Classical
noncomputable section

/-- A fixed set of ordinary local-map networks realizes every positive power of the
two demands. The unit on each supply edge has the prescribed power in bits. -/
structure PoweredGadget (F : Type*) [Field F] where
  b : ℕ
  k : ℕ
  C : ℕ
  paid : C + 8 + 8*k < 4*b
  realize (z : ℕ) (hz : 0 < z) :
    let X := MotifBase.binaryWires (k := F) demandSrc demandDst (fun _ => z*b)
    let Y := fun p : Profile C => MotifBase.binaryWires (k := F) supplySrc supplyDst
      (fun e => z * ((p.1 e).val + k))
    ∃ L : ∀ p j, X.Basis j → (Y p).Basis j → F,
      X.coeff = ∑ p, applyLocal (L p) (Y p).coeff

theorem exists_powered_gadget (F : Type*) [Field F] : Nonempty (PoweredGadget F) := by
  obtain ⟨b,k,C,paid,H,fh,w,h⟩ := exists_class_seed F
  let : Fintype H := fh
  obtain ⟨count,cost,seed⟩ := h
  exact ⟨⟨b,k,C,paid,fun z hz => powered_ordinary_sum supplySrc supplyDst
    (@connected) w cost demandSrc demandDst b count seed hz⟩⟩

/-- The three clusters in the row placement and the column placement, in party
order A,B,C,D,M,N. -/
def cluster : Bool → Fin 6 → Fin 3
  | false => ![0,1,0,2,0,2]
  | true => ![0,1,1,2,2,1]

def retained (layout : Bool) (e : Fin 8) : Prop :=
  cluster layout (supplySrc e) ≠ cluster layout (supplyDst e)

theorem shared_iff_retained (layout : Bool) (e : Fin 8) :
    wireOwner supplySrc supplyDst (cluster layout) e = none ↔ retained layout e := by
  classical
  unfold wireOwner retained
  split <;> simp_all

/-- Cluster-local kernels with the finite enumerations chosen uniformly in the party,
edge, and cluster types. -/
def groupedAt {F J E G : Type*} [CommSemiring F] [Fintype J] [Fintype E] [Fintype G]
    [DecidableEq G] {A : J → Type*} (src dst : E → J) (place : J → G)
    (I : E → Type*) [∀ e,Fintype (I e)]
    (L : ∀ j,A j → (wireNetwork (k := F) src dst I).Basis j → F) (x : ∀ j,A j) : F :=
  ∑ b : WiresAt src dst place (I := I) none,
    ∏ g, ∑ a : WiresAt src dst place (I := I) (some g),
      ∏ j : {j // place j = g}, L j (x j) (atParty src dst place j b (j.2.symm ▸ a))

theorem groupedAt_correct {F J E G : Type*} [CommSemiring F] [Fintype J] [Fintype E] [Fintype G]
    [DecidableEq G] {A : J → Type*} (src dst : E → J) (place : J → G)
    (I : E → Type*) [∀ e,Fintype (I e)]
    (L : ∀ j,A j → (wireNetwork (k := F) src dst I).Basis j → F) (x : ∀ j,A j) :
    applyLocal L (wireNetwork src dst I).coeff x = groupedAt src dst place I L x :=
  applyLocal_eq_grouped src dst place L x

/-- Contract the private wires within each chosen cluster. The only indices
summed across clusters are the retained supply wires. -/
def groupedTerm {F : Type*} [CommSemiring F] {A : Fin 6 → Type*}
    (I : Fin 8 → Type) [∀ e, Fintype (I e)] (layout : Bool)
    (L : ∀ j, A j → (wireNetwork (k := F) supplySrc supplyDst I).Basis j → F)
    (x : ∀ j, A j) : F :=
  groupedAt (A := A) supplySrc supplyDst (cluster layout) I L x

private theorem opposite : ∀ e, retained false e ↔ ¬ retained true e := by
  unfold retained
  decide

def surviving {I : Type*} [Fintype I] (w : I → Fin 8 → ℕ) (layout : Bool) : ℕ :=
  ∑ i, ∑ e, if retained layout e then w i e else 0

theorem common_layout {I : Type*} [Fintype I] (w : I → Fin 8 → ℕ) :
    ∃ layout, 2*surviving w layout ≤ ∑ i, ∑ e, w i e := by
  have both : surviving w false + surviving w true = ∑ i, ∑ e, w i e := by
    unfold surviving
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : retained true e <;> simp [opposite, h]
  by_cases h : surviving w false ≤ surviving w true
  · exact ⟨false, by omega⟩
  · exact ⟨true, by omega⟩

namespace PoweredGadget

variable {F : Type*} [Field F] (G : PoweredGadget F)

attribute [local irreducible] demandSrc demandDst supplySrc supplyDst cluster

private theorem expand {A : Fin 6 → Type*} (I : Fin 8 → Type) [∀ e, Fintype (I e)]
    (L : ∀ j, A j → (wireNetwork (k := F) supplySrc supplyDst I).Basis j → F)
    (x : ∀ j,A j) : applyLocal L (wireNetwork supplySrc supplyDst I).coeff x =
      ∑ y : ∀ e,I e, ∏ j,L j (x j) (edgeAssignment supplySrc supplyDst y j) := by
  classical
  rw [applyLocal_wireNetwork]
  apply Finset.sum_congr
  · exact congrArg (@Finset.univ ((e : Fin 8) → I e)) (Subsingleton.elim _ _)
  · intros; rfl

private theorem group {A : Fin 6 → Type*} (I : Fin 8 → Type) [∀ e, Fintype (I e)]
    (layout : Bool) (L : ∀ j,A j → (wireNetwork (k := F) supplySrc supplyDst I).Basis j → F)
    (x : ∀ j,A j) : applyLocal L (wireNetwork supplySrc supplyDst I).coeff x =
      groupedTerm (A := A) I layout L x :=
  groupedAt_correct (A := A) supplySrc supplyDst (cluster layout) I L x

set_option maxHeartbeats 1600000 in
/-- At specified demand endpoints, contracting the six local tables along eight
independent internal edge indices gives the demanded pair of equality wires. -/
theorem contraction (z : ℕ) (hz : 0 < z) :
    let X := MotifBase.binaryWires (k := F) demandSrc demandDst (fun _ => z*G.b)
    let idx := fun (p : Profile G.C) (e : Fin 8) => Fin (2^(z * ((p.1 e).val + G.k)))
    ∃ L : ∀ p j, X.Basis j → (wireNetwork (k := F) supplySrc supplyDst (idx p)).Basis j → F,
      ∀ x : ∀ j,X.Basis j, X.coeff x = ∑ p, ∑ y : ∀ e, idx p e,
        ∏ j, L p j (x j) (edgeAssignment supplySrc supplyDst y j) := by
  dsimp only
  obtain ⟨L, identity⟩ := G.realize z hz
  refine ⟨L, fun x => ?_⟩
  rw [identity,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  apply expand (A := (MotifBase.binaryWires (k := F) demandSrc demandDst (fun _ => z*G.b)).Basis)

set_option maxHeartbeats 1600000 in
/-- Either layout can be selected separately per outer summand while preserving
the demanded tensor. All private wires have been summed at their owning cluster. -/
theorem contraction_grouped (z : ℕ) (hz : 0 < z) (layout : Profile G.C → Bool) :
    let X := MotifBase.binaryWires (k := F) demandSrc demandDst (fun _ => z*G.b)
    let idx := fun (p : Profile G.C) (e : Fin 8) => Fin (2^(z * ((p.1 e).val + G.k)))
    ∃ L : ∀ p j, X.Basis j → (wireNetwork (k := F) supplySrc supplyDst (idx p)).Basis j → F,
      ∀ x : ∀ j,X.Basis j, X.coeff x = ∑ p, groupedTerm (A := X.Basis) (idx p) (layout p) (L p) x := by
  dsimp only
  obtain ⟨L, identity⟩ := G.realize z hz
  refine ⟨L, fun x => ?_⟩
  rw [identity, Finset.sum_apply]
  exact Finset.sum_congr rfl fun p _ =>
    group _ (layout p) (L p) x

def rate : ℝ := ((G.C:ℝ) + 8 + 8*(G.k:ℝ))/(2*(G.b:ℝ))

theorem base_pos : 0 < G.b := by have paid := G.paid; omega

theorem rate_nonneg : 0 ≤ G.rate := by unfold rate; positivity

theorem rate_lt_two : G.rate < 2 := by
  have bd := G.paid
  have pos := G.base_pos
  have gap : (G.C:ℝ) + 8 + 8*G.k < 4*G.b := by exact_mod_cast bd
  apply (div_lt_iff₀ (show (0:ℝ) < 2*G.b by positivity)).2
  linarith

/-- One common placement works for all matched pairs of arbitrary widths and
all their selected outer summands, with the same strict constant. -/
theorem common_layout_saving {I : Type*} [Fintype I] (p : I → Profile G.C) (z : I → ℕ) :
    ∃ layout, (surviving (fun i e => z i * (((p i).1 e).val + G.k)) layout : ℝ) ≤
      G.rate * (G.b * (∑ i, z i) : ℕ) := by
  let w (i : I) (e : Fin 8) := z i * (((p i).1 e).val + G.k)
  have each (i : I) : ∑ e, w i e ≤ z i * (G.C + 8 + 8*G.k) := by
    simpa only [w,Finset.mul_sum] using Nat.mul_le_mul_left (z i) (profile_cost G.k (p i))
  obtain ⟨l, hl⟩ := common_layout w
  have total := hl.trans (Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i))
  rw [← Finset.sum_mul] at total
  have realCost : 2*(surviving w l : ℝ) ≤ (∑ i, (z i:ℝ))*((G.C:ℝ) + 8 + 8*G.k) := by
    exact_mod_cast total
  have pos := G.base_pos
  have nz : (G.b:ℝ) ≠ 0 := by positivity
  refine ⟨l, ?_⟩
  rw [rate, Nat.cast_mul, Nat.cast_sum]
  calc
    _ ≤ ((∑ i, (z i:ℝ))*((G.C:ℝ) + 8 + 8*G.k))/2 := by change (surviving w l:ℝ) ≤ _; linarith
    _ = _ := by field_simp

set_option maxHeartbeats 1600000 in
/-- A matched collection has one common layout in each joint summand. The
same choice both preserves its contraction and pays the surviving wire cost. -/
theorem matched_contraction {I : Type*} [Fintype I] (z : I → ℕ) (hz : ∀ i, 0 < z i) :
    let X := fun i => MotifBase.binaryWires (k := F) demandSrc demandDst (fun _ => z i*G.b)
    let idx := fun (i : I) (p : Profile G.C) (e : Fin 8) => Fin (2^(z i * ((p.1 e).val + G.k)))
    ∃ (layout : (I → Profile G.C) → Bool)
      (L : ∀ i (p : Profile G.C) j, (X i).Basis j →
        (wireNetwork (k := F) supplySrc supplyDst (idx i p)).Basis j → F),
      (∀ p, (surviving (fun i e => z i * (((p i).1 e).val + G.k)) (layout p) : ℝ) ≤
        G.rate * (G.b * (∑ i, z i) : ℕ)) ∧
      ∀ x : ∀ i j,(X i).Basis j, (∏ i, (X i).coeff (x i)) =
        ∑ p, ∏ i, groupedTerm (A := (X i).Basis) (idx i (p i)) (layout p) (L i (p i)) (x i) := by
  dsimp only
  choose L identity using fun i => G.realize (z i) (hz i)
  choose layout paid using fun p => G.common_layout_saving p z
  refine ⟨layout,L,paid,fun x => ?_⟩
  let Y (i : I) (p : Profile G.C) := MotifBase.binaryWires (k := F) supplySrc supplyDst
    (fun e => z i * ((p.1 e).val + G.k))
  calc
    _ = ∏ i, ∑ p, applyLocal (L i p) (Y i p).coeff (x i) := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Finset.sum_apply,Y] using congrFun (identity i) (x i)
    _ = _ := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.prod_congr rfl
      intro i _
      exact group _ (layout p) (L i (p i)) (x i)

/-- Contracting the selected placement after matching at least a quarter of
the core, up to the packing error, gives a uniform strict contraction factor. -/
theorem subround_bound {before matched after error : ℝ}
    (matching : before/4 - error ≤ matched)
    (replace : after ≤ before - 2*matched + G.rate*matched) :
    1 - (2-G.rate)/4 < 1 ∧
      after ≤ (1 - (2-G.rate)/4)*before + (2-G.rate)*error := by
  have gap := G.rate_lt_two
  constructor
  · linarith
  · nlinarith only [replace, mul_le_mul_of_nonneg_left matching (sub_nonneg.mpr gap.le)]

end PoweredGadget


end
end Hierarchy.DescentSixParty

end OAI
