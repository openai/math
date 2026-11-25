import OAI.Hierarchy.DescentInputTerminals
import OAI.Hierarchy.DescentOutputSlots

namespace OAI
/-! # The integer bundle routing matrix of a populated good base -/

namespace Hierarchy.DescentBaseProfile
open scoped BigOperators Classical
noncomputable section
variable {E I C : Type*} [Fintype E] [Fintype I] [Fintype C] {Y : ℕ} [NeZero Y]

def matrixOfBundles (src dst : E → Fin Y) (i j : Fin Y) :=
  (Finset.univ.filter (fun e => src e=i ∧ dst e=j)).card

omit [NeZero Y] in
theorem matrix_rows (src dst : E → Fin Y) (i : Fin Y) :
    (∑j,matrixOfBundles src dst i j)=(Finset.univ.filter (fun e => src e=i)).card := by
  classical
  simpa [matrixOfBundles,Finset.filter_filter] using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.filter fun e => src e=i) Finset.univ dst

omit [NeZero Y] in
theorem matrix_columns (src dst : E → Fin Y) (j : Fin Y) :
    (∑i,matrixOfBundles src dst i j)=(Finset.univ.filter (fun e => dst e=j)).card := by
  classical
  simpa [matrixOfBundles,Finset.filter_filter,and_comm] using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.filter fun e => dst e=j) Finset.univ src

omit [NeZero Y] in
theorem input_bundle_load (owner : E → I) (atRow : I → Fin Y) (wt : I → ℝ) (u : ℝ)
    (actual : ∀i,((Finset.univ.filter fun e => owner e=i).card:ℝ)*u≤wt i) (j : Fin Y) :
    ((Finset.univ.filter fun e => atRow (owner e)=j).card:ℝ)*u ≤ inputLoad Finset.univ wt atRow j := by
  classical
  let bin := Finset.univ.filter (fun i => atRow i=j)
  have cnt := Finset.sum_card_fiberwise_eq_card_filter Finset.univ bin owner
  simp only [bin,Finset.mem_filter,Finset.mem_univ,true_and] at cnt
  rw [←cnt,Nat.cast_sum,Finset.sum_mul]
  unfold inputLoad
  rw [←Finset.sum_filter]
  apply Finset.sum_le_sum
  exact fun i _ => actual i

/-- The two per-terminal bounds needed by the rotor hold for the actual
cell multiplicities. Each old occurrence is assigned as a whole, and the
output depends only on the contact, its common capacity, and the ordinal
of the individual bundle within that contact. -/
theorem good_base_matrix_raw_of_rows (cap : C → ℝ) (N : C → ℕ) (wt : I → ℝ)
    (owner : E → I) (serial : E ↪ (Σ c,Fin (N c))) {B S u : ℝ}
    (sPos : 0<S) (uPos : 0<u) (unit : u≤B) (scale : (Y:ℝ)*B≤S)
    (_weights : ∀i,0≤wt i ∧ wt i≤B) (_full : ∑i,wt i≤2*S)
    (traffic : ∀c,(N c:ℝ)*u≤cap c) (budget : ∑c,cap c≤2*S)
    (contacts : 4*Fintype.card C≤Y)
    (actual : ∀i,((Finset.univ.filter fun e => owner e=i).card:ℝ)*u≤wt i)
    (input : I→Fin Y) (load : ∀j,inputLoad Finset.univ wt input j≤3*S/Y) :
    let fit := output_room cap sPos (fun c => (mul_nonneg (Nat.cast_nonneg _) uPos.le).trans (traffic c)) budget contacts
    let dst := fun e => outputSlot _ fit (chooseOutput cap N sPos uPos traffic e)
    (∀i,(∑j,(matrixOfBundles (input ∘ owner) (dst ∘ serial) i j:ℝ))≤9*S/(Y*u)) ∧
      (∀j,(∑i,(matrixOfBundles (input ∘ owner) (dst ∘ serial) i j:ℝ))≤9*S/(Y*u)) := by
  classical
  dsimp only
  let fit := output_room cap sPos (fun c => (mul_nonneg (Nat.cast_nonneg _) uPos.le).trans (traffic c)) budget contacts
  let dst := fun e => outputSlot _ fit (chooseOutput cap N sPos uPos traffic e)
  have hy : (0:ℝ)<Y := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Y)
  constructor
  · intro i
    rw [←Nat.cast_sum,matrix_rows]
    have used := (input_bundle_load owner input wt u actual i).trans (load i)
    have priced := (le_div_iff₀ hy).mp used
    apply (le_div_iff₀ (mul_pos hy uPos)).2
    change ((Finset.univ.filter (fun e => input (owner e)=i)).card:ℝ)*_≤_
    nlinarith only [priced,sPos]
  · intro j
    rw [←Nat.cast_sum,matrix_columns]
    have used := output_rows cap N sPos uPos traffic fit j
    change ((Finset.univ.filter fun e => dst e=j).card:ℝ)*u≤8*S/Y+u at used
    have unitBudget := (mul_le_mul_of_nonneg_left unit hy.le).trans scale
    have allowance : 8*S/Y+u≤9*S/Y := by
      apply (le_div_iff₀ hy).2
      rw [add_mul,div_mul_cancel₀ _ hy.ne']
      linarith
    have count : (Finset.univ.filter (fun e : E => dst (serial e)=j)).card≤
        (Finset.univ.filter (fun z => dst z=j)).card :=
      Finset.card_le_card_of_injOn serial (fun _ h => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩) serial.injective.injOn
    have realCount : ((Finset.univ.filter (fun e : E => dst (serial e)=j)).card:ℝ)≤
        (Finset.univ.filter (fun z => dst z=j)).card := by exact_mod_cast count
    have priced := (le_div_iff₀ hy).mp ((mul_le_mul_of_nonneg_right realCount uPos.le).trans (used.trans allowance))
    apply (le_div_iff₀ (mul_pos hy uPos)).2
    change ((Finset.univ.filter fun e => dst (serial e)=j).card:ℝ)*_≤_
    nlinarith only [priced]

theorem good_base_matrix_raw_with_load (cap : C → ℝ) (N : C → ℕ) (wt : I → ℝ)
    (owner : E → I) (serial : E ↪ (Σ c,Fin (N c))) {B S u : ℝ}
    (sPos : 0<S) (uPos : 0<u) (unit : u≤B) (scale : (Y:ℝ)*B≤S)
    (weights : ∀i,0≤wt i ∧ wt i≤B) (full : ∑i,wt i≤2*S)
    (traffic : ∀c,(N c:ℝ)*u≤cap c) (budget : ∑c,cap c≤2*S)
    (contacts : 4*Fintype.card C≤Y)
    (actual : ∀i,((Finset.univ.filter fun e => owner e=i).card:ℝ)*u≤wt i) :
    let fit := output_room cap sPos (fun c => (mul_nonneg (Nat.cast_nonneg _) uPos.le).trans (traffic c)) budget contacts
    let dst := fun e => outputSlot _ fit (chooseOutput cap N sPos uPos traffic e)
    ∃ input : I → Fin Y,
      (∀j,inputLoad Finset.univ wt input j≤3*S/Y) ∧
      (∀i,(∑j,(matrixOfBundles (input ∘ owner) (dst ∘ serial) i j:ℝ))≤9*S/(Y*u)) ∧
      (∀j,(∑i,(matrixOfBundles (input ∘ owner) (dst ∘ serial) i j:ℝ))≤9*S/(Y*u)) := by
  obtain ⟨input,load⟩ := input_rows wt (uPos.le.trans unit) (fun i=>(weights i).1)
    (fun i=>(weights i).2) full scale
  refine ⟨input,load,?_⟩
  exact good_base_matrix_raw_of_rows cap N wt owner serial sPos uPos unit scale weights full
    traffic budget contacts actual input load

theorem good_base_matrix_raw (cap : C → ℝ) (N : C → ℕ) (wt : I → ℝ)
    (owner : E → I) (serial : E ↪ (Σ c,Fin (N c))) {B S u : ℝ}
    (sPos : 0<S) (uPos : 0<u) (unit : u≤B) (scale : (Y:ℝ)*B≤S)
    (weights : ∀i,0≤wt i ∧ wt i≤B) (full : ∑i,wt i≤2*S)
    (traffic : ∀c,(N c:ℝ)*u≤cap c) (budget : ∑c,cap c≤2*S)
    (contacts : 4*Fintype.card C≤Y)
    (actual : ∀i,((Finset.univ.filter fun e => owner e=i).card:ℝ)*u≤wt i) :
    let fit := output_room cap sPos (fun c => (mul_nonneg (Nat.cast_nonneg _) uPos.le).trans (traffic c)) budget contacts
    let dst := fun e => outputSlot _ fit (chooseOutput cap N sPos uPos traffic e)
    ∃ input : I → Fin Y,
      (∀i,(∑j,(matrixOfBundles (input ∘ owner) (dst ∘ serial) i j:ℝ))≤9*S/(Y*u)) ∧
      (∀j,(∑i,(matrixOfBundles (input ∘ owner) (dst ∘ serial) i j:ℝ))≤9*S/(Y*u)) := by
  obtain ⟨input,_,rows,cols⟩ := good_base_matrix_raw_with_load cap N wt owner serial sPos uPos unit scale
    weights full traffic budget contacts actual
  exact ⟨input,rows,cols⟩

theorem good_base_matrix (cap : C → ℝ) (N : C → ℕ) (wt : I → ℝ)
    (owner : (Σ c,Fin (N c)) → I) {B S u : ℝ}
    (sPos : 0<S) (uPos : 0<u) (unit : u≤B) (scale : (Y:ℝ)*B≤S)
    (weights : ∀i,0≤wt i ∧ wt i≤B) (full : ∑i,wt i≤2*S)
    (traffic : ∀c,(N c:ℝ)*u≤cap c) (budget : ∑c,cap c≤2*S)
    (contacts : 4*Fintype.card C≤Y)
    (actual : ∀i,((Finset.univ.filter fun e => owner e=i).card:ℝ)*u≤wt i) :
    let fit := output_room cap sPos (fun c => (mul_nonneg (Nat.cast_nonneg _) uPos.le).trans (traffic c)) budget contacts
    let dst := fun e => outputSlot _ fit (chooseOutput cap N sPos uPos traffic e)
    ∃ input : I → Fin Y,
      (∀i,(∑j,(matrixOfBundles (input ∘ owner) dst i j:ℝ))≤9*S/(Y*u)) ∧
      (∀j,(∑i,(matrixOfBundles (input ∘ owner) dst i j:ℝ))≤9*S/(Y*u)) :=
  good_base_matrix_raw cap N wt owner (Function.Embedding.refl _) sPos uPos unit scale
    weights full traffic budget contacts actual

/-- Count the actual shared contact before restricting to either of its
endpoint bases. This one enumeration is used on both sides. -/
def contactCounts (label : E → C) (c : C) := (Finset.univ.filter fun e => label e=c).card

def sharedIndex (label : E → C) : E ≃ Σ c,Fin (contactCounts label c) :=
  (Equiv.sigmaFiberEquiv label).symm.trans (Equiv.sigmaCongrRight fun c =>
    Fintype.equivFinOfCardEq (show Fintype.card {e // label e=c}=contactCounts label c from by
      simp only [Fintype.card_subtype,contactCounts]))

omit [Fintype C] in
@[simp] theorem sharedIndex_contact (label : E → C) (e : E) :
    (sharedIndex label e).1=label e := rfl

/-- Restrict a global bundle key to one endpoint base of one common direct
contact. Its ordinal is copied from the global key, even when the two bases
have different neighbors, port budgets or local type enumerations. -/
def sideIndex {V : Type*} (side : C → V) {N : C → ℕ} (key : E ↪ Σ c,Fin (N c)) (v : V) :
    {e // side (key e).1=v} ↪ Σ c : {c // side c=v},Fin (N c.val) where
  toFun e := ⟨⟨(key e.val).1,e.property⟩,(key e.val).2⟩
  inj' _a _b h := Subtype.ext (key.injective <| congrArg
    (fun p : Σ c : {c // side c=v},Fin (N c.val) => (⟨p.1.val,p.2⟩ : Σ c,Fin (N c))) h)

omit [Fintype C] in
theorem same_direct_ordinal {V W : Type*} (left : C → V) (right : C → W)
    (label : E → C) (e : E) :
    ((sideIndex left (sharedIndex label).toEmbedding (left (label e))) ⟨e,rfl⟩).2.val =
    ((sideIndex right (sharedIndex label).toEmbedding (right (label e))) ⟨e,rfl⟩).2.val := rfl

end
end Hierarchy.DescentBaseProfile

end OAI
