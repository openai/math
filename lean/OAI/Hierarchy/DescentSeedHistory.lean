import OAI.Hierarchy.DescentSeedBoundaryPattern
import OAI.Hierarchy.DescentFiniteWordRead
import OAI.Hierarchy.DescentPrimitivePaletteLabels
import OAI.Hierarchy.DescentQuotientHistory
import OAI.Hierarchy.DescentSeedMenuSize
import Mathlib.Data.List.GetD

namespace OAI
/-! # The bounded, site-independent Boolean atom at a seeded trivalent vertex -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentInitialHost DescentPhysicalSplit
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} {D : ℕ} {P : Type} [Fintype P]
variable (N : Network D P (fun _=>1))

def censusScalar [CommSemiring F] {s : ℕ} (t : CensusTag s) (cols : List (List Bool)) : F :=
  if ∀p, ((Finset.univ : Finset (Fin s)).filter fun i=>
    (fun j : Fin t.1.val=>(cols.getD j.val []).getD i.val false)=p).card=(t.2 p).val
    then 1 else 0

def censusRole {s : ℕ} (tri : N.Trivalent) (v : N.Site) (h : Count N s v) : CensusTag s :=
  ⟨⟨seedArity N v,Nat.lt_succ_of_le (seedArity_le N tri v)⟩,h∘(seedPattern N tri.1 v).symm⟩

def censusRecipe {s : ℕ} (tri : N.Trivalent) (v : N.Site) (h : Count N s v) :
    Recipe (CensusTag s) (Boundary (stacked N s) v) :=
  atom (censusRole N tri v h) (seedArity N v) (boundaryIndex N v).symm

private theorem read_single {s n : ℕ} (width : n = 1) (w : Word (s*n))
    (i : Fin s) (j : Fin n) : (wordList w).getD i.val false = rowAt w i j := by
  let k := finProdFinEquiv (i,j)
  have jzero : j.val = 0 := by have h := j.isLt; omega
  have ix : k.val = i.val := by
    change j.val + n*i.val = i.val
    simp [jzero,width]
  calc
    _ = (wordList w).getD k.val false := congrArg (fun a => (wordList w).getD a false) ix.symm
    _ = w k := finiteWord_read w k false

theorem census_represents [Field F] (s : ℕ) (tri : N.Trivalent) (h : ∀v,Count N s v) :
    Represents (stacked N s) (censusScalar (F:=F)) (seedLocal N s h) (fun v=>censusRecipe N tri v (h v)) := by
  intro v z x
  change N.Site at v
  refine (atom_value (B:=Boundary N v) (censusScalar (F:=F)) (censusRole N tri v (h v))
    (seedArity N v) (boundaryIndex N v).symm (input (stacked N s) z x)).trans ?_
  let row (i : Fin s) : Pattern N v := (fun e=>rowAt (z e) i,fun p=>rowAt (x p) i)
  let data := input (stacked N s) z x
  let pattern := seedPattern N tri.1 v
  let cols := List.ofFn fun k=>data ((boundaryIndex N v).symm k)
  have digit (i : Fin s) (j : Fin (seedArity N v)) :
      (cols.getD j.val []).getD i.val false = pattern (row i) j := by
    dsimp only [cols]
    rw [finiteWord_read]
    obtain ⟨a,rfl⟩ := (boundaryIndex N v).surjective j
    cases a with
    | inl e =>
      simp only [pattern,seedPattern,Equiv.coe_fn_mk,Equiv.symm_apply_apply]
      exact read_single (tri.1 e.val) (z e) i _
    | inr p =>
      simp only [pattern,seedPattern,Equiv.coe_fn_mk,Equiv.symm_apply_apply]
      exact read_single rfl (x p) i _
  have frequency (p : Fin (seedArity N v) → Bool) :
      (Finset.univ.filter fun i : Fin s => (fun j : Fin (seedArity N v) => (cols.getD j.val []).getD i.val false) = p).card =
        (counts N row (pattern.symm p)).val := by
    simp only [counts, Fin.val_mk]
    apply congrArg (fun rows : Finset (Fin s) => rows.card)
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [show (fun j : Fin (seedArity N v) => (cols.getD j.val []).getD i.val false) = pattern (row i) from funext (digit i)]
    exact pattern.eq_symm_apply.symm
  unfold censusScalar seedLocal censusTable
  apply if_congr ?_ rfl rfl
  change (∀p, (Finset.univ.filter fun i : Fin s =>
    (fun j : Fin (seedArity N v) => (cols.getD j.val []).getD i.val false) = p).card = ((h v) (pattern.symm p)).val) ↔ h v = counts N row
  constructor
  · intro eq
    funext q
    apply Fin.ext
    simpa only [Equiv.symm_apply_apply] using (eq (pattern q)).symm.trans (frequency (pattern q))
  · intro eq p
    rw [eq]
    exact frequency p

theorem censusTag_card (s : ℕ) : Fintype.card (CensusTag s)≤4*(s+1)^8 := by
  rw [Fintype.card_sigma]
  apply (Finset.sum_le_sum (g:=fun _=>(s+1)^8) fun m _=>?_).trans_eq (by simp)
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by decide) (by omega : m.val≤3))

end
end Hierarchy.DescentKernelHistory

end OAI
