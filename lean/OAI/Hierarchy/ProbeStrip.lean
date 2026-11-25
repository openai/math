import OAI.Hierarchy.ProbeBallPrices

namespace OAI
/-! # One physical price-test format for a strip of tile links and free joins -/

namespace Hierarchy.AdaptiveProbe.Strip
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical BigOperators
noncomputable section

variable {n k : ℕ}

def steps (n : ℕ) (i : Fin (n+1)) : Finset (Fin (n+1)) :=
  Finset.univ.filter fun j => i.val+1=j.val ∨ j.val+1=i.val

private theorem from_zero (j : ℕ) (bound : j≤n) : (⟨j,by omega⟩ : Fin (n+1)) ∈
    neighborhood (steps n) 0 j := by
  induction j with
  | zero => exact Finset.mem_singleton_self _
  | succ j ih =>
    apply (mem_neighborhood_step _ _ _ _).mpr
    exact ⟨⟨j,by omega⟩,ih (by omega),Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩)⟩

/-- The physical column at ordinal i is in the rooted radius-n strip test. -/
def column (n : ℕ) : Fin (n+1) ↪ TestColumns (steps n) 0 n where
  toFun i := ⟨i,by
    have start := from_zero (n:=n) i.val (by omega)
    have enlarge {r s : ℕ} (le : r≤ s) : neighborhood (steps n) 0 r ⊆ neighborhood (steps n) 0 s := by
      induction le with
      | refl => exact fun _ h => h
      | step _ prev => exact fun y h => (mem_neighborhood_step _ _ _ _).mpr ⟨y,prev h,Or.inl rfl⟩
    exact enlarge (by omega : i.val≤n) start⟩
  inj' := fun _ _ h => congrArg Subtype.val h

/-- The n printed consecutive physical edge descriptions; every color runs on a
separate layer, with the same price on each layer of a given edge. -/
def horizontal (n : ℕ) (i : Fin n) : DistinctPair (TestColumns (steps n) 0 n) where
  left := column n i.castSucc
  right := column n i.succ
  apart := fun eq => by have h := congrArg Fin.val ((column n).injective eq); simp at h

theorem hosts (len : Fin n → ℝ) (cost : ∀ i, len i≤1) (x y : TestColumns (steps n) 0 n)
    (near : y ∈ testNext (steps n) 0 n x) : ∃ e, len e ≤ 1 ∧
    (((horizontal n e).left=x ∧ (horizontal n e).right=y) ∨ ((horizontal n e).left=y ∧ (horizontal n e).right=x)) := by
  have hit := (Finset.mem_filter.mp (Finset.mem_subtype.mp near)).2
  rcases hit with fwd|back
  · let e : Fin n := ⟨x.val.val,by omega⟩
    exact ⟨e,cost e,Or.inl ⟨Subtype.ext (Fin.ext rfl),Subtype.ext (Fin.ext fwd)⟩⟩
  · let e : Fin n := ⟨y.val.val,by omega⟩
    exact ⟨e,cost e,Or.inr ⟨Subtype.ext (Fin.ext rfl),Subtype.ext (Fin.ext back)⟩⟩

/-- A single uniform M and then a positive discrepancy slack for every occurrence,
permutation, and time, since only the live commodity prices vary. -/
theorem strip_flattening {F A B : Type*} [Field F] [Fintype A] [Fintype B]
    [SiteNaming (ColumnSite (TestColumns (steps n) 0 n) k)]
    (hk : 0<k) (no : ¬HasSpectralFlat F (k+1)) (len : Fin n → ℝ) (cost : ∀ i,len i≤1)
    (d : A → LocalCommodity (TestColumns (steps n) 0 n) k)
    (buy : B → DistinctPair (TestColumns (steps n) 0 n)) {η : ℝ} (resolution : 0<η) :
    letI : Nonempty (ColumnWires.Role (TestColumns (steps n) 0 n) (Fin n) (A ⊕ B) k) := ⟨.catalyst (column n 0) ⟨0,hk⟩⟩
    ∃ M₀ : ℕ, ∀ M : ℝ, 0<M → M₀≤M → ∀ cap : A → ℝ,
    ∃ ε : ℝ, 0<ε ∧ ∀ y ∈ Set.Icc (0:A → ℝ) cap,
      let wires := ColumnWires.wires (horizontal n) (LocalCommodity.extraEnds d buy)
      let req := ColumnWires.demand (I:=TestColumns (steps n) 0 n) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B))
      let prices := ColumnWires.quote M len (LocalCommodity.extraPrice (B:=B) y)
      Probe.discrepancy F wires req prices ≤ ε →
      ∃ z : TestColumns (steps n) 0 n → Coordinates k,
      (∀ j, len j=0 → z (column n j.castSucc) = z (column n j.succ)) ∧
      ∀ l, |(LocalCommodity.sources (H:=Fin n) d buy l).quote M prices -
        (LocalCommodity.sources (H:=Fin n) d buy l).model z| < η := by
  obtain ⟨N,allM⟩ := LocalCommodity.test_flattening (steps n) 0 n hk no (horizontal n) len (hosts len cost) d buy resolution
  refine ⟨N,?_⟩; intro M pm large cap
  obtain ⟨ε,pos,all⟩ := allM M pm large cap
  refine ⟨ε,pos,?_⟩; intro y box wires req prices pass
  obtain ⟨z,joins,obs⟩ := all y box pass
  exact ⟨z,fun j free => joins _ _ ⟨j,free,rfl,rfl⟩,obs⟩

end
end Hierarchy.AdaptiveProbe.Strip

end OAI
