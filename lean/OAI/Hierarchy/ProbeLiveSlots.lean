import OAI.Hierarchy.ProbeAdvisedPurchase
import OAI.Hierarchy.ProbeExcess
import Mathlib.Data.List.Nodup

namespace OAI
/-! # Actual purchased rows embed into the signed adaptive commodity inventory -/

namespace Hierarchy.AdaptiveProbe
open scoped Classical BigOperators
noncomputable section

private theorem scan_selected {V : Type*} [DecidableEq V] (ps : List (List V)) (marked : Finset V) :
    ∀ p ∈ (scanPaths ps marked).1, p ∈ ps := by
  induction ps generalizing marked with
  | nil => simp [scanPaths]
  | cons p ps ih =>
    by_cases use : p.toFinset ⊆ marked
    · simp only [scanPaths,ite_eq_left use,List.mem_cons]
      intro q h; rcases h with eq|old
      · exact Or.inl eq
      · exact Or.inr (ih _ q old)
    · intro q h
      exact List.mem_cons_of_mem p (ih _ q (by simpa only [scanPaths,ite_eq_right use] using h))

/-- The retained list supplies both the actual marked tile and its unique index in
its H-chain. Distinct purchased H-chains in this native scan have disjoint rows. -/
def selectedEmbedding {V : Type*} [DecidableEq V] {H : ℕ} (ps : List (List V)) (marked : Finset V)
    (good : ∀ p ∈ ps, p.length=H ∧ p.Nodup) : Fin (scanPaths ps marked).1.length × Fin H ↪ V := by
  let kept := (scanPaths ps marked).1
  have spec (i : Fin kept.length) := good (kept.get i) (scan_selected ps marked _ (List.get_mem ..))
  let atRow (i : Fin kept.length) (j : Fin H) := (kept.get i).get (Fin.cast (spec i).1.symm j)
  refine ⟨fun point => atRow point.1 point.2,?_⟩
  rintro ⟨i,j⟩ ⟨i',j'⟩ eq
  have member (i : Fin kept.length) (j : Fin H) : atRow i j ∈ (kept.get i).toFinset :=
    List.mem_toFinset.mpr (List.get_mem ..)
  have fail (i i' : Fin kept.length) (lt : i < i') (j j' : Fin H) (same : atRow i j=atRow i' j') : False := by
    have disj := List.pairwise_iff_get.mp (scan_disjoint ps marked).2 i i' lt
    exact Finset.disjoint_left.mp disj (member i j) (same.symm ▸ member i' j')
  change atRow i j=atRow i' j' at eq
  have indices : i=i' := by
    rcases lt_trichotomy i i' with lt|e|gt
    · exact False.elim (fail _ _ lt _ _ eq)
    · exact e
    · exact False.elim (fail _ _ gt _ _ eq.symm)
  subst i'
  have jEq := (List.nodup_iff_injective_get.mp (spec i).2) eq
  exact Prod.ext rfl (Fin.ext (congrArg (fun v : Fin (kept.get i).length => v.val) jEq))

theorem selectedEmbedding_mem {V : Type*} [DecidableEq V] {H : ℕ} (ps : List (List V)) (marked : Finset V)
    (good : ∀ p ∈ ps, p.length=H ∧ p.Nodup) (i : Fin (scanPaths ps marked).1.length) (j : Fin H) :
    selectedEmbedding ps marked good (i,j) ∈ marked := by
  have subset := (scan_disjoint ps marked).1 _ (List.get_mem (scanPaths ps marked).1 i)
  exact subset (List.mem_toFinset.mpr (List.get_mem ..))

theorem selectedEmbedding_next {V : Type*} [DecidableEq V] {H : ℕ} (ps : List (List V)) (marked : Finset V)
    (good : ∀ p ∈ ps, p.length=H ∧ p.Nodup) (edge : V → V → Prop)
    (chain : ∀ p ∈ ps, p.IsChain edge) (i : Fin (scanPaths ps marked).1.length) {j : ℕ} (hj : j+1<H) :
    edge (selectedEmbedding ps marked good (i,⟨j,by omega⟩)) (selectedEmbedding ps marked good (i,⟨j+1,hj⟩)) := by
  let kept := (scanPaths ps marked).1.get i
  have mem : kept ∈ ps := scan_selected ps marked kept (List.get_mem ..)
  have length := (good kept mem).1
  exact List.isChain_iff_getElem.mp (chain kept mem) j (by omega)

/-- Global slots preserve the stage and signed axis in the actual stock address.
Thus coincident tile numbers in different stage/sign scans remain separate inventory. -/
def commoditySlots {V : Type*} {N k H : ℕ} (counts : Fin N → (Fin k × Bool) → ℕ)
    (rows : ∀ s c, Fin (counts s c) × Fin H ↪ V) :
    ((Σ s : Fin N, Σ c : Fin k × Bool, Fin (counts s c)) × Fin H) ↪ Commodity V N k where
  toFun p := .inr ((rows p.1.1 p.1.2.1 (p.1.2.2,p.2),p.1.1),p.1.2.1)
  inj' := by
    rintro ⟨⟨s,c,i⟩,j⟩ ⟨⟨s',c',i'⟩,j'⟩ eq
    have pair := Sum.inr.inj eq
    have sc := congrArg (fun t => t.1.2) pair
    have cc := congrArg Prod.snd pair
    dsimp at sc cc
    subst s'; subst c'
    have index := (rows s c).injective (congrArg (fun t => t.1.1) pair)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj index
    rfl

end
end Hierarchy.AdaptiveProbe

namespace Hierarchy.ProbeStage
open AdaptiveProbe ProtocolRAM
open scoped Classical BigOperators
noncomputable section

variable {h d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))

def liveCount (s : StageAt h d) (c : Fin k × Bool) := (advisedPurchases S π s depth (marked s c)).1.length

abbrev LiveChains := Σ s : StageAt h d, Σ c : Fin k × Bool, Fin (liveCount S π depth marked s c)

theorem liveChain_card : Fintype.card (LiveChains S π depth marked) = ∑ s, ∑ c, liveCount S π depth marked s c := by
  simp only [LiveChains,Fintype.card_sigma,Fintype.card_fin]

def liveDigit (s : StageAt h d) (c : Fin k × Bool) :=
  let sh := stageAt h d s
  let rows := ProtocolRAMPurchaseOwners.successor (advisedStage h d π s) (Fintype.equivFin sh.Group).toEmbedding
    (D:=S.degree) (portDigits (S.rows sh.span))
  let ps := PurchaseDFS.candidates rows depth
  selectedEmbedding (H:=depth+1) ps (marked s c) fun _p mem =>
    ⟨((PurchaseDFS.mem_candidates rows).mp mem).1,((PurchaseDFS.mem_candidates rows).mp mem).2.1⟩

def liveSlots : (LiveChains S π depth marked × Fin (depth+1)) ↪ Commodity (Fin (2^h)) (permutationFabric h d).shapes.length k :=
  commoditySlots (liveCount S π depth marked) (liveDigit S π depth marked)

theorem liveSlot_marked (path : LiveChains S π depth marked) (j : Fin (depth+1)) :
    (liveDigit S π depth marked path.1 path.2.1 (path.2.2,j)) ∈ marked path.1 path.2.1 :=
by
  let sh := stageAt h d path.1
  let rows := ProtocolRAMPurchaseOwners.successor (advisedStage h d π path.1) (Fintype.equivFin sh.Group).toEmbedding
    (D:=S.degree) (portDigits (S.rows sh.span))
  exact selectedEmbedding_mem (PurchaseDFS.candidates rows depth) (marked path.1 path.2.1)
    (fun p mem => ⟨((PurchaseDFS.mem_candidates rows).mp mem).1,((PurchaseDFS.mem_candidates rows).mp mem).2.1⟩) path.2.2 j

end
end Hierarchy.ProbeStage

end OAI
