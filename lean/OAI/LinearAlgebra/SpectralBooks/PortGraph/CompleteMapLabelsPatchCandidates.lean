import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsPatchObservation
import Mathlib.Data.Finset.Preimage

/-! # Reconstructing the candidate tests on the named vertices of a port view -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.MapLabels

open PlanarPatch PlanarCertSize

abbrev PatchRow (N : ℕ) := PortView (BaseAlphabet N) 1

variable {N : ℕ}

def rowName (s : PatchRow N) := vertexVal s.1 .preorderName
def rowRound (s : PatchRow N) := vertexVal s.1 .removalRound

def rowTarget (s : PatchRow N) (i : Fin 4) : Option ℕ :=
  (s.2 i).map fun p => vertexVal p.2 .preorderName

def namedStep (rows : Finset (PatchRow N)) (x : ℕ) (i : Fin 4) (y : ℕ) : Prop :=
  ∃ s ∈ rows, rowName s = x ∧ rowTarget s i = some y

def namedGraph (rows : Finset (PatchRow N)) : SimpleGraph ℕ where
  Adj x y := x ≠ y ∧ ((∃ i, namedStep rows x i y) ∨ (∃ i, namedStep rows y i x))
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def namedRemaining (rows : Finset (PatchRow N)) (t : ℕ) : Finset ℕ :=
  (rows.filter fun s => t < rowRound s).image rowName

def namedBoundary (rows : Finset (PatchRow N)) (R P : Finset ℕ) : ℕ := by
  classical
  exact ∑ x ∈ P, (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ R \ P, namedStep rows x i y)).card

def namedCandidates (rows : Finset (PatchRow N)) (K : ℕ) (ε : ℝ) (R : Finset ℕ) :
    Finset (Finset ℕ) := by
  classical
  exact R.powerset.filter fun P => P.Nonempty ∧ ((namedGraph rows).induce (P : Set ℕ)).Connected ∧
    P.card ≤ K ∧ (namedBoundary rows R P : ℝ) ≤ ε * P.card

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)
variable (b : V → BaseAlphabet N) (key : V ↪ ℕ) (hk : ∀ v, vertexVal (b v) .preorderName = key v)
variable (r : ℕ) (v : V)

abbrev observedRows := patchRows r (PortView.actual M.slots b (r+1) v)

def reportedBall (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun w =>
    t < vertexVal (b w) .removalRound ∧ (underlying M.graph.tail M.graph.head).edist v w ≤ r

include hk in
theorem namedRemaining_actual (t : ℕ) :
    namedRemaining (observedRows M b r v) t = (reportedBall M b r v t).map key := by
  classical
  ext x
  simp only [namedRemaining, Finset.mem_image, Finset.mem_filter, observedRows, patchRows_actual,
    Finset.mem_map, reportedBall, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s,⟨⟨w,hw,rfl⟩,ht⟩,rfl⟩
    exact ⟨w,⟨ht,hw⟩,(hk w).symm⟩
  · rintro ⟨w,⟨ht,hw⟩,rfl⟩
    exact ⟨_,⟨⟨w,hw,rfl⟩,ht⟩,hk w⟩

include hk in
theorem namedStep_actual {x y : V} (i : Fin 4)
    (hx : (underlying M.graph.tail M.graph.head).edist v x ≤ r) :
    namedStep (observedRows M b r v) (key x) i (key y) ↔
      ∃ j, M.graph.portStep M.slots x i = some (y,j) := by
  classical
  have target (a : V) : rowTarget (PortView.actual M.slots b 1 a) i =
      (M.graph.portStep M.slots a i).map (fun p => key p.1) := by
    cases h : M.graph.portStep M.slots a i <;> simp [rowTarget,PortView.actual,h,hk]
  constructor
  · rintro ⟨s,hs,hn,ht⟩
    obtain ⟨a,_,rfl⟩ := (patchRows_actual M b r v s).mp hs
    obtain rfl : a = x := key.injective ((hk a).symm.trans hn)
    rw [target] at ht
    cases h : M.graph.portStep M.slots a i with
    | none => simp [h] at ht
    | some p =>
      have he : p.1 = y := key.injective (by simpa [h] using ht)
      exact ⟨p.2, by simp [← he]⟩
  · rintro ⟨j,h⟩
    refine ⟨_, (patchRows_actual M b r v _).mpr ⟨x,hx,rfl⟩,hk x,?_⟩
    rw [target,h]
    rfl

include hk in
theorem namedConnected_actual {t : ℕ} {P : Finset V} (hP : P ⊆ reportedBall M b r v t) :
    ((namedGraph (observedRows M b r v)).induce (P.map key : Set ℕ)).Connected ↔
      Connected M.graph.tail M.graph.head P := by
  classical
  have hball {x : V} (hx : x ∈ P) :=
    (Finset.mem_filter.mp (hP hx)).2.2
  let iso : (underlying M.graph.tail M.graph.head).induce (P : Set V) ≃g
      (namedGraph (observedRows M b r v)).induce (P.map key : Set ℕ) :=
    { toEquiv := Finset.equivMap key P
      map_rel_iff' := by
        intro x y
        change (key x.val ≠ key y.val ∧ _) ↔ (underlying M.graph.tail M.graph.head).Adj x y
        simp only [ne_eq, key.injective.eq_iff]
        constructor
        · rintro ⟨hne,⟨i,hs⟩ | ⟨i,hs⟩⟩
          · exact (adj_iff_step M).mpr ⟨hne,i,(namedStep_actual M b key hk r v i (hball x.property)).mp hs⟩
          · exact ((adj_iff_step M).mpr ⟨Ne.symm hne,i,(namedStep_actual M b key hk r v i (hball y.property)).mp hs⟩).symm
        · intro h
          obtain ⟨hne,i,hs⟩ := (adj_iff_step M).mp h
          exact ⟨hne, Or.inl ⟨i, (namedStep_actual M b key hk r v i (hball x.property)).mpr hs⟩⟩ }
  exact iso.connected_iff.symm

include hk in
theorem namedBoundary_actual_slots {t : ℕ} {P : Finset V} (hP : P ⊆ reportedBall M b r v t) :
    namedBoundary (observedRows M b r v) ((reportedBall M b r v t).map key) (P.map key) =
      ∑ x ∈ P, (Finset.univ.filter (fun i : Fin 4 =>
        ∃ y j, M.graph.portStep M.slots x i = some (y,j) ∧ y ∈ reportedBall M b r v t ∧ y ∉ P)).card := by
  classical
  rw [namedBoundary, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  have hball := (Finset.mem_filter.mp (hP hx)).2.2
  constructor
  · rintro ⟨a,⟨ha,hp⟩,hs⟩
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j,hj⟩ := (namedStep_actual M b key hk r v i hball).mp hs
    exact ⟨y,j,hj,hy,fun h => hp (Finset.mem_map_of_mem _ h)⟩
  · rintro ⟨y,j,hj,hy,hp⟩
    exact ⟨key y,⟨Finset.mem_map_of_mem _ hy, fun h => hp ((Finset.mem_map' _).mp h)⟩,
      (namedStep_actual M b key hk r v i hball).mpr ⟨j,hj⟩⟩

end PortGraph.MapLabels

end

end SpectralBooks
end LinearAlgebra
end OAI
