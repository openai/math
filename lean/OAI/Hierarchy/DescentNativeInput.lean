import OAI.Hierarchy.DescentSeedMarkedGraph
import OAI.Hierarchy.DescentSeedInternal
import OAI.Hierarchy.DescentInitialCopies
import OAI.Hierarchy.DescentHubNetwork

namespace OAI
/-! # Field-valued physical initial histories at the independent-copy package boundary -/

namespace Hierarchy.DescentInitialHost
open Computability.BorderVNP.Crossing DescentSixParty Catalyst CatalystSubstitution CorrectionBatch CorrectionFrame
open ThreeFlat Routing
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {k p : ℕ} (X : Approximation F k p)
local notation "P" => Fin (Fintype.card (Port p X.width))

theorem markedInput_value (x : Port p X.width→Bool) :
    (markedInput X).value (fun i _=>x ((Fintype.equivFin _).symm i))=X.coeff x :=
  (hub_value X.network.copyGraph X.network.copyTable _).trans ((physical_output X).2.2 x)

theorem input_width : (markedInput X).liveWidth=Fintype.card X.network.copyGraph.Edge := by
  let N := X.network.copyGraph
  change (∑ e ∈ Finset.univ.map (Function.Embedding.inl : N.Edge ↪ N.Edge ⊕ P),
    Sum.elim N.width (fun _ : P => 1) e) = Fintype.card N.Edge
  rw [Finset.sum_map]
  change (∑ i : N.Edge, N.width i) = _
  exact (Finset.sum_congr rfl (fun i _ => (physical_output X).1.1 i)).trans (by simp [N])

theorem input_tethers : (markedInput X).tetherWidth=Fintype.card (Port p X.width) := by
  let N := X.network.copyGraph
  let rim := Finset.univ.map (Function.Embedding.inr : P ↪ N.Edge ⊕ P)
  have comp : (markedInput X).coreᶜ = rim := by
    ext e
    rw [Finset.mem_compl]
    let left := (Function.Embedding.inl : N.Edge ↪ N.Edge ⊕ P)
    let right := (Function.Embedding.inr : P ↪ N.Edge ⊕ P)
    change (e ∉ Finset.univ.map left) ↔ e ∈ Finset.univ.map right
    rcases e with old | pin
    · constructor
      · intro missing
        exact False.elim (missing (Finset.mem_map.mpr ⟨old, Finset.mem_univ _, rfl⟩))
      · intro h
        obtain ⟨_, _, eq⟩ := Finset.mem_map.mp h
        cases eq
    · constructor
      · intro _
        exact Finset.mem_map.mpr ⟨pin, Finset.mem_univ _, rfl⟩
      · intro _ h
        obtain ⟨_, _, eq⟩ := Finset.mem_map.mp h
        cases eq
  rw [MarkedWorld.tetherWidth,comp]
  change (∑ e ∈ rim, Sum.elim N.width (fun _ : P => 1) e) = _
  dsimp only [rim]
  rw [Finset.sum_map]
  change (∑ _ : P, 1) = _
  simp

/-- R independent sets of physical tensor copies, each with its own selected
local histogram and field scalar. All coordinates remain addressable by the
ordinary independentCopies interface, including every catalyst direction. -/
def initialGroup (R s : ℕ) :=
  Histories.collect (fun _ : Fin R => Histories.seedInternal (markedInput X) s (Sum.elim (fun _=>true) (fun _=>false)))

def packagePins (R s : ℕ) (x : Port ((R*s)*p) (copiesWidth (R*s) X.width)→Bool) :
    Ports (fun _ : Σ _i : Fin R,P=>s*1) :=
  fun q => stackRows (fun j : Fin s => fun _ : Fin 1=>
    x (copiesPortEquiv (p:=p) (R*s) X.width (finProdFinEquiv (q.1,j),(Fintype.equivFin _).symm q.2)))

theorem complete_input (R s : ℕ) (x : Port ((R*s)*p) (copiesWidth (R*s) X.width)→Bool) :
    (initialGroup X R s).value (packagePins X R s x)=(independentCopies (R*s) X).coeff x := by
  unfold initialGroup
  rw [Histories.collect_value,CatalystSubstitution.copies_coeff]
  calc
    _ = ∏i : Fin R, ∏ j : Fin s,X.coeff (fun port=>x (copiesPortEquiv (p:=p) (R*s) X.width
        (finProdFinEquiv (i,j),port))) := by
      apply Finset.prod_congr rfl
      intro i _
      refine (Histories.seedInternal_value (markedInput X) s _ _).trans ?_
      apply Finset.prod_congr rfl
      intro j _
      simpa only [packagePins,rowAt_stackRows] using markedInput_value X
        (fun p=>x (copiesPortEquiv (R*s) X.width (finProdFinEquiv (i,j),p)))
    _ = _ := by
      let term (i : Fin (R*s)) := X.coeff (fun p => x (copiesPortEquiv (R*s) X.width (i,p)))
      exact (Fintype.prod_prod_type (fun ij : Fin R × Fin s => term (finProdFinEquiv ij))).symm.trans
        (finProdFinEquiv.prod_comp term)

end
end Hierarchy.DescentInitialHost

end OAI
