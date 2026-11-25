import OAI.Hierarchy.DescentNativeInput
import OAI.Hierarchy.DescentInitialPackage

namespace OAI
/-! # Width accounts for the physical initial independent copies -/

namespace Hierarchy.DescentInitialHost

open Computability.BorderVNP.Crossing DescentSixParty Catalyst CatalystSubstitution CorrectionBatch CorrectionFrame
open ThreeFlat Routing
open scoped Classical BigOperators
noncomputable section

variable {F : Type*} [Field F] {D : ℕ}

private theorem collect_live {I : Type} [Fintype I] {P : I → Type*} {bits : ∀ i, P i → ℕ}
    (H : ∀ i, Histories F D (P i) (bits i)) (c : (Histories.collect H).Choice) :
    ((Histories.collect H).state c).liveWidth = ∑ i, ((H i).state (c i)).liveWidth :=
  block_core_width (fun i => ((H i).state (c i)).toWorld) (fun i => ((H i).state (c i)).core)

private theorem collect_tethers {I : Type} [Fintype I] {P : I → Type*} {bits : ∀ i, P i → ℕ}
    (H : ∀ i, Histories F D (P i) (bits i)) (c : (Histories.collect H).Choice) :
    ((Histories.collect H).state c).tetherWidth = ∑ i, ((H i).state (c i)).tetherWidth := by
  let A := fun i => ((H i).state (c i)).toWorld
  let core := fun i => ((H i).state (c i)).core
  have compl : (blockCore A core)ᶜ = blockCore A (fun i => (core i)ᶜ) := by
    ext ⟨i,e⟩
    exact Finset.mem_compl.trans ((not_congr (mem_blockCore A core i e)).trans
      (Finset.mem_compl.symm.trans (mem_blockCore A (fun j => (core j)ᶜ) i e).symm))
  change (∑ e ∈ (blockCore A core)ᶜ, (blockGraph A).width e) = _
  rw [compl]
  exact block_core_width A (fun i => (core i)ᶜ)

private theorem seed_live {P : Type*} [Fintype P] {bits : P → ℕ}
    (A : MarkedWorld F D P bits) (s : ℕ) (retain : A.graph.Site → Bool)
    (c : (Histories.seedInternal A s retain).Choice) :
    ((Histories.seedInternal A s retain).state c).liveWidth = s * A.liveWidth := by
  change (∑ e ∈ A.core, s * A.graph.width e) = s * ∑ e ∈ A.core, A.graph.width e
  rw [Finset.mul_sum]

private theorem seed_tethers {P : Type*} [Fintype P] {bits : P → ℕ}
    (A : MarkedWorld F D P bits) (s : ℕ) (retain : A.graph.Site → Bool)
    (c : (Histories.seedInternal A s retain).Choice) :
    ((Histories.seedInternal A s retain).state c).tetherWidth = s * A.tetherWidth := by
  change (∑ e ∈ A.coreᶜ, s * A.graph.width e) = s * ∑ e ∈ A.coreᶜ, A.graph.width e
  rw [Finset.mul_sum]

variable {k p : ℕ} (X : Approximation F k p)

theorem initial_liveWidth (S s : ℕ) (c : (initialGroup X S s).Choice) :
    ((initialGroup X S s).state c).liveWidth = S*s*Fintype.card X.network.copyGraph.Edge := by
  let keep : (markedInput X).graph.Site → Bool := Sum.elim (fun _ => true) (fun _ => false)
  let stack := Histories.seedInternal (markedInput X) s keep
  calc
    _ = ∑ i : Fin S, (stack.state (c i)).liveWidth := collect_live (fun _ : Fin S => stack) c
    _ = ∑ _ : Fin S, s * (markedInput X).liveWidth :=
      Finset.sum_congr rfl (fun i _ => seed_live (markedInput X) s keep (c i))
    _ = _ := by simp [input_width, Nat.mul_assoc]

theorem initial_tetherWidth (S s : ℕ) (c : (initialGroup X S s).Choice) :
    ((initialGroup X S s).state c).tetherWidth = S*s*Fintype.card (Port p X.width) := by
  let keep : (markedInput X).graph.Site → Bool := Sum.elim (fun _ => true) (fun _ => false)
  let stack := Histories.seedInternal (markedInput X) s keep
  calc
    _ = ∑ i : Fin S, (stack.state (c i)).tetherWidth := collect_tethers (fun _ : Fin S => stack) c
    _ = ∑ _ : Fin S, s * (markedInput X).tetherWidth :=
      Finset.sum_congr rfl (fun i _ => seed_tethers (markedInput X) s keep (c i))
    _ = _ := by simp [input_tethers, Nat.mul_assoc]

theorem initial_sites_le : Fintype.card (Site X.network.copyGraph) ≤ 10*(X.size+1) := by
  have h := («initialize» X).2.1
  omega

theorem initial_group_sites (S s : ℕ) (c : (initialGroup X S s).Choice) :
    Fintype.card ((initialGroup X S s).state c).graph.Site =
      S * Fintype.card (Site X.network.copyGraph) := by
  change Fintype.card (Σ _ : Fin S, Site X.network.copyGraph) = _
  simp [Fintype.card_sigma]

theorem initial_invoice (S s : ℕ) :
    (∀ c : (initialGroup X S s).Choice,
      ((initialGroup X S s).state c).liveWidth = S*s*Fintype.card X.network.copyGraph.Edge ∧
      ((initialGroup X S s).state c).tetherWidth = S*s*Fintype.card (Port p X.width) ∧
      Fintype.card ((initialGroup X S s).state c).graph.Site =
        S*Fintype.card (Site X.network.copyGraph)) ∧
    Fintype.card (Site X.network.copyGraph) ≤ 10*(X.size+1) ∧
    ∀ x : Port ((S*s)*p) (copiesWidth (S*s) X.width) → Bool,
      (initialGroup X S s).value (packagePins X S s x) =
        (independentCopies (S*s) X).coeff x :=
  ⟨fun c => ⟨initial_liveWidth X S s c, initial_tetherWidth X S s c, initial_group_sites X S s c⟩,
    initial_sites_le X, complete_input X S s⟩


end
end Hierarchy.DescentInitialHost

end OAI
