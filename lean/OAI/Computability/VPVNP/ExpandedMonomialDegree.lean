import OAI.Computability.VPVNP.CompressionDegreeCoverage

/-!
# Degrees of paths in an expanded network contraction

The exponent of a complete path is the sum of its local map exponents. At a
placement node the previous factors are visited once in their placement fiber.
This associates each expanded path to a branch of the term history and bounds
its total degree using the map records of that same branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace NetworkKernel

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A}
variable {N : Network}

/-- Pushing a vertex factor adds the degrees of the kernel and of its children. -/
theorem Term.pushWitness_degree_le (t : Term A N) (F : Factors A N)
    (W : ∀ u z, MonomialWitness κ (F u z)) (K : ∀ v a z, MonomialWitness κ (t.kernel v a z))
    (rec : t.output.Site → SiteRecords) (previous : N.Site → ℕ) (B : ℕ)
    (hW : ∀ u z c, (∑ l, (W u z).exponents c l) ≤ previous u * B)
    (hK : ∀ v a z c, (∑ l, (K v a z).exponents c l) ≤ ∑ j, (rec v).degree j)
    (hB : ∀ v j, (rec v).degree j ≤ B) (v : t.output.Site) (z : t.output.Half v)
    (c : (t.pushWitness F W K v z).Choice) :
    (∑ l, (t.pushWitness F W K v z).exponents c l) ≤ t.pushHistorySize rec previous v * B := by
  classical
  obtain ⟨⟨a, children, own⟩, rfl⟩ := (t.pushChoice F W K v z).symm.surjective c
  simp only [Term.pushChoice_exponents, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have hc : Fintype.card (rec v).Map ≤ (rec v).count := by unfold SiteRecords.count; omega
  have hk : (∑ j, (rec v).degree j) ≤ (rec v).count * B := calc
    _ ≤ ∑ _ : (rec v).Map, B := Finset.sum_le_sum fun j _ => hB v j
    _ ≤ _ := by simpa using Nat.mul_le_mul_right B hc
  rw [Term.pushHistorySize, Nat.add_mul, Finset.sum_mul, Nat.add_comm]
  exact Nat.add_le_add ((hK v a z own).trans hk) (Finset.sum_le_sum fun u _ => hW _ _ _)

namespace History

/-- Each expanded choice selects a single term chain. Its records suffice to
bound the exponents for any valid input occurrence bound and map degree cap. -/
def DegreeBound {Z : Type} {Y : Z → Network} (H : History A N) (K : H.KernelWitnesses κ)
    (chains : ∀ z, TermChain A N (Y z)) : Prop :=
  ∀ (F : Factors A N) (W : ∀ u z, MonomialWitness κ (F u z))
    (c : (H.expandedWitness K F W).Choice), ∃ z : Z, ∀ (previous : N.Site → ℕ) (B : ℕ),
    (∀ u x w, (∑ l, (W u x).exponents w l) ≤ previous u * B) →
    (chains z).AllRecordsLe B →
    (∑ l, (H.expandedWitness K F W).exponents c l) ≤ ∑ v, (chains z).occurrences previous v * B

theorem DegreeBound.stop (K : (History.stop (k := A) (N := N)).KernelWitnesses κ) :
    DegreeBound .stop K (fun _ : Unit => TermChain.done N) := by
  intro F W c
  obtain ⟨⟨a, choices⟩, rfl⟩ := (History.stopChoice K F W).symm.surjective c
  refine ⟨(), fun previous B hW _ => ?_⟩
  simp only [History.stopChoice_exponents, TermChain.occurrences]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun v _ => hW _ _ _

theorem DegreeBound.branch (s : Step A N) (tail : ∀ i, History A (s.term i).output)
    (K : (History.branch s tail).KernelWitnesses κ)
    (rec : ∀ i, (s.term i).output.Site → SiteRecords)
    {Z : s.Choice → Type} {Y : ∀ i, Z i → Network}
    (chains : ∀ i z, TermChain A (s.term i).output (Y i z))
    (hK : ∀ i v a z c, (∑ l, (K.1 i v a z).exponents c l) ≤ ∑ j, (rec i v).degree j)
    (hTail : ∀ i, DegreeBound (tail i) (K.2 i) (chains i)) :
    DegreeBound (History.branch s tail) K (fun (z : (i : s.Choice) × Z i) =>
      TermChain.more (s.term z.1) (rec z.1) (chains z.1 z.2)) := by
  intro F W c
  obtain ⟨⟨i, rest⟩, rfl⟩ := (History.branchChoice s tail K F W).symm.surjective c
  obtain ⟨z, hz⟩ := hTail i _ _ rest
  refine ⟨⟨i, z⟩, fun previous B hW hB => ?_⟩
  simp only [History.branchChoice_exponents, TermChain.occurrences]
  exact hz _ B
    ((s.term i).pushWitness_degree_le F W (K.1 i) (rec i) previous B hW (hK i) hB.2.1) hB.2.2

open private transportWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory

/-- Identify a pass output with the network of the next state, transporting
the history, witnesses, and selected term chains together. -/
theorem DegreeBound.castInput {N' : Network} (e : N = N') {Z : Type} {Y : Z → Network}
    (H : History A N) (K : H.KernelWitnesses κ) (chains : ∀ z, TermChain A N (Y z))
    (h : DegreeBound H K chains) :
    DegreeBound (e ▸ H) (transportWitnesses e H K) (fun z => e ▸ chains z) := by
  cases e
  exact h

/-- Local RAM paths have exponent zero before any kernels are pushed. -/
theorem DegreeBound.expandedCount {Z : Type} {Y : Z → Network} (H : History A N)
    (K : H.KernelWitnesses κ) (chains : ∀ z, TermChain A N (Y z))
    (h : DegreeBound H K chains) (P : ∀ u, N.Half u → Type) [∀ u x, Fintype (P u x)]
    (c : (H.expandedCount K P).Choice) : ∃ z : Z, ∀ B, (chains z).AllRecordsLe B →
      (∑ l, (H.expandedCount K P).exponents c l) ≤
        ∑ v, (chains z).occurrences (fun _ => 1) v * B := by
  obtain ⟨z, hz⟩ := h _ (fun u x => MonomialWitness.paths κ (P u x)) c
  exact ⟨z, fun B hB => hz _ B (fun _ _ _ => by simp [MonomialWitness.paths]) hB⟩

end History
end NetworkKernel

namespace Compression.StateExecution

open NetworkKernel

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {κ : L → R}
variable {a g b n : ℕ} {X : State a g}

/-- Lift per-site degree coverage to each complete monomial of a state execution. -/
theorem history_degreeBound (E : StateExecution R b n X) (K : E.MapWitnesses κ)
    (rec : E.Records) (hc : E.DegreeCovered K rec) :
    E.history.DegreeBound (E.historyWitnesses K) (E.termChain rec) := by
  induction E with
  | done X => exact History.DegreeBound.stop _
  | more p tail ih =>
    apply History.DegreeBound.branch p.step (fun i => (p.output_eq i).symm ▸ (tail i).history)
      ((more p tail).historyWitnesses K) rec.1
      (Z := fun i => (tail i).Choices) (Y := fun i z => ((tail i).finalState z).network)
      (fun i z => (p.output_eq i).symm ▸ (tail i).termChain (rec.2 i) z) hc.1
    exact fun i => (ih i (K.2 i) (rec.2 i) (hc.2 i)).castInput (p.output_eq i).symm _ _ _

end Compression.StateExecution

end VPVNP
end Computability
end OAI
