import OAI.Hierarchy.DescentSeedPaidCableStage
import OAI.Hierarchy.DescentSeedCableFieldSource
import OAI.Hierarchy.DescentSeedSignedFull
import OAI.Hierarchy.DescentCollectedPhase
import OAI.Hierarchy.DescentSeedAtomBudget
import OAI.Hierarchy.DescentStageAllWidths

namespace OAI
/-! # The genuine paid ordinary epoch starts at the actual physical source -/

namespace Hierarchy.DescentInitialHost
open DescentSixParty DescentCompiler DescentHostDegree Catalyst DescentColonies
open scoped Classical BigOperators

noncomputable section
variable {F : Type} [Field F] {cp p : ℕ}

theorem paid_group_seed_rows (X : Approximation F cp p) (G : PoweredGadget F) (S : AtomSchedule)
    {z f k : ℕ} (hz : 0<z) (field : 0<k) (positive : 0<S.height)
    (cut : packExponent 20 3≤f) (radix : S.radix=2^k)
    (width : k=groupBits S.rounds S.height S.hostGain S.capGain f)
    (budget : 10*(X.size+1)≤S.initialSites) (c : (initialGroup X S.copies (z*G.b)).Choice) :
    let s := z*G.b
    let wire := S.epochPower^S.priceExponent
    let q := 1/((s:ℝ)*wire)
    let ε := ((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower
    ∃A : GroupStage ((initialGroup X S.copies s).state c) G q ε
      (Fin (S.groupCount 0)) (Site X.network.copyGraph) k,
      A.StateBounds S 0 ∧ A.wire=wire ∧ A.hist=s ∧ A.cap=256 ∧ A.z=z ∧ A.degree=3 ∧
        A.pos=seedPos X c (S.initialDigits radix) ∧ A.block=seedBlock X c (S.initialDigits radix) ∧
        HEq A.records (seedRecords X c) ∧ (∀v,(A.records v).length=(seedRecords X c v).length) ∧
        (fun v=>A.hub (A.pos v).2)=seedHub X c ∧ A.hub=hubFlag X.network.copyGraph ∧ A.near=near X.network.copyGraph ∧
        DescentPackedSeed.Signed.Plane.Receipt X S A ((DescentSeedRoot.oldOrder X c).trans Fin.valEmbedding)
          (Fintype.equivFin _).toEmbedding rfl := by
  obtain ⟨A,valid,words,atoms,cap,grain,degree,sites,blocks,records,counts,hubs,hostHubs,nearby,signed,_⟩ :=
    paid_group_seed_cables X G S hz field positive cut radix width budget c
  exact ⟨A,valid,words,atoms,cap,grain,degree,sites,blocks,records,counts,hubs,hostHubs,nearby,signed⟩

theorem paid_group_seed (X : Approximation F cp p) (G : PoweredGadget F) (S : AtomSchedule)
    {z f k : ℕ} (hz : 0<z) (field : 0<k) (positive : 0<S.height)
    (cut : packExponent 20 3≤f) (radix : S.radix=2^k)
    (width : k=groupBits S.rounds S.height S.hostGain S.capGain f)
    (budget : 10*(X.size+1)≤S.initialSites) (c : (initialGroup X S.copies (z*G.b)).Choice) :
    let s := z*G.b
    let wire := S.epochPower^S.priceExponent
    let q := 1/((s:ℝ)*wire)
    let ε := ((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower
    ∃A : GroupStage ((initialGroup X S.copies s).state c) G q ε
      (Fin (S.groupCount 0)) (Site X.network.copyGraph) k,
      A.StateBounds S 0 ∧ A.wire=wire ∧ A.hist=s ∧ A.cap=256 ∧ A.z=z ∧ A.degree=3 := by
  obtain ⟨A,valid,wire,history,capacity,grain,degree,_⟩ :=
    paid_group_seed_rows X G S hz field positive cut radix width budget c
  exact ⟨A,valid,wire,history,capacity,grain,degree⟩

end
end Hierarchy.DescentInitialHost

end OAI
