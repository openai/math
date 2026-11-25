import OAI.Hierarchy.DescentSeedPaidCableStage
import OAI.Hierarchy.DescentSeedLinkFields

namespace OAI
/-! # Reached initial world and physical links for each chosen original ballot -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentInitialHost DescentCompiler DescentHostDegree Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp pins : ℕ}

theorem initial_link (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
    {z f k : ℕ} (hz : 0<z) (field : 0<k) (positive : 0<S.height)
    (cut : packExponent 20 3≤f) (radix : S.radix=2^k)
    (width : k=groupBits S.rounds S.height S.hostGain S.capGain f)
    (budget : 10*(X.size+1)≤S.initialSites) (c : (initialGroup X S.copies (z*G.b)).Choice) :
    let s:=z*G.b
    let wire:=S.epochPower^S.priceExponent
    let q:=1/((s:ℝ)*wire)
    let fee:=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower
    ∃r : Reached ((initialGroup X S.copies s).state c) G q fee S k 0 z 3 wire s,
      SeedLink X c r (S.initialDigits radix) := by
  obtain ⟨A,valid,words,atoms,capacity,grain,degree,sites,blocks,records,counts,hubs,hostHubs,nearby,signed,cables⟩ :=
    paid_group_seed_cables X G S hz field positive cut radix width budget c
  refine ⟨⟨_,A,valid,grain,words,atoms,degree,DescentSeedRoot.oldOrder X c,
    (Fintype.equivFin _).toEmbedding,by omega,by omega⟩,rfl,HEq.rfl,heq_of_eq sites,blocks,records,counts,hubs,rfl,(fun v=>⟨v,rfl,congrFun hostHubs v⟩),capacity,?_,?_,?_,?_,?_,signed,cables⟩
  · intro pin
    change ((A.pos _).1,A.block _)=_
    rw [sites,blocks]
    rfl
  · intro pin pin' same
    change (A.pos _).2=(A.pos _).2
    rw [sites]
    exact congrArg Sum.inr same
  · intro pin
    change (Fintype.equivFin _ (A.pos _).2).val=_
    rw [sites]
    rfl
  · intro u
    change (A.pos u).1=_ ∧ (Fintype.equivFin _ (A.pos u).2).val=_
    rw [sites];exact ⟨rfl,rfl⟩
  · intro v u
    change u∈A.near v ↔ _
    rw [nearby]
    simp [DescentPackedSeed.Signed.Plane.initialTicket]

end
end Hierarchy.DescentSixParty.Chronology

end OAI
