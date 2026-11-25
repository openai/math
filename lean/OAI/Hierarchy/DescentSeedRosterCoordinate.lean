import OAI.Hierarchy.DescentSeedNativeDirectory
import OAI.Hierarchy.DescentVenueRosterDefinition

namespace OAI
/-! # The original graph's ranked neighbors in the reached, padded seed roster -/
namespace Hierarchy.DescentDatedSeedStartup.OriginalRoster
open DescentSixParty DescentCompiler DescentInitialHost DescentSeedRoot DescentSeedInitialTable
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage Catalyst
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist H cp p : ℕ}
    (X : Approximation F cp p) (R : Reached W G q ε S k i z 3 wire hist)
    (size : Fintype.card R.V=Fintype.card (Vertex X))
local notation "V₀" => Vertex X

def ticket : R.V ≃ V₀ :=
  ((Equiv.ofBijective R.vertex ((Fintype.bijective_iff_injective_and_card _).2
    ⟨R.vertex.injective,by simp⟩)).trans (finCongr size)).trans (Fintype.equivFin V₀).symm

private theorem ticket_rank (v : R.V) : index (ticket X R size v)=(R.vertex v).val :=
  congrArg Fin.val ((Fintype.equivFin V₀).apply_symm_apply (Fin.cast size (R.vertex v)))

variable (nearby : ∀v u,u∈R.placement.near v ↔ ticket X R size u∈near X.network.copyGraph (ticket X R size v))

include nearby in
private theorem ticket_slot (v : R.V) (u : ↥(R.placement.near v)) :
    (((near X.network.copyGraph (ticket X R size v)).filter (fun t=>index t< index (ticket X R size u.val))).card)=
      (hostSlot R.placement (R.vertex.trans Fin.valEmbedding) v u).val := by
  rw [hostSlot_val]
  symm
  apply Finset.card_bij (fun t _=>ticket X R size t)
  · intro t ht
    obtain ⟨mem,early⟩:=Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨(nearby v t).mp mem,by
      simpa only [ticket_rank,Function.Embedding.trans_apply,Fin.valEmbedding_apply] using early⟩
  · exact fun _ _ _ _ eqn=>(ticket X R size).injective eqn
  · intro t ht
    obtain ⟨x,rfl⟩:=(ticket X R size).surjective t
    obtain ⟨mem,early⟩:=Finset.mem_filter.mp ht
    exact ⟨x,Finset.mem_filter.mpr ⟨(nearby v x).mpr mem,by
      simpa only [ticket_rank,Function.Embedding.trans_apply,Fin.valEmbedding_apply] using early⟩,rfl⟩

include nearby in
private theorem ticket_neighbors (v : R.V) (j : Fin 3) :
    neighbors X (ticket X R size v) j=(hostRoster R.placement (R.vertex.trans Fin.valEmbedding) v (Fin.cast R.branch.symm j)).map (ticket X R size) := by
  let legal (u : V₀) := u∈near X.network.copyGraph (ticket X R size v) ∧
    ((near X.network.copyGraph (ticket X R size v)).filter (fun t=>index t< index u)).card=j.val
  have translate (u : V₀) (yes : legal u) : ∃x : ↥(R.placement.near v),
      ticket X R size x.val=u ∧ hostSlot R.placement (R.vertex.trans Fin.valEmbedding) v x=Fin.cast R.branch.symm j := by
    obtain ⟨t,rfl⟩:=(ticket X R size).surjective u
    let x : ↥(R.placement.near v):=⟨t,(nearby v t).mpr yes.1⟩
    exact ⟨x,rfl,Fin.ext ((ticket_slot X R size nearby v x).symm.trans yes.2)⟩
  unfold neighbors
  split
  · rename_i live
    obtain ⟨x,hx,hj⟩:=translate live.choose live.choose_spec
    rw [←hj,at_host]
    exact congrArg some hx.symm
  · rename_i empty
    unfold hostRoster
    split
    · rename_i active
      let x:=active.choose
      exact (empty ⟨ticket X R size x.val,(nearby v x.val).mp x.property,
        (ticket_slot X R size nearby v x).trans (congrArg Fin.val active.choose_spec)⟩).elim
    · rfl

include nearby in
theorem raw_roster (wide : Fintype.card R.V≤H) (room : Fintype.card V₀≤H) :
    R.venueRoster wide=roster X ((Fintype.equivFin V₀).toEmbedding.trans (Fin.castLEEmb room)) := by
  let orig:=(Fintype.equivFin V₀).toEmbedding.trans (Fin.castLEEmb room)
  let host:=R.vertex.trans (Fin.castLEEmb wide)
  have same (v : R.V) : orig (ticket X R size v)=host v:=Fin.ext (ticket_rank X R size v)
  funext h j
  by_cases occupied : ∃v,host v=h
  · obtain ⟨v,rfl⟩:=occupied
    have present : ∃u,host u=host v:=⟨v,rfl⟩
    change hostRotor host _ (host v) _=roster X orig (host v) j
    rw [hostRotor,dite_eq_left present,host.injective present.choose_spec,roster,←same v,rack_real]
    simp only [Option.bind_some,ticket_neighbors X R size nearby]
    cases hostRoster R.placement (R.vertex.trans Fin.valEmbedding) v (Fin.cast R.branch.symm j) with
    | none => rfl
    | some u => exact congrArg some (same u).symm
  · have vacant : ¬∃u,orig u=h:=by
      rintro ⟨u,hit⟩
      obtain ⟨v,rfl⟩:=(ticket X R size).surjective u
      exact occupied ⟨v,(same v).symm.trans hit⟩
    change hostRotor host _ h _=roster X orig h j
    simp [hostRotor,roster,rack,occupied,vacant]

end
end Hierarchy.DescentDatedSeedStartup.OriginalRoster

end OAI
