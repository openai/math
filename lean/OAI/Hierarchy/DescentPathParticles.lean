import OAI.Hierarchy.DescentParticleRead
import OAI.Hierarchy.DescentRecordedResetTokens

namespace OAI
/-! # The paid records and immutable exterior equalities count the actual archive nodes on every path -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentKernelHistory DescentCompiler DescentInitialHost Catalyst
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε u : ℝ} {S : AtomSchedule} {k : ℕ}
variable {W₀ W₁ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ w hist : ℕ}
    {first : Reached W₀ G q ε S k i₀ z₀ D₀ w hist} {last : Reached W₁ G q ε S k i₁ z₁ D₁ w hist}

def Archive.Particles (a : Archive W₀) (r : Reached W₀ G q ε S k i₀ z₀ D₀ w hist) : Prop :=
  LocalParticles a.bit (fun v=>(r.placement.records v).length) (fun v=>r.placement.hub (r.placement.pos v).2)

theorem OrdinaryLink.advance_particles {W : MarkedWorld F d P bits} {i z D z' D' : ℕ}
    {source : Reached W G q ε S k i z D w hist} {he : 0≤ε}
    {T : StageInput W G u ε} {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
    {target : Reached n.result G q ε S k (i+1) z' D' w hist}
    (ticket : OrdinaryLink source he T p n target) (a : Archive W) (prev : a.Particles source) :
    (ticket.advance a).Particles target := by
  have pre : LocalParticles a.bit (fun v=>(T.records v).length) T.hub := by
    rw [show (fun v=>(T.records v).length)=(fun v=>(source.placement.records v).length) from funext ticket.sourceCounts,
      ticket.sourceFlags]
    exact prev
  exact ticket.particles.read he T p a.bit pre

theorem Path.particles (p : ℕ) (hp : 0<p) (a : Archive W₀) (path : Path first last)
    (r : path.recorded p) (prev : a.Particles first) :
    (path.archive p hp a (path.recorded_whole p r)).Particles last := by
  induction path with
  | here=>exact prev
  | ordinary prevPath ticket ih=>exact ticket.advance_particles _ (ih r)
  | reset prevPath b ih=>
    have pre:=ih r.1
    have post:=resetArchive_exterior b r.2 pre.balance pre.attached
    exact ⟨resetArchive_tokenized b r.2 _ pre.nodes,post.1,post.2⟩

variable {cp pins s z : ℕ} (X : Approximation F cp pins)
variable (c : (initialGroup X S.copies s).Choice)
variable (r : Reached ((initialGroup X S.copies s).state c) G q ε S k 0 z 3 w s)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×DescentColonies.Block k)

theorem seed_particles (ids : SeedLink X c r digits) : (seedArchive X S.copies s c).Particles r := by
  unfold Archive.Particles
  rw [show (fun v=>(r.placement.records v).length)=(fun v=>(seedRecords X c v).length) from funext ids.counts,ids.hubs]
  exact ⟨BitDescription.tokenized_seed X c,seed_hub_balance X c,seed_exterior_owners X c⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
