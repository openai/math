import OAI.Hierarchy.DescentDatedSeedRoster
import OAI.Hierarchy.DescentSeedInitialHeldImage
import OAI.Hierarchy.DescentSeedVenueTokenPhase
import OAI.Hierarchy.DescentSeedCompleteHostNumber

namespace OAI
/-! # The count and ordered venue of the actual initial loader image -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentSeedInitialTable DescentColonies DescentSIMDLookup DescentPackedColony DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM Catalyst ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
  {k cp p H : ℕ} (X : Approximation F cp p)
  (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload

variable {q ε : ℝ} {wire s z₀ w : ℕ} {c : (initialGroup X S.copies s).Choice}
  (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z₀) (wire:=wire) c digits)
  (wide : Fintype.card o.raw.V ≤ H)
local notation "final" => completeImage G op X digits publicWide l header payload Z


include wide in
/-- The original loader keeps the archive host count and populates every ranked venue row. -/
theorem execute_initial_held (m : Memory w) (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w)
    (fields : l.operandBits*l.operandLanes ≤ w) (early : header < l.base)
    (sourceSpace : publicWords X+span jobs ≤ finish) (live : 0 < lanes)
    (machine : payload ≤ w) (space : limit < 2^w) :
    (completeAfter G op X digits publicWide l header payload Z w).Exec m ((final) m)
        (completeTicks (S:=S) (k:=k) G op X publicWide l payload Z w) ∧
      (Chronology.DatePorts.initial G op X S.copies l k H g₀ payload Z).held o.source limit ((final) m) := by
  obtain ⟨run,_,venue,_⟩:=complete_after_count G op X digits publicWide l header payload Z o wide m
    signed fields early sourceSpace live machine space
  refine ⟨run,(Chronology.DatePorts.initial_held_iff G op X H l payload Z o.source limit ((final) m)).2 ?_⟩
  refine ⟨source_hosts X o wide,?_,?_⟩
  · rw [source_roster X o wide publicWide]
    exact venue
  · rw [source_host_size X o]
    have natural:=complete_host_number G op X digits publicWide l header payload Z m early sourceSpace live machine space
    exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun n : ℕ=>(n:Word w)) natural)

include wide in
theorem initial_held (m : Memory w) (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w)
    (fields : l.operandBits*l.operandLanes ≤ w) (early : header < l.base)
    (sourceSpace : publicWords X+span jobs ≤ finish) (live : 0 < lanes)
    (machine : payload ≤ w) (space : limit < 2^w) :
    (Chronology.DatePorts.initial G op X S.copies l k H g₀ payload Z).held o.source limit ((final) m) :=
  (execute_initial_held G op X digits publicWide l header payload Z o wide m signed fields early
    sourceSpace live machine space).2

/-- The public graph width supplies the capacity of the originating branch. -/
theorem initial_held_of_public (m : Memory w) (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w)
    (fields : l.operandBits*l.operandLanes ≤ w) (early : header < l.base)
    (sourceSpace : publicWords X+span jobs ≤ finish) (live : 0 < lanes)
    (machine : payload ≤ w) (space : limit < 2^w) :
    (Chronology.DatePorts.initial G op X S.copies l k H g₀ payload Z).held o.source limit ((final) m) :=
  initial_held G op X digits publicWide l header payload Z o (o.seed.hostSize.le.trans publicWide) m
    signed fields early sourceSpace live machine space

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
