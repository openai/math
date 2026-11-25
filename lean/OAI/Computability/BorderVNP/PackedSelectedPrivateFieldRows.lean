import OAI.Computability.BorderVNP.PackedOuterCompiledFieldRows
import OAI.Computability.BorderVNP.PackedHistoryNormalizedSelected

/-! # Coherent private field rows on the selected machine at every outer level

The repeated flattening of the public inner copy-and-port rectangle defines
the outer port numbering. Each active selected compilation supplies the
actual subdivision, stage and terminal sparse cable rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Adaptive Packing Inherited PublicCapacity EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- Public outer port capacity, growing by precisely the inner copy fan at each level. -/
def portCapacity (base : ℕ) : ℕ → ℕ
  | 0 => base
  | t+1 => Parallel.nestedCapacity S.fanIn (portCapacity base t) S.rounds

/-- Public outer ports obtained by flattening the genuine nested-copy names. -/
def privatePorts {P : Type} {np : ℕ} (leaf : P ↪ Fin np) :
    (t : ℕ) → Port (fan S) P t ↪ Fin (portCapacity S np t)
  | 0 => leaf
  | t+1 => Flat.portRows S.rounds (Parallel.nestedPorts S.fanIn (privatePorts leaf t) S.rounds)

variable {S} {P : Type} [Fintype P] {bits : P → ℕ} {start T : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {w np : ℕ} (C : Compiled bits deep budget cap w) (leaf : P ↪ Fin np)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)

/-- The actual site/cable/port metadata used by the complete selected machine's private tapes. -/
noncomputable def Compiled.privateSiteRows (t : ℕ) (ht : t<T) : (C.machine t ht).F.SiteRows :=
  (C.atLevel t ht).program.privateSiteRows (privatePorts S leaf t) (seeds t)

/-- No cable or port naming hypothesis is required of the selected physical machine. -/
noncomputable def Compiled.privateFieldRows (t : ℕ) (ht : t<T) :
    (C.machine t ht).FieldRows (C.privateSiteRows leaf seeds t ht) (privatePorts S leaf t) (privatePorts S leaf (t+1)) :=
  (C.atLevel t ht).fieldRows (privatePorts S leaf t) (seeds t)

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
