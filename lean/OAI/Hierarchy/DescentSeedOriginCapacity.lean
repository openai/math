import OAI.Hierarchy.DescentSeedOriginIdentity
import OAI.Hierarchy.DescentDatedStageVenue

namespace OAI
/-! # The physical venue and host capacity under original-world identification -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot
open DescentColonies DescentPacking.PackedMatch.Local.Stage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
    {k z wire s H w : ℕ}

section Venue
variable {P : Type} {u : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F u P bits}
variable (r : Reached W G q ε S k 0 z 3 wire s)
local notation "g₀" => S.groupCount 0

abbrev AtVenue (wide : Fintype.card r.V≤H) (i : Dated.Operands) (M countBits floor : ℕ)
    (rs : Fin H→Fin 3→Option (Fin H)) (m : Memory w) :=
  stageVenue r wide i M countBits floor rs m

private def across (eqn : W=W') : Reached W' G q ε S k 0 z 3 wire s :=
  Eq.ndrec (motive := fun A => Reached A G q ε S k 0 z 3 wire s) r eqn

theorem wide_across (eqn : W=W') (wide : Fintype.card r.V≤H) :
    Fintype.card (across r eqn).V≤H := by cases eqn;exact wide

theorem venue_across (eqn : W=W') (wide : Fintype.card r.V≤H) (i : Dated.Operands)
    (M b floor : ℕ) (rs : Fin H→Fin 3→Option (Fin H)) (m : Memory w)
    (old : AtVenue r wide i M b floor rs m) :
    AtVenue (across r eqn) (wide_across r eqn wide) i M b floor rs m := by
  cases eqn
  exact old
end Venue

variable {cp p : ℕ} (X : Approximation F cp p)
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) c digits)
    (wide : @Fintype.card o.raw.V o.raw.finite ≤ H)

include wide in
theorem source_hosts : @Fintype.card o.source.V o.source.finite ≤ H := by
  have counts := transport_card (W := (initialGroup X S.copies s).state c)
    (W' := initial_world X S.copies s (S.groupCount 0) k digits c)
    (G := G) (S := S) (q := q) (fee := ε) (k := k) (z := z) (wire := wire) (s := s)
    o.raw (linked_world X c digits o.seed)
  unfold Origin.source
  exact counts.le.trans wide

end
end Hierarchy.DescentDatedSeedStartup

end OAI
