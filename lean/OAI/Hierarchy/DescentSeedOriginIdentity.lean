import OAI.Hierarchy.DescentSeedOriginalWorld

namespace OAI
/-! # Physically named date-zero source -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentCompiler DescentColonies Catalyst
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

variable {cp pins : ℕ} (X : Approximation F cp pins) {G : PoweredGadget F} {S : AtomSchedule}
    {q fee : ℝ} {k z wire s : ℕ}

section Transport
variable {P : Type} {u : ℕ} {bits : P → ℕ} {W W' : MarkedWorld F u P bits}

def transport (r : Reached W G q fee S k 0 z 3 wire s) (eqn : world r = W') :
    Reached W' G q fee S k 0 z 3 wire s :=
  Eq.ndrec (motive := fun A => Reached A G q fee S k 0 z 3 wire s) (reached r) eqn

theorem transport_card (r : Reached W G q fee S k 0 z 3 wire s) (eqn : world r = W') :
    @Fintype.card (transport r eqn).V (transport r eqn).finite = @Fintype.card r.V r.finite := by
  cases eqn
  rfl

end Transport

/-- The concrete original seed reader supplies every datum for this start.
The same original selector choice determines the named initial history. -/
structure Origin (c : (initialGroup X S.copies s).Choice)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k) where
  raw : Reached ((initialGroup X S.copies s).state c) G q fee S k 0 z 3 wire s
  seed : Chronology.SeedLink X c raw digits

namespace Origin
variable {X} {c : (initialGroup X S.copies s).Choice}
    {digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k}
    (o : Origin (S:=S) (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)

def source : Reached ((initial X S.copies s (S.groupCount 0) k digits).state c)
    G q fee S k 0 z 3 wire s :=
  transport (W' := initial_world X S.copies s (S.groupCount 0) k digits c)
    o.raw (linked_world X c digits o.seed)

end Origin
end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSeedInitialTable
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot
open Catalyst DescentColonies
noncomputable section
variable {F : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
  {k cp pins wire s z H : ℕ} (X : Approximation F cp pins)
  {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
  (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) (s:=s) c digits)
  (wide : Fintype.card o.raw.V ≤ H)

/-- Original graph names are the same genuine finite ordinals used by the
startup table, padded to the common date's host capacity. -/
def originalHosts : Vertex X↪Fin H :=
  (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb (o.seed.hostSize ▸ wide))
end
end Hierarchy.DescentSeedInitialTable

end OAI
