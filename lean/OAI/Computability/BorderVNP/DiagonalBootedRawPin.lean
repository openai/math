import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.DiagonalExternalFreeCanonical

/-! # The raw substituted row at all the booted signed pin returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open RoutingISA RoutingISA.Pins RoutingISA.Evaluator VPVNP.BurstRAM CellMacro.Generator ProcessorSlots
open scoped Classical

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (ib hb sb : Fin (R+1) → ℕ)

/-- A raw row is guessed by the lead team. The others have an empty local
guess and physically write zero on their entire inactive substitution array. -/
theorem Wiring.substitution_jointGuess (raw : Fin d → Bool) (u : Fin (R+1)) (m : Memory w) :
    let L := G.pinLayout u (ib u) (hb u) (sb u)
    SubstitutionAt L (extendGuess ((G.jointGuess ib hb sb).symm raw u)) m ↔
      SubstitutionAt L (extendGuess raw) m := by
  intro L
  by_cases lead : u=0
  · subst u
    rfl
  · have inactive (i : ℕ) : ¬ L.active i := fun h => lead (Fin.ext h.1)
    simp only [SubstitutionAt,ite_eq_right (inactive _)]

variable {gen : Fragment IO} {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w}
    {args : Fin (R+1) → UnitAddresses} {col : Fin d → Bool} {ext : Exterior R r link → Bool}
    (B : ∀ u, BootedPinStart gen G pub reg args col ext u)

local notation3 (prettyPrint := false) "sub" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "live" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "ref" => fun u => (args u).starbase
local notation3 (prettyPrint := false) "layout" => fun u => G.pinLayout u ((args u).ibase) ((args u).hbase) ((args u).starbase)
local notation3 (prettyPrint := false) "digits" => (G.jointGuess sub live ref).symm

/-- The original raw row of (11.2) is physically present at the exact pin
returns in the joint exterior prefix decomposition. The calling column is
independent of these substituted row bits. -/
theorem ProcessorSlots.BootedPinStart.raw_substitution (raw : Fin d → Bool) (u : Fin (R+1))
    (apart : Separated (layout u)) :
    SubstitutionAt (layout u) (extendGuess raw) ((B u).pins (digits raw u)).val.2.2 := by
  apply (G.substitution_jointGuess sub live ref raw u _).mp
  rw [((B u).outputs (digits raw u)).2.2.2.2]
  intro i hi
  exact preparedMemory_substitute (layout u) _ _ apart le_rfl hi

/-- The immutable raw row survives the actual geometry return at every booted
team when its scratch region starts after the two pin arrays. -/
theorem ProcessorSlots.BootedPinStart.raw_geometry (raw : Fin d → Bool) (u : Fin (R+1))
    (apart : Separated (layout u)) {fresh dest clock o : ℕ} {outputs : Fin o → ℕ}
    {trace : List (TeamRAM.Event w)} {last : Bank w} {mem : Memory w} :
    let chosen := (B u).pins (digits raw u)
    PackedHistoryCircuit.GeometryReturn (pub u) (RoutingISA.CompactMachine.install gen n (B u).start.routines)
      chosen.val.2.1 chosen.val.2.2 fresh dest clock outputs trace last mem →
    (layout u).ibase+(layout u).count ≤ fresh → SubstitutionAt (layout u) (extendGuess raw) mem := by
  intro chosen returned upper
  exact Diagonal.ExternalSew.substitution_geometry (BootedPinStart.raw_substitution G B raw u apart) returned upper

end TeamContraction

end BorderVNP
end Computability
end OAI
