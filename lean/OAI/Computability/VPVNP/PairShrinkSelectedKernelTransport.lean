import OAI.Computability.VPVNP.PairShrinkSelectedWitness

/-!
# Reindexing the shrinking kernel at a selected physical row

Recovering the scheduled index and state from an origin preserves the
placed arguments and every witness of the local product. In particular,
the transported visit uses the same bits, exponent vector and ordered
child packets, even when several residents emit the same label.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRoleDirectory

open BurstRAM Compression CompressorRecords LocalHistory NodeArguments NetworkKernel
open TreeDecode TraversalRows TraversalRoles
set_option quotPrecheck false

variable {k K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k} {B : S.Templates}
    {f : B.Entry → K} {hf : B.IsSolution f} (v : SelectedLevel B f hf)
    (u : (v.pass.step.term v.term).output.Site) (h : tagLevel B f hf v = .shrink)

local notation "x" => occurrence v u h
local notation "Z" => (x).state
local notation "j" => (x).i
local notation "sel" => (x).selection
local notation "site" => (x).site
local notation "r₀" => originReader B f hf v.origin v.term
local notation "r₁" => (shrinkPassReaders B f hf j rfl Z).termParsers sel

variable (z : (v.pass.step.term v.term).output.Half u)
    (a : Placed (v.pass.step.term v.term).place v.input.network.Half u)
local notation "parent" => halfEquiv v u h z
local notation "old" => placedEquiv v u h a

attribute [local irreducible] nodeReader shrinkPassReaders

set_option maxHeartbeats 1500000 in
-- Normalize the occurrence and its transported half without unfolding the node parser.
/-- Reindexing the parent preserves the unread suffix on every bit stream. -/
theorem node_suffix (bs : List Bool) :
    ((nodeReader r₀ u z).read bs).map Prod.snd =
      ((nodeReader r₁ site parent).read bs).map Prod.snd := by
  rcases v with ⟨a,g,b,n,Y,p,origin,t,tape⟩
  cases origin with
  | shrink stage lengthEq Y =>
    subst g
    dsimp only [halfEquiv, occurrence, originReader, ShrinkOccurrence.nextState]
    exact congrArg (fun zz => ((nodeReader ((shrinkPassReaders B f hf stage rfl Y).termParsers t)
      u zz).read bs).map Prod.snd) (Equiv.refl_apply z).symm
  | refresh => cases h

set_option maxHeartbeats 1500000 in
-- Compute the ordered finite placement fiber before comparing the child lists.
theorem children_packets (base : ℕ) :
    TreeDecode.children r₀
      (fun t y => ⟨(sitePointers B.recordLimit base (siteOrder v.input) t).1, packed v.input t y⟩)
      u a =
      TreeDecode.children r₁
        (fun t y => ⟨NodeArguments.ChildScan.childNode Z base B.recordLimit t, packed Z t y⟩)
        site old := by
  rcases v with ⟨a,g,b,n,Y,p,origin,t,tape⟩
  cases origin with
  | shrink stage lengthEq Y =>
    subst g
    rfl
  | refresh => cases h

end PairSimulation.ShrinkRoleDirectory

end VPVNP
end Computability
end OAI
