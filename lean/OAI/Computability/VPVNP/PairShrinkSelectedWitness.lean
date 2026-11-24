import OAI.Computability.VPVNP.PairShrinkSelectedOccurrence
import OAI.Computability.VPVNP.PairShrinkRoleScheduledSuffix

/-!
# Witnesses of the shrinking kernel at a selected physical row

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
local notation "tr" => (B.shrinkPassAt f hf j rfl Z).step.term sel
local notation "r₀" => originReader B f hf v.origin v.term
local notation "r₁" => (shrinkPassReaders B f hf j rfl Z).termParsers sel
local notation "Old" => Placed (v.pass.step.term v.term).place v.input.network.Half u
local notation "PhysicalOld" => Placed (tr).place (Z).network.Half site

set_option maxHeartbeats 1200000 in
-- Eliminate the index equality in the shrinking pass before reindexing its placed fields.
/-- Old half-wire assignments at the recovered shrinking site. -/
noncomputable def placedEquiv : Old ≃ PhysicalOld := by
  rcases v with ⟨a,g,b,n,Y,p,origin,t,tape⟩
  cases origin with
  | shrink stage lengthEq Y =>
    subst g
    with_unfolding_all exact Equiv.refl _
  | refresh => cases h

variable (z : (v.pass.step.term v.term).output.Half u)
    (a : Placed (v.pass.step.term v.term).place v.input.network.Half u)
local notation "parent" => halfEquiv v u h z
local notation "old" => placedEquiv v u h a

set_option maxHeartbeats 1500000 in
-- Both witness types are dependent products over the reindexed resident map calls.
/-- Reindex the entire local witness, including its hidden fields and map choices. -/
noncomputable def witnessEquiv :
    ((r₀).witness u a z).Choice ≃ ((r₁).witness site old parent).Choice := by
  rcases v with ⟨a,g,b,n,Y,p,origin,t,tape⟩
  cases origin with
  | shrink stage lengthEq Y =>
    subst g
    with_unfolding_all exact Equiv.refl _
  | refresh => cases h

attribute [local irreducible] nodeReader TermParsers.nodeBits shrinkPassReaders

set_option maxHeartbeats 1500000 in
-- The selected parser and its transported witness reduce at the actual pass origin.
theorem witness_fields (c : ((r₀).witness u a z).Choice) :
    let chosen := witnessEquiv v u h z a c
    (r₀).nodeBits u a z c = (r₁).nodeBits site old parent chosen ∧
      ((r₀).witness u a z).exponents c = ((r₁).witness site old parent).exponents chosen := by
  rcases v with ⟨a,g,b,n,Y,p,origin,t,tape⟩
  cases origin with
  | shrink stage lengthEq Y =>
    subst g
    dsimp only [witnessEquiv, placedEquiv, halfEquiv, occurrence, originReader,
      ShrinkOccurrence.nextState, Equiv.refl_apply]
    with_reducible exact ⟨rfl, rfl⟩
  | refresh => cases h

end PairSimulation.ShrinkRoleDirectory

end VPVNP
end Computability
end OAI
