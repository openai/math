import OAI.Hierarchy.DescentPhysicalResetSceneInputs
import OAI.Hierarchy.DescentPhysicalTrunkCensus

namespace OAI
/-! # The dated trunk census reads the attained actor directory and published palette -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentResetTrunkCompactPointer DescentDatedAddressBook ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "radius" => (Z).k-(T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "used" => Fintype.card B.next.V
variable {H w : ℕ} (previous : Fintype.card input.V≤H)
local notation "oldRank" => (vertex).trans (Fin.castLEEmb previous)
local notation "rawId" => (Z).rawHostRank T oldRank
local notation "denseId" => (Z).denseHostRank T oldRank
local notation "rawHosts" => H*(DescentDenseHostOrder.roster (Z).graph radius Ht).card
variable (v : ResetOutput) (base : ℕ) (old : v.OriginalOperands base)
local notation "A" => v.front
local notation "p₀" => (A).peer
local notation "floor₀" => v.actorEnd base
local notation "L" => v.actor.directory (v.middle.stop base)
local notation "scene" => v.issuedScene base old
local notation "literalSize" => (p₀).oldHosts*(DescentDenseHostOrder.roster old.evidence.board old.evidence.rootBits old.evidence.depth).card
variable (safe : v.front.SceneRoom (v.actorEnd base) (v.issuedScene base old) w)
local notation "arr" m => (A).preScalar floor₀ scene safe m
local notation "palAt" => (p₀).threshold ((A).peers floor₀)

/-- The only equalities between catalogues concern public literal values.
The three input reads are the actual output of `paid_actor_directory`. -/
theorem issued_trunk_census (m : Memory w) (sites : (L).sites=(p₀).hosts)
    (names : (p₀).hosts=rawHosts) (active : used≤(L).inverse.size)
    (sameSize : rawHosts=literalSize)
    (palette : ∀(j : Fin 3) (r : Fin rawHosts),DescentResetTrunkPalette.value
      old.evidence.board old.evidence.rootBits old.evidence.depth j (r.cast sameSize)=
        DescentResetTrunkPalette.value (Z).graph radius Ht j r)
    (count : m (L).count.base=(used:Word w))
    (inverse : ∀u:B.next.V,m ((L).inverse.base+(denseId u).val)=((rawId u).val:Word w))
    (rank : ∀u:B.next.V,m ((L).ranks.base+(rawId u).val)=((denseId u).val:Word w)) :
    Measured ((A).trunkBanks floor₀ scene) (compactActorName B previous) (compactTrunkPeer B previous) (arr m) ∧
      ∀(j : Fin 3) (r : Fin rawHosts),(arr m) (palAt+j.val*rawHosts+r.val)=
        (DescentResetTrunkPalette.value (Z).graph radius Ht j r:Word w) := by
  have table (j : Fin 3) (r : Fin rawHosts) :
      (arr m) (palAt+j.val*rawHosts+r.val)=(DescentResetTrunkPalette.value (Z).graph radius Ht j r:Word w):=by
    have read:=(A).preScalar_palette floor₀ scene safe m j (r.cast sameSize)
    change (arr m) (palAt+j.val*(p₀).hosts+r.val)=
      (DescentResetTrunkPalette.value old.evidence.board old.evidence.rootBits old.evidence.depth j
        (r.cast sameSize):Word w) at read
    rw [names,palette j r] at read
    exact read
  refine ⟨measured_trunk_actors B previous _ _ ?_ ?_ ?_ ?_,table⟩
  · obtain ⟨_,_,_,rankEnd,mid,vals,_,last⟩:=(L).ordered
    have low : (L).count.base<floor₀:=by
      change (L).ranks.base+(L).sites<(L).endAddress
      omega
    exact ((A).preScalar_lower floor₀ scene safe m _ low).trans count
  · intro u
    have small : (denseId u).val<(L).inverse.size:=(denseId u).isLt.trans_le active
    have low : (L).inverse.base+(denseId u).val<floor₀:=
      (Nat.add_lt_add_left small _).trans_le (L).ordered.2.2.2.2.2.2.2
    exact ((A).preScalar_lower floor₀ scene safe m _ low).trans (inverse u)
  · intro u
    rw [v.issued_trunk_prefix base old sites]
    have small : (rawId u).val<(L).sites:=(rawId u).isLt.trans_le (sites.trans names).ge
    obtain ⟨_,_,_,rankEnd,mid,vals,_,last⟩:=(L).ordered
    have low : (L).ranks.base+(rawId u).val<floor₀:=by change _<(L).endAddress;omega
    exact ((A).preScalar_lower floor₀ scene safe m _ low).trans (rank u)
  · intro r
    change (arr m) (palAt+1*(p₀).hosts+r.val)=_
    rw [names]
    simpa [DescentResetTrunkPalette.value] using table 1 r

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
