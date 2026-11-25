import OAI.Hierarchy.DescentPhysicalTrunkRead

namespace OAI
/-! # Carry the original actor census and three signed peer fields into the priced trunk -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentResetTrunkCompactPointer DescentDyadicSpan ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront) (floor : ℕ) (s : v.Scene) {w : ℕ} (safe : v.SceneRoom floor s w)
local notation "low₀" => v.peer.endAddress (v.peers floor)

/-- Even if the dyadic suffix of the raw prefix straddles a later table,
every live raw rank is inside the original measured range. -/
theorem trunk_census_later {N P : ℕ} (hosts : P=v.peer.hosts) (active : N≤ s.inverse.size)
    {name : Fin N→Fin P} {other : Fin N→Option (Fin N)} (initial : Memory w)
    (stored : Measured (v.trunkBanks floor s) name other (v.preScalar floor s safe initial)) :
    Measured (v.trunkBanks floor s) name other ((v.received floor s safe).image initial):=by
  have keeps:=(v.retained_cuts floor s safe initial).2.1
  have small:=safe.count.2.2
  have here:=safe.inverse.2.2
  have width:=safe.count.1
  have total : s.count.base<low₀:=(Nat.lt_add_of_pos_right width).trans_le small
  have room : v.peer.threshold (v.peers floor)+2*v.peer.hosts+span v.peer.hosts≤low₀:=le_rfl
  have rankSpace : v.peer.hosts≤low₀:=by omega
  constructor
  · exact (keeps s.count.base total).trans stored.count
  · intro i
    exact (keeps _ ((Nat.add_lt_add_left (i.isLt.trans_le active) _).trans_le here)).trans (stored.here i)
  · intro i
    have addr : (name i).val<v.peer.hosts:=(name i).isLt.trans_le hosts.le
    have early : v.peer.threshold (v.peers floor)+1*v.peer.hosts+(name i).val<low₀:=by omega
    exact (keeps _ early).trans (stored.turn i)
  · intro i
    have addr : (name i).val<v.peer.hosts:=(name i).isLt.trans_le hosts.le
    have early : s.count.base-v.peer.hosts+(name i).val<low₀:=by omega
    exact (keeps _ early).trans (stored.number i)

end
end Hierarchy.DescentDatedAddressBook.CandidateFront
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentResetTrunkCompactPointer DescentResetFieldAssembler DescentCommonHost DescentResetTrunkIssue DescentActorRaster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "radius₁" => (Z).k-(T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "pal" => DescentDenseHostOrder.roster (Z).graph radius₁ Ht
local notation "used" => Fintype.card B.next.V
local notation "grp" => S.groupCount (i+1)
local notation "half" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*input.placement.cap)
variable {H0 H bw b : ℕ} (previous : Fintype.card input.V≤H0)
local notation "oldRank" => (vertex).trans (Fin.castLEEmb previous)
local notation "real" => (Z).rawHostRank T oldRank
local notation "dense" => (Z).denseHostRank T oldRank
local notation "rawSize" => H0*(pal).card


open DescentPackedZip DescentSixParty.Chronology DescentDyadicSpan
variable {M : ℕ}
local notation "L₀" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "cap₀" => input.placement.cap
local notation "slot" => Fin L₀×Fin (2*cap₀)
local notation "Q" => DescentResetStemPackedIssue.count L₀ cap₀
local notation "ord₀" => DescentResetStemPackedIssue.ordinal L₀ cap₀

open ThreeFlat.RAM PhysicalProcedure

variable (v : DescentDatedAddressBook.CandidateFront) (floor : ℕ) (s : v.Scene)
  (safe : v.SceneRoom floor s bw)
local notation "dateBanks" => v.trunkBanks floor s
local notation "midAddr" => v.mixed floor
local notation "counted" => v.peer.endAddress (v.peers floor)
local notation "atStem" => v.stemOutput floor
local notation "deck" m => (v.received floor s safe).image m

open DescentPackedColony DescentSortedRoster
local notation "pre₀" m => v.preScalar floor s safe m
local notation "near₀" => v.peer.rawPeers (v.peers floor)
local notation "pal₀" => v.peer.threshold (v.peers floor)

/-- The scalar used by the trunk and its compact peer census, on their native memories. -/
abbrev ActorTrunkReads (initial : Memory bw) : Prop :=
    (∀r : Fin v.newHosts,v.preParent floor s safe initial (counted+r.val)=
       ((DescentResetFieldAssembler.raw v.metaBits ((originalTrunkRack B r).elim .blank (hostShape B))).val:Word bw)) ∧
      Measured dateBanks (compactActorName B previous) (compactTrunkPeer B previous) (deck initial)

/-- This is the scalar word subsequently read by the real dated trunk
operand. Its arrays are the three actual measured peers and original palette. -/
theorem trunk_prepared (initial : Memory bw) {p : ℕ} (record : B.Recorded p)
    (hosts : v.peer.hosts=rawSize) (active : used≤ s.inverse.size) (denseFit : used≤v.newHosts)
    (installed : s.rawHeader=rawTrunkExpr v.metaBits v.peer.hosts near₀ pal₀)
    (ns : Fin rawSize→Fin 3→Option (Fin rawSize))
    (positioned : ∀u,present (DescentResetPeerUnionRAM.selfPeers ns) (real u)=
      (insert u ((Z).emittedNear T u)).map real)
    (loops : ∀u,(∀j,ns (real u) j≠some (real u)) ↔ u∉(Z).emittedNear T u)
    (rows : ∀(r : Fin rawSize) (j : Fin 3),(pre₀ initial) (near₀+j.val*rawSize+r.val)=(target (ns r j):Word bw))
    (palette : ∀(j : Fin 3) (r : Fin rawSize),(pre₀ initial) (pal₀+j.val*rawSize+r.val)=
      (DescentResetTrunkPalette.value (Z).graph radius₁ Ht j r:Word bw))
    (census : Measured dateBanks (compactActorName B previous) (compactTrunkPeer B previous) (pre₀ initial))
    (field : 5≤2^v.metaBits) (word : 5≤2^bw) :
    (∀r : Fin v.newHosts,v.preParent floor s safe initial (counted+r.val)=
       ((DescentResetFieldAssembler.raw v.metaBits ((originalTrunkRack B r).elim .blank (hostShape B))).val:Word bw)) ∧
      Measured dateBanks (compactActorName B previous) (compactTrunkPeer B previous) (deck initial):=by
  have read (u : B.next.V): (pre₀ initial) (s.inverse.base+(B.next.vertex u).val)=((real u).val:Word bw):=by
    have now:=census.here ((compactActorOrder B previous) u)
    change (pre₀ initial) (s.inverse.base+(dense u).val)=_ at now
    rw [dense_physical B previous u] at now
    simpa only [compactActorName,Equiv.symm_apply_apply] using now
  have space : pal₀+2*rawSize+span rawSize≤ counted:=by rw [←hosts];exact le_rfl
  have runway : rawSize<2^bw:=by have:=safe.peers.total;omega
  have ends:=v.peer.ordered (v.peers floor)
  have low : near₀≤pal₀:=(Nat.le_add_right ..).trans
    ((show near₀+3*v.peer.hosts≤v.peer.three (v.peers floor) from le_rfl).trans (ends.2.1.trans ends.2.2.1))
  have before : near₀+2*rawSize+span rawSize≤ counted:=
    (Nat.add_le_add_right (Nat.add_le_add_right low _) _).trans space
  have yes:=original_trunk_headers B previous record ns (pre₀ initial) s.count s.inverse near₀ pal₀ counted
    positioned loops rows palette census.count read active denseFit safe.count safe.inverse
    (scalar_bank_room before safe.peers.total) (scalar_bank_room space safe.peers.total)
    field word runway safe.parent
  have emitted:=yes.2.1
  constructor
  · intro r
    change (DescentResetTrunkCompactScalar.phase bw v.newHosts counted s.count s.inverse s.rawHeader).image (pre₀ initial) _=_
    rw [installed,hosts]
    exact emitted r
  · exact v.trunk_census_later floor s safe hosts.symm active initial census

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
