import OAI.Hierarchy.DescentReachedCalendarPeers
import OAI.Hierarchy.DescentPhysicalCalendarStem
import OAI.Hierarchy.DescentPhysicalTrunkRead
import OAI.Hierarchy.DescentPhysicalTrunkCensus

namespace OAI
/-! # Reading the trunk operand from a reached reset date -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentSIMDLookup
open DescentSharedCableNames DescentResetTrunkCompactPointer DescentGroupPeerOrder DescentPackedZip DescentResetLocalRoster ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false

private theorem palette_congr {n n' degree radius radius' H : ℕ}
    (left : NonlinearExpanders.Graph n degree) (right : NonlinearExpanders.Graph n' degree)
    (dimension : n=n') (same : HEq left right) (roots : radius=radius') (height : ℕ)
    (sizes : H*(DescentDenseHostOrder.roster right radius' height).card=H*(DescentDenseHostOrder.roster left radius height).card)
    (j : Fin 3) (u : Fin (H*(DescentDenseHostOrder.roster right radius' height).card)) :
    DescentResetTrunkPalette.value left radius height j (u.cast sizes) =
      DescentResetTrunkPalette.value right radius' height j u := by
  subst n'; subst radius'
  cases eq_of_heq same
  rfl

variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (oldM nextM field metaBits : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR calendar
local notation "H" => S.hostSize i
local notation "height" => GroupStage.depthBound D n f g
local notation "cap₀" => (calendar.take i).prod*256
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "radius" => (Z).k-(T).commonDepth
local notation "rawSize" => H*(DescentDenseHostOrder.roster (Z).graph radius height).card
local notation "used" => Fintype.card B.next.V
local notation "named" => (Z).rawHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb input.valid.host))
local notation "ranked" => (Z).denseHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb input.valid.host))
local notation "sg" => S.groupCount (i+1)
local notation "lows" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "parts" => Fin lows × Fin (2*input.placement.cap)
local notation "ordinal" => DescentResetStemPackedIssue.ordinal lows input.placement.cap
variable (paid : input.placement.cap=cap₀) (floor : ℕ)
    (old : EarlierBanks D k cap₀ n) (flags countBank inverse : Bank) {w : ℕ}
local notation "early" => calendarOriginals S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR calendar floor old
local notation "scene" => (A).fromOriginals floor early flags countBank inverse
variable (safe : (A).SceneRoom floor scene w) (initial : Memory w)
local notation "banks" => (A).trunkBanks floor scene
local notation "pre" => (A).preScalar floor scene safe initial
local notation "deck" => ((A).received floor scene safe).image initial
local notation "paletteAt" => (A).peer.threshold ((A).peers floor)
local notation "nearAt" => (A).peer.rawPeers ((A).peers floor)

include paid

/-- The primitive actor words here are the three components of the counted actor
directory on entry. The observed rows and signed words use the identical native prefix. -/
theorem reached_trunk_with_registers {p : ℕ} (record : B.Recorded p)
    (active : used ≤ inverse.size) (countBefore : countBank.base < floor)
    (invBefore : inverse.base+inverse.size ≤ floor) (rankBefore : (banks).number.base+rawSize ≤ floor)
    (countRead : initial countBank.base = (used:Word w))
    (invRead : ∀v:B.next.V,initial (inverse.base+(ranked v).val) = ((named v).val:Word w))
    (rankRead : ∀v:B.next.V,initial ((banks).number.base+(named v).val) = ((ranked v).val:Word w))
    (neighbors : ∃ns : Fin rawSize → Fin 3 → Option (Fin rawSize),
      (∀v j,pre (nearAt+j.val*rawSize+v.val) = (target (ns v j):Word w)) ∧
      (∀v:B.next.V,DescentSortedRoster.present (selfPeers ns) (named v)=(insert v ((Z).emittedNear T v)).map named) ∧
      ∀v:B.next.V,(∀j,ns (named v) j≠some (named v)) ↔ v∉(Z).emittedNear T v)
    (issued : ∀(x : Fin (2^k)) (side : Bool) (slot : parts) (p : Row ((A).newHosts) sg nextM),
      deck ((A).stemOutput floor+(finProdFinEquiv (x,ordinal (side,slot))).val*((A).newHosts*chunks sg nextM)+
        (row _ _ _ p).val) =
        ((data (fun r g₀=>(originalTrunkRack B r).elim 0 (fun v=>DescentResetFieldAssembler.raw metaBits («meta» B ((g₀,v),x)
          (localOrigin B ((g₀,v),x) (stemIndex B side slot))))) p).val:Word w))
    (degree : B.next.placement.degree+1 < 2^metaBits) (cap : B.next.placement.cap < 2^metaBits)
    (alphabet : 5 ≤ 2^metaBits) (machine : 5 ≤ 2^w) (packed : 7*metaBits*nextM ≤ w)
    (limit : (A).trunkEnd floor < 2^w) :
    (((A).trunkScene floor scene safe).Runs initial ∧
      ∀x : Fin (2^k),((A).trunkOperand floor x.val).Fits w ((A).trunkEnd floor) ∧
        Source ((A).trunkOperand floor x.val)
          (fun (r : Fin ((A).newHosts)) g₀=>DescentResetFieldAssembler.raw metaBits (actualMeta B (originalTrunkRack B) x (trunkCandidate B) r g₀))
          nextM (((A).trunkScene floor scene safe).image initial)) ∧ ActorTrunkReads B input.valid.host A floor scene safe initial := by
  obtain ⟨ns,reads,position,loops⟩ := neighbors
  have names := canonical_raw_hosts B oldM nextM field metaBits calendar
  have radiusEq : k=radius := by rw [B.keyWidth,B.commonDepth]; omega
  have sizes : rawSize=H*(DescentDenseHostOrder.roster ctl.board k height).card := congrArg (H*·) (calendar_palette B).symm
  have palette (j : Fin 3) (r : Fin rawSize) :
      pre (paletteAt+j.val*rawSize+r.val)=(DescentResetTrunkPalette.value (Z).graph radius height j r:Word w) := by
    have read := (A).preScalar_palette floor scene safe initial j (r.cast sizes)
    change pre (paletteAt+j.val*(A).peer.hosts+r.val)=
      (DescentResetTrunkPalette.value ctl.board k height j (r.cast sizes):Word w) at read
    rw [names,palette_congr ctl.board (Z).graph B.dimension.symm B.graph.symm radiusEq height sizes j r] at read
    exact read
  have census := measured_trunk_actors B input.valid.host banks pre
    (((A).preScalar_lower floor scene safe initial _ countBefore).trans countRead)
    (fun v=>((A).preScalar_lower floor scene safe initial _
      ((Nat.add_lt_add_left ((ranked v).isLt.trans_le active) _).trans_le invBefore)).trans (invRead v))
    (fun v=>((A).preScalar_lower floor scene safe initial _
      ((Nat.add_lt_add_left (named v).isLt _).trans_le rankBefore)).trans (rankRead v))
    (by intro r; change pre (paletteAt+1*(A).peer.hosts+r.val)=_; rw [names]
        simpa [DescentResetTrunkPalette.value] using palette 1 r)
  have countCap : used ≤ (A).newHosts := B.next.valid.host
  obtain ⟨value,installed⟩ := trunk_prepared B input.valid.host A floor scene safe initial record names active
    countCap rfl ns position loops reads palette census alphabet machine
  have shape : (A).signedQueries = DescentResetStemPackedIssue.count lows input.placement.cap :=
    congrArg₂ DescentResetStemPackedIssue.count (calendar_low_count B) paid.symm
  refine ⟨?_,value,installed⟩
  exact trunk_operand B input.valid.host A floor scene safe initial names rfl rfl shape countCap active
    limit degree cap (by change metaBits * 7 * nextM ≤ w; rw [Nat.mul_comm metaBits 7]; exact packed) installed value
    (fun x p r=>issued x true p r)

theorem reached_trunk_operand {p : ℕ} (record : B.Recorded p)
    (active : used ≤ inverse.size) (countBefore : countBank.base < floor)
    (invBefore : inverse.base+inverse.size ≤ floor) (rankBefore : (banks).number.base+rawSize ≤ floor)
    (countRead : initial countBank.base = (used:Word w))
    (invRead : ∀v:B.next.V,initial (inverse.base+(ranked v).val) = ((named v).val:Word w))
    (rankRead : ∀v:B.next.V,initial ((banks).number.base+(named v).val) = ((ranked v).val:Word w))
    (neighbors : ∃ns : Fin rawSize → Fin 3 → Option (Fin rawSize),
      (∀v j,pre (nearAt+j.val*rawSize+v.val) = (target (ns v j):Word w)) ∧
      (∀v:B.next.V,DescentSortedRoster.present (selfPeers ns) (named v)=(insert v ((Z).emittedNear T v)).map named) ∧
      ∀v:B.next.V,(∀j,ns (named v) j≠some (named v)) ↔ v∉(Z).emittedNear T v)
    (issued : ∀(x : Fin (2^k)) (side : Bool) (slot : parts) (p : Row ((A).newHosts) sg nextM),
      deck ((A).stemOutput floor+(finProdFinEquiv (x,ordinal (side,slot))).val*((A).newHosts*chunks sg nextM)+
        (row _ _ _ p).val) =
        ((data (fun r g₀=>(originalTrunkRack B r).elim 0 (fun v=>DescentResetFieldAssembler.raw metaBits («meta» B ((g₀,v),x)
          (localOrigin B ((g₀,v),x) (stemIndex B side slot))))) p).val:Word w))
    (degree : B.next.placement.degree+1 < 2^metaBits) (cap : B.next.placement.cap < 2^metaBits)
    (alphabet : 5 ≤ 2^metaBits) (machine : 5 ≤ 2^w) (packed : 7*metaBits*nextM ≤ w)
    (limit : (A).trunkEnd floor < 2^w) :
    ((A).trunkScene floor scene safe).Runs initial ∧
      ∀x : Fin (2^k),((A).trunkOperand floor x.val).Fits w ((A).trunkEnd floor) ∧
        Source ((A).trunkOperand floor x.val)
          (fun (r : Fin ((A).newHosts)) g₀=>DescentResetFieldAssembler.raw metaBits (actualMeta B (originalTrunkRack B) x (trunkCandidate B) r g₀))
          nextM (((A).trunkScene floor scene safe).image initial) := by
  exact (reached_trunk_with_registers
    (B:=B) (oldM:=oldM) (nextM:=nextM) (field:=field) (metaBits:=metaBits) (calendar:=calendar) (paid:=paid)
    (floor:=floor) (old:=old) (flags:=flags) (countBank:=countBank) (inverse:=inverse) (safe:=safe)
    (initial:=initial) (record:=record) (active:=active) (countBefore:=countBefore) (invBefore:=invBefore)
    (rankBefore:=rankBefore) (countRead:=countRead) (invRead:=invRead) (rankRead:=rankRead)
    (neighbors:=neighbors) (issued:=issued) (degree:=degree) (cap:=cap) (alphabet:=alphabet)
    (machine:=machine) (packed:=packed) (limit:=limit)).1

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
