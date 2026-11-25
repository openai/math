import OAI.Hierarchy.DescentDatedOrdinarySignedPhase
import OAI.Hierarchy.DescentSignedLedgerReads

namespace OAI
/-! Exact word-level inputs/outputs of the dated rank and route calendar,
all read from the same immutable prefix of the actual final memory. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentParallelBase DescentParallelBase.ParentFilter DescentDyadicSpan DescentOrdinarySignedMeta
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (s:SignedExtent) (I:s.Input) (base:ℕ) (m:Memory w)
local notation "sheet" => s.installed I base m
variable (ok:s.Fits I base w) (room:s.roof base<2^w)
include ok room

theorem funded_field (i:Fin 3) (j:Fin s.hdrRows):
    sheet (base+i.val*span s.hdrRows+j.val)=(DescentOrdinaryDonorRankDirectory.expression I.rankBanks s.priorHosts (fieldIndex i)).eval sheet (j.val:Word w):=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 0 (by change _<21;decide) (s.installed_words I base m ok room).1
  exact (p i j).trans (by simp [fromIndex,i.isLt])

theorem funded_map (j:Fin s.mapWords):
    sheet (s.mapBase base+j.val)=(s.maps I.hostPitch j.val:Word w):=by
  exact (SignedPrefix.at_job sheet (s.jobs I base) base 1 (by change _<21;decide) (s.installed_words I base m ok room).1) j

theorem funded_view (i:Fin 3) (j:Fin s.viewRows):
    sheet (s.viewBase base+i.val*span s.viewRows+j.val)=
      (indexed (.lookup (subbank (s.mapBase base) s.viewRows 0) .row) s.hdrRows (subbank base s.hdrRows i.val)).eval sheet (j.val:Word w):=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 2 (by change _<21;decide) (s.installed_words I base m ok room).1
  exact (p i j).trans (by simp [fromIndex,i.isLt])

theorem static_path:
    Static (DescentOrdinaryDonorSources.PathKeys.table (s.keyStart base) s.degree s.fieldBits s.fieldBits s.lanes)
      (DescentOrdinaryDonorSources.PathKeys.merge s.reach (a:=s.fieldBits) (b:=s.fieldBits)) s.lanes sheet:=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 3 (by change _<21;decide) (s.installed_words I base m ok room).1
  apply SignedPrefix.at_table _ _ _ _ _ id _ (fun _=>rfl) p
  intro i;fin_cases i <;> change _*s.lanes≤_*s.lanes <;> apply Nat.mul_le_mul_right <;> omega

theorem funded_lookup (i:Fin s.lookupWords):
    sheet (s.lookupStart base+i.val)=(DescentPackedChildNeighbor.SIMD.ROM.numbers (s.reach*s.reach) s.fieldBits s.fieldBits s.lanes s.hosts s.groups i.val:Word w):=
  (SignedPrefix.at_job sheet (s.jobs I base) base 4 (by change _<21;decide) (s.installed_words I base m ok room).1) i

theorem funded_rank (z:s.Socket) (i:Fin 5) (row:Fin s.slab):
    sheet ((s.rankPage base z i).base+row.val)=(s.rankField I base z i).eval sheet (row.val:Word w):=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 5 (by change _<21;decide) (s.installed_words I base m ok room).1
  let j:=finProdFinEquiv (s.socketId z,i)
  exact (p j row).trans (by simp only [fromIndex,dite_eq_left j.isLt,Fin.eta,j,Equiv.symm_apply_apply])

theorem static_peer:
    Static (DescentOrdinaryDonorSources.ROM.table (s.peerStart base) s.lowSites s.fieldBits s.lanes)
      (DescentOrdinaryDonorSources.peerDigit s.lowSites (b:=s.fieldBits)) s.lanes sheet:=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 6 (by change _<21;decide) (s.installed_words I base m ok room).1
  apply SignedPrefix.at_table _ _ _ _ _ id _ (fun _=>rfl) p
  intro i;fin_cases i <;> change _*s.lanes≤_*s.lanes <;> apply Nat.mul_le_mul_right <;> omega

theorem funded_donor (z:s.Socket) (f:Fin 11) (row:Fin s.slab):
    sheet ((subbank (s.localStart base) s.slab (s.localId z f)).base+row.val)=(s.donorField I base z f).eval sheet (row.val:Word w):=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 7 (by change _<21;decide) (s.installed_words I base m ok room).1
  let j:=finProdFinEquiv (s.socketId z,f)
  exact (p j row).trans (by simp only [fromIndex,dite_eq_left j.isLt,Fin.eta,j,Equiv.symm_apply_apply])

theorem funded_transpose (z:s.Socket) (f:Fin 11) (l:Fin s.lowSites) (row:Fin s.oldSlab):
    sheet ((subbank (s.projectedStart base) s.oldSlab (s.projectedId z f l)).base+row.val)=
      (s.transposed base (finProdFinEquiv (s.socketId z,f)) l).eval sheet (row.val:Word w):=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 8 (by change _<21;decide) (s.installed_words I base m ok room).1
  let j:=finProdFinEquiv (finProdFinEquiv (s.socketId z,f),l)
  exact (p j row).trans (by simp only [fromIndex,dite_eq_left j.isLt,Fin.eta,j,Equiv.symm_apply_apply])

theorem static_forward:
    let f:=SourceReturn.Query.forward s.reach s.lowSites
    Static (DescentOrdinaryAtomFieldRAM.ROM.joined (DescentOrdinaryAtomFieldRAM.ROM.binary f s.lanes) s.forwardBits (s.forwardBase base) id) f s.lanes sheet:=by
  intro f
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 9 (by change _<21;decide) (s.installed_words I base m ok room).1
  apply SignedPrefix.at_table _ _ _ _ _ id _ (fun _=>rfl) p
  intro i;fin_cases i <;> change _*s.lanes≤_*s.lanes <;> apply Nat.mul_le_mul_right <;> omega

theorem static_return_key:
    let f:=SourceReturn.Query.finish s.reach s.lowSites
    Static (DescentOrdinaryAtomFieldRAM.ROM.joined (DescentOrdinaryAtomFieldRAM.ROM.binary f s.lanes) s.finishBits (s.backBase base) id) f s.lanes sheet:=by
  intro f
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 10 (by change _<21;decide) (s.installed_words I base m ok room).1
  apply SignedPrefix.at_table _ _ _ _ _ id _ (fun _=>rfl) p
  intro i;fin_cases i <;> change _*s.lanes≤_*s.lanes <;> apply Nat.mul_le_mul_right <;> omega

theorem static_return (j:Fin s.routeTotal):
    Static (SourceReturn.RAM.ROM.table s.reach s.lowSites s.fieldBits s.lanes (s.routeStart base) j) (SourceReturn.RAM.choose (b:=s.fieldBits) j) s.lanes sheet:=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 11 (by change _<21;decide) (s.installed_words I base m ok room).1
  exact SignedPrefix.at_table _ _ _ _ _ (SourceReturn.RAM.ROM.address j)
    (fun i=>SourceReturn.RAM.ROM.bound i) (fun i=>SourceReturn.RAM.ROM.at_ j i) p

theorem funded_return (c:s.Consumer) (f:Fin 11) (row:Fin s.oldSlab):
    sheet ((subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)).base+row.val)=(s.routed I base c f).eval sheet (row.val:Word w):=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 12 (by change _<21;decide) (s.installed_words I base m ok room).1
  let j:=finProdFinEquiv (s.requestId c,f)
  exact (p j row).trans (by simp only [fromIndex,dite_eq_left j.isLt,Fin.eta,j,Equiv.symm_apply_apply])

theorem static_joins (f:Fin 11):
    Static (Fused.TablesROM.joins s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes (s.shapesStart base) f)
      (DescentPacking.PackedMatch.Local.Gather.setField (d:=s.fieldBits) f) s.lanes sheet:=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 13 (by change _<21;decide) (s.installed_words I base m ok room).1
  exact SignedPrefix.at_table _ _ _ _ _ (Fused.TablesROM.address (f.castAdd 2)) (fun j=>Fused.TablesROM.page_bits j)
    (Fused.TablesROM.insert_page f) p

theorem static_controls:
    Static (RawControls.flagsTable (s.rawStart base) s.fieldBits s.fieldBits s.lanes)
      (rawFlags (a:=s.fieldBits)) s.lanes sheet ∧
    Static (RawControls.unitsTable (s.rawStart base) s.fieldBits s.fieldBits s.lanes)
      (rawUnits (a:=s.fieldBits) (b:=s.fieldBits)) s.lanes sheet:=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 14 (by change _<21;decide) (s.installed_words I base m ok room).1
  constructor
  · exact SignedPrefix.at_table _ _ _ _ _ (Fin.castAdd 2) (fun j=>RawControls.bitsBound _ _ _ j) (fun i=>by fin_cases i <;> rfl) p
  · exact SignedPrefix.at_table _ _ _ _ _ (Fin.natAdd 2) (fun j=>RawControls.bitsBound _ _ _ j) (fun i=>by fin_cases i <;> rfl) p

theorem static_formatter:
    Static (pairTable (s.metaStart base) I.newDegree s.fieldBits s.lanes) (pair s.fieldBits) s.lanes sheet ∧
    Static (metaTable (s.metaStart base) I.newDegree s.fieldBits s.lanes) (format I.newDegree s.fieldBits) s.lanes sheet:=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 15 (by change _<21;decide) (s.installed_words I base m ok room).1
  constructor
  · exact SignedPrefix.at_table _ _ _ _ _ (Fin.castAdd 2) (fun j=>pageFits _ _ _ j) (fun i=>by fin_cases i <;> rfl) p
  · exact SignedPrefix.at_table _ _ _ _ _ (Fin.natAdd 2) (fun j=>pageFits _ _ _ j) (fun i=>by fin_cases i <;> rfl) p

theorem static_gate:
    Static (gateTable (s.gateStart base) s.fieldBits s.lanes) (keepField (b:=s.fieldBits)) s.lanes sheet:=by
  have p:=SignedPrefix.at_job sheet (s.jobs I base) base 16 (by change _<21;decide) (s.installed_words I base m ok room).1
  apply SignedPrefix.at_table _ _ _ _ _ id _ (fun _=>rfl) p
  intro i;fin_cases i <;> change _*s.lanes≤_*s.lanes <;> apply Nat.mul_le_mul_right <;> omega

theorem funded_peer_key (j:Fin (2^DescentOrdinarySocketPeer.bits s.fieldBits s.lanes)):
    sheet (s.peerKeyBase base+j.val)=(DescentOrdinarySocketPeer.table s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes j.val:Word w):=
  (SignedPrefix.at_job sheet (s.jobs I base) base 17 (by change _<21;decide) (s.installed_words I base m ok room).1) j

theorem funded_peer_lookup (j:Fin s.peerLookupWords):
    sheet (s.peerROMBase base+j.val)=(DescentPackedChildNeighbor.SIMD.ROM.numbers s.peerKinds s.peerBits s.fieldBits s.lanes s.hosts s.groups j.val:Word w):=
  (SignedPrefix.at_job sheet (s.jobs I base) base 18 (by change _<21;decide) (s.installed_words I base m ok room).1) j

theorem funded_peer_head (j:Fin s.peerHeadWords):
    sheet (s.peerHeadBase base+j.val)=(DescentOrdinaryCompactPeer.ROM.contents s.priorHosts s.hosts (s.reach*s.reach) s.lowSites I.newDegree I.hostPitch j.val:Word w):=
  (SignedPrefix.at_job sheet (s.jobs I base) base 19 (by change _<21;decide) (s.installed_words I base m ok room).1) j

theorem funded_peer_value (r:Fin s.peerHeadRows):
    sheet (s.peerHeadOut base+r.val)=(s.peerHeadExpr I base).eval sheet (r.val:Word w):=by
  have q:=(SignedPrefix.at_job sheet (s.jobs I base) base 20 (by change _<21;decide) (s.installed_words I base m ok room).1) (0:Fin 1) r
  simp only [Fin.val_zero,Nat.zero_mul,Nat.add_zero] at q
  exact q

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
