import OAI.Hierarchy.DescentDatedResetVenueRun
import OAI.Hierarchy.DescentVenueQuantityPrice

namespace OAI
/-! # Full CPU and installed instruction charge for both reset rasters and the next dated venue -/
namespace Hierarchy.DescentCompactVenuePeers
open ProtocolRAM DescentSixParty.Chronology DescentSortedRoster DescentFallbackRankRAM
open DescentStaticWordColumn (names names_seq names_mount names_scan)
noncomputable section
def prototype:Inputs:=⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,fun _=>⟨0,0⟩⟩
def rowWork:=(entry prototype 0 0 0).work
def hubWork:=(flag prototype 0 0).work
def fee (R H:ℕ):=
  DescentVenueQuantityPlanes.tableScanBill (book 0 R H) (H*3) rowWork+
    (4+H*(2*hubWork+4))+7*(11+4*hubWork)

/-- The instruction count for a sorted lookup depends only on the work of its input expressions. -/
private theorem pick_work_eq {D : ℕ} (f g : Fin D → Expr)
    (same : ∀ i, (f i).work = (g i).work) (pos x y : ℕ) (xs : List (Fin D)) :
    (pick f (.lit pos) x xs).work = (pick g (.lit pos) y xs).work := by
  have bit (i j : Fin D) : (rankBit f (f i) j).work = (rankBit g (g i) j).work := by
    unfold rankBit
    generalize prior j = js
    induction js with
    | nil => simp only [List.map_nil, unlessSeen, Expr.work, same]
    | cons t ts ih => simp only [List.map_cons, unlessSeen, Expr.work, same, ih]
  have rank (i : Fin D) : (calculate f (f i)).work = (calculate g (g i)).work := by
    unfold calculate
    generalize (Finset.univ : Finset (Fin D)).toList = js
    induction js with
    | nil => rfl
    | cons j js ih =>
      change (rankBit f (f i) j).work + (foldSum (js.map (rankBit f (f i)))).work + 1 = _
      rw [bit i j, ih]
      rfl
  induction xs with
  | nil => rfl
  | cons i is ih => simp only [pick, Expr.work, same, rank, ih]

theorem billed (B:Inputs)(base R H w:ℕ)(tag:ℕ→Bool):
    (phase B base R H w tag).ticks+7*names (phase B base R H w tag).program=fee R H:=by
  have cost (pos : ℕ) :
      (pick (compact B R H (.lookup (hosts base R H) .row)) (.lit pos) H (List.finRange 3)).work =
      (pick (compact prototype 0 0 (.lookup (hosts 0 0 0) .row)) (.lit pos) 0 (List.finRange 3)).work :=
    pick_work_eq (compact B R H (.lookup (hosts base R H) .row))
      (compact prototype 0 0 (.lookup (hosts 0 0 0) .row)) (fun _ => rfl) pos H 0 (List.finRange 3)
  have e:(entry B base R H).work=rowWork:=by simp only [entry, rowWork, Expr.work, cost]
  have h:(flag B base R).work=hubWork:=rfl
  change ticks B base R H + 7 * names (program B base R H w tag) = fee R H
  simp only [program,ticks,names_seq,names_mount,names_scan,e,h,fee,DescentVenueQuantityPlanes.tableScanBill,book]
  omega
end
end Hierarchy.DescentCompactVenuePeers

namespace Hierarchy.DescentDatedAddressBook.ResetVenue
open DescentSixParty.Chronology
open DescentStaticWordColumn (names names_seq)
noncomputable section
variable (v:ResetVenue)
def fee:=DescentVenueQuantityPlanes.fee v.dense+DescentVenueQuantityPlanes.fee v.actorDims+
  DescentCompactVenuePeers.fee v.rawHosts v.dense.hosts+v.next.tariff

theorem billed (B:Earlier)(base w:ℕ)(first:0<v.dense.oldLanes)(moved:0<v.dense.lanes)(cells:0<v.dense.blocks)
    (actor:0<v.actorLanes)(alive:0<v.next.aliveLanes)(signed:0<v.next.signedLanes)(paid:0<v.next.paidLanes)
    (used:0<v.next.lanes):
    (v.phase B base w).ticks+7*names (v.phase B base w).program≤v.fee:=by
  have f:=DescentVenueQuantityPlanes.billed v.dense (v.paidLayout B base) w first moved cells
  have a:=DescentVenueQuantityPlanes.billed v.actorDims (v.actorLayout B base) w actor moved cells
  have p:=DescentCompactVenuePeers.billed B.ranks (v.peerStart base) v.rawHosts v.dense.hosts w B.tag
  have r:=v.next.price (v.sources B base) (v.venueStart base) w alive signed paid used
  simp only [phase,NativePhase.seq,names_seq,fee]
  change _≤_
  dsimp only [DescentSixParty.StageVenueTail.Date.phase] at *
  omega

end
end Hierarchy.DescentDatedAddressBook.ResetVenue

end OAI
