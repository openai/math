import OAI.Hierarchy.DescentOrdinaryRawRankFields

namespace OAI
/-! # The six ordinary parent fields retained through either capture -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material
open DescentSIMDLookup DescentSharedCableNames DescentHaloWalkRAM DescentHaloPackedRebase
open DescentPacking.PackedMatch.Local
open scoped Classical Fin.CommRing
noncomputable section

def rawAnchorMark (s : Shape) (v : Parts s) (x : Fin s.blocks) (old : Fin s.cap) : Bool :=
  let signed:=(encode _ (s.blocks*(2*s.cap))).symm v.cables
    (finProdFinEquiv (x,old.castLE (by omega : s.cap≤2*s.cap)))
  (DescentSignedCableCodec.decode s.degree s.cap signed).elim false (·.markedOut)

/-- Forward paths are evaluated on the original donor's data for both
endpoints, including a raw edge internalized by either quotient. The rank
is that donor's ordinal at the reached receiver, measured on the left path. -/
def rawObserved (s : Shape) (u : Setup) (v : Parts s) (rev : Cell (chartBits s)) (z : Seat s) :
    Fin 6 → Cell u.fieldBits :=
  let left:=rawAtSeat s u.profile u.motifWidth u.slots false v z.1 z.2.1 z.2.2
  let right:=rawAtSeat s u.profile u.motifWidth u.slots true v z.1 z.2.1 z.2.2
  let donor:=seatDonor s u.profile u.motifWidth u.slots v z.1 z.2.1
  let report_:=report u.oldBits u.gain u.slots donor z.2.2
  let first:=samePre report_
  let second:=(!first && samePost report_)
  let root:=if left.val=0 then 0 else ranked s rev left
  ![(left.val:Cell u.fieldBits),(right.val:Cell u.fieldBits),(first.toNat:Cell u.fieldBits),
    (second.toNat:Cell u.fieldBits),(root:Cell u.fieldBits),((rawAnchorMark s v z.1 z.2.1).toNat:Cell u.fieldBits)]

theorem raw_paths (s : Shape) (u : Setup) (v : Parts s) (rev : Cell (chartBits s)) (z : Seat s) (side : Bool) :
    rawObserved s u v rev z (if side then 1 else 0)=
      ((rawAtSeat s u.profile u.motifWidth u.slots side v z.1 z.2.1 z.2.2).val:Cell u.fieldBits) := by
  cases side <;> rfl

theorem raw_flags (s : Shape) (u : Setup) (v : Parts s) (rev : Cell (chartBits s)) (z : Seat s) :
    let d:=seatDonor s u.profile u.motifWidth u.slots v z.1 z.2.1
    let report_:=report u.oldBits u.gain u.slots d z.2.2
    rawObserved s u v rev z 2=((samePre report_).toNat:Cell u.fieldBits) ∧
      rawObserved s u v rev z 3=((!samePre report_ && samePost report_).toNat:Cell u.fieldBits) :=
  ⟨rfl,rfl⟩

theorem raw_reverse_rank {H : ℕ} (s : Shape) (u : Setup) (v : Parts s) (z : Seat s)
    (R : Fin H→Fin s.degree→Option (Fin H)) («mutual» : ∀h h' j,R h j=some h'→∃q,R h' q=some h)
    (old recv : Fin H) (p : Fin (breadth s.degree))
    (held : rawAtSeat s u.profile u.motifWidth u.slots false v z.1 z.2.1 z.2.2=Packed.token (some p))
    (reached : walk R old (path p) 4=some recv) :
    rawObserved s u v (digest (reverseEntries s R old)) z 4=
      (Ranks.earlier (Rebase.terminal R) recv old.val:Cell u.fieldBits) := by
  obtain ⟨_,_,_,rank⟩:=Rebase.actual R «mutual» old recv p reached
  change ((if (rawAtSeat s u.profile u.motifWidth u.slots false v z.1 z.2.1 z.2.2).val=0 then 0 else
    ranked s (digest (reverseEntries s R old)) (rawAtSeat s u.profile u.motifWidth u.slots false v z.1 z.2.1 z.2.2):ℕ):Cell u.fieldBits)=_
  have ordinal : (rawAtSeat s u.profile u.motifWidth u.slots false v z.1 z.2.1 z.2.2).val = p.val+1 :=
    congrArg (fun c : Cell (ParentIncidence.pathBits s.degree) => c.val) held
  have present : (rawAtSeat s u.profile u.motifWidth u.slots false v z.1 z.2.1 z.2.2).val ≠ 0 := by omega
  have readback : ranked s (digest (reverseEntries s R old))
      (rawAtSeat s u.profile u.motifWidth u.slots false v z.1 z.2.1 z.2.2) =
        (reverseEntries s R old p).val :=
    (congrArg (ranked s (digest (reverseEntries s R old))) held).trans (ranked_read s _ p)
  rw [ite_eq_right present,readback]
  exact congrArg (fun r:ℕ=>(r:Cell u.fieldBits)) rank

@[simp] theorem raw_mark (s : Shape) (u : Setup) (v : Parts s) (rev : Cell (chartBits s)) (z : Seat s) :
    rawObserved s u v rev z 5=((rawAnchorMark s v z.1 z.2.1).toNat:Cell u.fieldBits) := rfl

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material

end OAI
