import OAI.Hierarchy.DescentCalendarContactPolynomial
import OAI.Hierarchy.DescentResetReceivedVolume
import OAI.Hierarchy.DescentResetReceivedSourcePrice

namespace OAI
/-! The dated word coefficient for a complete candidate receipt uses only fixed
rotor data, the incoming capacity, the block width, and the original source operands. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty DescentDenseHostOrder DescentResetLocalRoster DescentResetPeerUnionRAM
open CandidateFront
noncomputable section
set_option quotPrecheck false
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (D f g : ℕ)
variable {ι : ℕ→Type*} {J : ℕ→ℕ}
variable (v : ∀h,ι h→ResetOutput) (S : ∀h,ι h→AtomSchedule)
    (k tail age oldLane newLane rootField «meta» C packet U gain : ∀h,ι h→ℕ)
    (calendar : ∀h,ι h→List ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "sh" => fun h i=>(roster board (k h i) height).card
local notation "cap" => fun h i=>((calendar h i).take (age h i)).prod*256
local notation "front" h:arg i:arg => setupFront (S h i) board (k h i) (tail h i) (age h i) D f g
  (oldLane h i) (newLane h i) (rootField h i) («meta» h i) (C h i) (packet h i) (calendar h i)

private theorem evidence_small (D wires : ℕ) {count shapes work rows : ∀h,ι h→ℕ}
    (hc : SmallAt J count) (hs : SmallAt J shapes) (hw : SmallAt J work) (hr : SmallAt J rows) :
    SmallAt J (fun h i=>evidenceFactor D (count h i) (shapes h i) wires (work h i)+
      peerFactor D (shapes h i) (rows h i) (work h i)) := by
  let cn (x : ℕ) := SmallAt.const (ι:=ι) J x
  have book := cn (((D+2)+2)*(2*1))
  have score := (cn 14).add ((cn (D+2)).mul (hw.add (cn 11)))
  have wide := (cn 1).mul hs
  have bucket := ((cn 2).mul wide).add (cn 1)
  have lookup := ((cn 2).mul (hs.mul (cn 1))).add (cn 1)
  have both := bucket.add lookup
  have pages := ((((cn 2).mul bucket).add ((cn wires).mul lookup)).add ((cn 2).mul both)).add both
  have oldClock := ((cn 4).add ((cn 10).mul book)).add
    ((cn 4).add (hc.mul ((cn 4).add ((cn 1).mul (((cn 2).mul score).add (cn 4))))))
  have oldText := ((cn 15).mul (book.add (cn 1))).add
    ((cn 15).add (hc.mul ((cn 11).add ((cn 4).mul score))))
  have evidence := (((oldClock.add ((cn 7).mul oldText)).add ((cn 16).add ((cn 10).mul pages)))).add
    ((cn 7).mul ((cn 15).mul (pages.add (cn 4))))
  have slots := ((cn (D+1)).mul hs).add (cn 3)
  have literal := ((cn 2).mul ((cn 2).mul (wide.add (cn 1)))).add (cn (2*(1+1)))
  have flags := (slots.mul hr).mul (cn 1)
  have scan := ((cn 42).mul wide).add (((cn 1).mul hs).mul (hr.mul (hw.add (cn 8))))
  have scanText := (cn 42).add ((cn 1).mul (hr.mul (hw.add (cn 8))))
  have side := slots.add (cn 1)
  have compute : SmallAt J (fun h i => Program.sortWork (Candidates.count (shapes h i) D)) := by
    simpa only [Program.sortWork,Candidates.count,pow_succ,pow_zero,Nat.one_mul] using
      (cn 100).mul ((side.mul side).mul side)
  have time := (((cn 4).add ((cn 10).mul literal)).add ((cn 4).add ((cn 10).mul flags))).add
    (((cn 4).add (slots.mul ((cn 4).add (((cn 2).mul scan).add ((cn 4).mul wide))))).add
      ((cn 4).add ((cn 3).mul ((cn 4).add (wide.mul (((cn 2).mul compute).add (cn 4)))))))
  have declarations := (((cn 15).mul (literal.add (cn 1))).add ((cn 15).mul (flags.add (cn 1)))).add
    (((cn 15).add (slots.mul ((cn 11).add ((cn 4).mul scanText)))).add ((cn 15).add ((cn 3).mul ((cn 11).add ((cn 4).mul compute)))))
  have groups := wide.mul (cn 4)
  have loc := (cn 3).mul (((cn 2).mul groups).add (cn 1))
  have chart := (cn (4*1)).add (wide.add ((cn 1).add groups))
  have mounts := ((((cn 4).add ((cn 10).mul loc)).add ((cn 4).add ((cn 10).mul chart))).add
    ((cn 4).add (groups.mul (cn 84)))).add ((cn 4).add (groups.mul (cn 25004)))
  have texts := ((((cn 15).mul (loc.add (cn 1))).add ((cn 15).mul (chart.add (cn 1)))).add (cn 171)).add (cn 50011)
  exact evidence.add (((time.add mounts).add ((cn 4).add ((cn 10).mul ((cn 3).mul wide)))).add
    ((cn 7).mul ((declarations.add texts).add ((cn 15).mul (((cn 3).mul wide).add (cn 1))))))

theorem calendar_receipt_paid (mounted : ∀ h i,(v h i).front=front h i)
    (window : SmallAt J (fun h i=>2^(k h i))) (capacity : SmallAt J cap)
    (operand : SmallAt J U) (increase : SmallAt J gain) :
    SmallAt J (fun h i=>(v h i).receiptFactor (gain h i) (U h i)) := by
  let cn (z : ℕ):=SmallAt.const (ι:=ι) J z
  have depth : SmallAt J k:=window.of_le (fun _ _=>Nat.lt_two_pow_self.le)
  have twice : SmallAt J (fun h i=>2^(k h i+1)):=by simpa only [pow_succ] using window.mul (cn 2)
  have shapes : SmallAt J sh:=((cn _).mul twice).of_le fun h i=>roster_bound board (k h i) height
  have tickets : SmallAt J (fun h i=>2*DescentFallbackShapeTable.rows (k h i) (2^n)):=
    (cn 2).mul (((depth.add (cn 1)).mul window).mul (cn _))
  have keys: SmallAt J (fun h i=>DescentResetStemPackedIssue.count (2^(k h i)) (cap h i)) :=
    (cn 2).mul (window.mul ((cn 2).mul capacity))
  have roots : SmallAt J (fun h i=>rootSlots (k h i) (2^n)):=twice.add (twice.mul (cn _))
  have evidence : SmallAt J (fun h i=>ClosedReset.Window.publicEvidenceRows board height (k h i) (cap h i)) := by
    change SmallAt J (fun h i=>Axes.rows (2*(2^(k h i)*(2*cap h i)))
      (2*(rootSlots (k h i) (2^n)*(2^n+2^height)))
      (2*(rootSlots (k h i) (2^n)*DescentResetCableSlots.cableCap board height)))
    unfold Axes.rows
    exact keys.add ((cn 1).add ((((cn 2).mul (roots.mul (cn _))).mul keys).add ((cn 2).mul (roots.mul (cn _)))))
  have ev : SmallAt J (fun h i=>(v h i).front.evidenceTrafficFactor (U h i)) := by
    simp only [mounted]
    change SmallAt J (fun h i=>evidenceFactor D (DescentResetStemPackedIssue.count (2^(k h i)) (cap h i))
      (sh h i) (DescentResetCableSlots.cableCap board height) (U h i)+
      peerFactor D (sh h i) (ClosedReset.Window.publicEvidenceRows board height (k h i) (cap h i)) (U h i))
    exact evidence_small D _ keys shapes operand evidence
  have stem : SmallAt J (fun h i=>
      stemCoefficient (v h i).front.peer.oldDegree (v h i).front.oldTicketCount (v h i).front.blocks
        (v h i).front.signedQueries (v h i).front.peer.shapes (U h i) (U h i)) := by
    simp only [mounted]
    exact stemCoefficient_small (cn D) tickets window keys shapes operand operand
  have contact:=calendar_factor_paid board D height v U (fun h i=>contact_fields_from_calendar board (v h i)
    (S h i) (k h i) (tail h i) (age h i) D f g (oldLane h i) (newLane h i) (rootField h i) («meta» h i)
    (C h i) (packet h i) (calendar h i) (mounted h i)) window capacity operand
  have shPaid : SmallAt J (fun h i=>(v h i).front.peer.shapes):=by simp only [mounted];exact shapes
  unfold receiptFactor
  have unit := ((cn 8).mul operand).add (cn 10)
  exact (((ev.mul (shPaid.add (cn 1))).add ((cn 2).mul contact)).add
      (stem.mul ((cn 4).add ((cn 2).mul increase)))).add
    (((cn 4).add (increase.mul (((cn 2).mul unit).add (cn 4)))).add
      ((cn 7).mul ((cn 11).add ((cn 4).mul unit))))


end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
