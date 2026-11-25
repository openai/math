import OAI.Hierarchy.DescentOrdinaryOriginBounds
import OAI.Hierarchy.DescentOrdinaryArgumentWidths
import OAI.Hierarchy.DescentArgumentWidthArithmetic

namespace OAI
/-! # Scalar parameters determining the largest key of the ordinary argument phase -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentRawCablePanel DescentCompiler.TerminalScale DescentArgumentWidthArithmetic
open DescentOrdinaryOriginBounds
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

/-- These fields omit address offsets, the number of hosts, the global population
and the lane pitches. The chip format and vector key are those of the emitted code. -/
def argumentParameters (A : ArgumentEntry v) : Fin 23 → ℕ :=
  ![16,A.previous.size,A.previous.nodes,
    max A.roleBits (DescentPrimitivePalette.printedBits v.gadget v.palette.seedWidth v.palette.grainLimit v.palette.rotor),
    v.reference.oldNodes,v.reference.countBits,
    A.clip.venue.paths,A.previous.blocks,DepotRAM.totalBits (A.chip v).format,
    v.reference.degree+1,2^v.reference.k,v.reference.capacity,v.reference.nameBits,
    v.reference.bits,v.bornBook.blocks,v.bornBook.cap,v.bornBook.names,v.bornBook.widths,
    v.vector.bookBits,v.resolver.size,v.resolver.nodes,v.resolver.operands,v.metadata.paidBits]

/-- In addition to the reference and selector parameters, the returned columns carry
the old grain field and the metadata field of this very date. -/
theorem argument_width_bound (A : ArgumentEntry v) (U : ℕ)
    (bound : ∀j,v.argumentParameters A j≤ U) (grain : v.bornBook.bits≤ U)
    (metadata : v.metadata.chart.bits≤ U) (i : Fin 16) :
    v.argumentWidths A i≤ U^11 :=by
  have large : 16≤ U:=bound 0
  have pos : 0<U:=by omega
  have big : 2≤ U:=by omega
  have small {x : ℕ} (h : x≤16) : x≤ U^1:=one (by omega)
  have refK:=DescentArgumentWidthArithmetic.reference v.reference U large (bound 9) (bound 10) (bound 4) (bound 11)
    (bound 13) (bound 12) (bound 5)
  have role : A.roleBits ≤ U := (Nat.le_max_left ..).trans (bound 3)
  have printed : DescentPrimitivePalette.printedBits v.gadget v.palette.seedWidth v.palette.grainLimit v.palette.rotor ≤ U :=
    (Nat.le_max_right ..).trans (bound 3)
  have old : v.reference.oldNodes≤ U:=bound 4
  have count : v.reference.countBits≤ U:=bound 5
  have walks : A.clip.venue.paths≤ U:=bound 6
  have blocks : A.previous.blocks≤ U:=bound 7
  have size : v.resolver.size≤ U:=bound 19
  have nodes : v.resolver.nodes≤ U:=bound 20
  have sumsize:=add big (one size) (small (by decide : 2≤16))
  have chip : v.bornBook.chipBits≤ U^8:=
    births large (bound 14) (bound 15) (bound 16) (bound 17)
  have origin : v.originChart.peak≤ U^9:=
    local_width (by omega) (bound 9) (bound 10) (bound 4) (bound 11) (bound 20)
  have digit : v.originChart.ordinalBits*v.originChart.newNodes≤ U^9:=
    (Nat.le_max_right _ _).trans origin
  fin_cases i
  · change (A.previous.size+2)*A.previous.nodes≤_
    exact raise pos (mul (add big (one (bound 1)) (small (by decide))) (one (bound 2))) (by decide)
  · change A.roleBits*v.reference.oldNodes≤_
    exact raise pos (mul (one role) (one old)) (by decide)
  · change v.reference.countBits*(A.clip.venue.paths*A.previous.blocks)+v.reference.countBits≤_
    exact raise pos (add big (mul (one count) (mul (one walks) (one blocks))) (one count)) (by decide)
  · exact raise pos (one (bound 8)) (by decide)
  · exact refK.1
  · exact raise pos refK.2 (by decide)
  · change v.bornBook.chipBits*1+v.bornBook.chipBits≤_
    simpa only [mul_one] using raise pos (add big chip chip) (by decide : 9≤11)
  · exact raise pos (one (bound 18)) (by decide)
  · exact raise pos (mul sumsize (one nodes)) (by decide)
  · exact raise pos (add big sumsize sumsize) (by decide)
  · exact raise pos (mul (small (by decide : 11≤16)) sumsize) (by decide)
  · exact raise pos origin (by decide)
  · change (v.originChart.ordinalBits*v.originChart.newNodes)*1+_≤_
    simpa only [mul_one] using raise pos (add big digit digit) (by decide : 10≤11)
  · exact raise pos (returned large metadata metadata nodes size (bound 21)) (by decide)
  · exact max_le (max_le (raise pos chip (by decide : 8≤11))
        (raise pos (mul (one grain) (one nodes)) (by decide : 1+1≤11)))
      (raise pos (one printed) (by decide : 1≤11))
  · change max (v.metadata.chart.bits*(v.resolver.nodes+1)) (max v.metadata.paidBits
      (v.resolver.size+2+v.metadata.chart.bits))≤_
    exact max_le (raise pos (mul (one metadata) (add big (one nodes) (small (by decide)))) (by decide))
      (max_le (raise pos (one (bound 22)) (by decide)) (raise pos (add big sumsize (one metadata)) (by decide)))


/-- The cut needed to buy the sixteen physical dictionary widths is independent
of the fraction reserved for host work. -/
theorem argument_unit_at_scale (A : ArgumentEntry v) (J a : ℕ)
    (bound : ∀j,(v.withFundedArguments 0 A).argumentParameters (v.fundedEntry 0 A) j≤ scale J a)
    (grain : (v.withFundedArguments 0 A).bornBook.bits≤ scale J a)
    (metadata : (v.withFundedArguments 0 A).metadata.chart.bits≤ scale J a) :
    v.fullArgumentUnit A≤ scale J (11*a) :=by
  apply Finset.sup_le
  intro i _
  refine ((v.withFundedArguments 0 A).argument_width_bound (v.fundedEntry 0 A) _ bound grain metadata i).trans_eq ?_
  unfold scale
  rw [←pow_mul]
  congr 1
  ring

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
