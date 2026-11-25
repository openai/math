import OAI.ThreeFlat.Diagonal.PhysicalNodeWordFits
import OAI.ThreeFlat.Diagonal.PhysicalIndividualCharge
import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace

namespace OAI
/-! # Word-sized cursor fees for the original fold schedule -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction
open scoped BigOperators Classical
variable {F : Type} [Field F]
namespace Block

/-- Independent of the state of the native node publisher, the true
geometric recurrence on its selected stage history has two word-sized columns. -/
theorem cursor_archive_fits (B : Block F) {u rem low off slots total copies depth stride cells e tariff : ℕ}
    (hu : 40≤u) (he : e+2≤u) (half : low≤u^10/2) (degree : 2^(B.exponent 0)≤u)
    (growth : B.peakBase≤u) (slot : off*slots*3≤u^e)
    (traceCost : TraceBitHeader.seedTraceWork low stride cells copies depth≤2^low*u^e)
    (tariffBound : tariff≤u^e) (hk : 2≤(B.repeat (u^8)).charge+rem)
    (h : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.History) :
    let A := B.cursorState hk low off slots
    let r := (B.repeat (u^8)).run rem A
    r.ArchiveFits (16*u^10) tariff h (B.charges (u^8) rem A)
      (B.seedWork hk low off slots total copies depth stride cells) (B.clippedPairs hk low off slots total) := by
  intro A r
  let start := B.seedWork hk low off slots total copies depth stride cells
  have covers (v) : B.clippedPairs hk low off slots total v≤ start v := by
    have h := B.seedWork_covers hk low off slots total copies depth stride cells v
    change _≤B.seedWork hk low off slots total copies depth stride cells v
    omega
  apply r.archiveFits_of_peak h (B.charges (u^8) rem A) start _ _ _ covers
  intro z
  have lift : u^e≤u^(e+2) := Nat.pow_le_pow_right (by omega) (by omega)
  have pos : 1≤u^(e+2) := Nat.pow_pos (by omega)
  have bounded (v) : start v≤2^low*u^(e+2) := B.cursor_start_le (by omega) hk degree slot traceCost v
  have peak := B.cursor_terminal_peak (e:=e+2) (unitWork:=max 1 tariff) hu he half growth (slot.trans lift) hk
    h start bounded (max_le pos (tariffBound.trans lift)) (r.finalSite h z)
  have work : max 1 tariff*r.rootArray h (B.charges (u^8) rem A) start z≤2^((3*u^10+4)/5) := by
    change r.rootArray h (B.charges (u^8) rem A) start ((r.finalSite h).symm ((r.finalSite h) z)) *
      max 1 tariff ≤ 2^((3*u^10+4)/5) at peak
    rwa [Equiv.symm_apply_apply, Nat.mul_comm] at peak
  have pos10 : 0<u^10 := Nat.pow_pos (by omega)
  exact work.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))


end Block
end ThreeFlat.Diagonal.PhysicalStage
end

end OAI
