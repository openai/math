import OAI.ThreeFlat.Diagonal.TraceVirtualBanks
import OAI.ThreeFlat.Diagonal.TickWorkspace
import OAI.ThreeFlat.RAM.HistoryStageBody

namespace OAI
/-! # Physical S12, S13, S14 and virtual trace region separation -/
namespace ThreeFlat.Diagonal.TraceBitHeader
open RAM RAM.HistoryInitialSeed RAM.HistoryStageBody.Physical TickWorkspace
open scoped Classical
variable {F : Type*} [Fintype F] [Field F] {w : ℕ}

theorem visible_regions (u cells slots rows masks : ℕ) (im : RAM.PhysicalPrelude.Image F w)
    (loc : TraceSuffixOracle.Locations)
    (rawRoom : 11*cells ≤ stride u) (two : 2 ≤ stride u)
    (description : loc.description+im.advice≤base u 52)
    (parameters : loc.parameters+im.parameters≤base u 52)
    (table : loc.table+w*FixedTraceImage.count im.G≤base u 52) :
    Visible (base u 52) cells (base u 54) slots (base u 56) rows (base u 55) masks im loc := by
  exact ⟨two.trans (TickWorkspace.lower ..),
    Or.inr ((Nat.add_le_add_left rawRoom _).trans (apart (by decide : 52<54))),
    Or.inr ((Nat.add_le_add_left rawRoom _).trans (apart (by decide : 52<56))),
    Or.inr ((Nat.add_le_add_left rawRoom _).trans (apart (by decide : 52<55))),
    Or.inl description,Or.inl parameters,Or.inl table⟩

theorem selected_separated (u : ℕ) (B : TraceBucketAtom.Layout) (z : HistoryInitialSeed.Site)
    (V : ℕ) (vol : volume u=V) (wide : 8≤V) (idx : z.index<V)
    (rows : 4*z.rows (initial u B)≤V) (pins : z.extPins≤V) :
    Separated (initial u B) z := by
  have strideEq : stride u=V^4 := congrArg (·^4) vol
  have s12:=TickWorkspace.apart (u:=u) (by decide : 12<13)
  have s13:=TickWorkspace.apart (u:=u) (by decide : 13<14)
  rw [strideEq] at s12 s13
  have n : z.index*(V*V)+V+z.extPins≤V^4 := by
    have h : (z.index+1)*(V*V)≤V*(V*V):=Nat.mul_le_mul_right _ idx
    have room : 2*V≤V*V := by nlinarith
    have larger : V^3≤V^4 := Nat.pow_le_pow_right (by omega) (by decide)
    nlinarith
  have node : 8*z.index+6≤V^4 := by
    have h : 8*(z.index+1)≤8*V:=Nat.mul_le_mul_left _ idx
    have h2 : 8*V≤V^2 := by nlinarith
    exact (by omega : 8*z.index+6≤V^2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  constructor
  · change base u 12+z.index*(volume u*volume u)+4*z.rows (initial u B)≤
      base u 12+z.index*(volume u*volume u)+volume u
    rw [vol];omega
  · change base u 12+z.index*(volume u*volume u)+volume u+z.extPins≤base u 13+8*z.index
    rw [vol];omega
  · change base u 13+8*z.index+6≤base u 14+volume u
    omega

theorem protected_high (u : ℕ) (B : TraceBucketAtom.Layout) (z : HistoryInitialSeed.Site)
    (sep : Separated (initial u B) z) (room : volume u+42 ≤ stride u)
    (slot length : ℕ) (slotHigh : 14<slot) : Protected (initial u B) z (base u slot) length := by
  apply Protected.of_span sep (Or.inr ?_)
  change base u 14+volume u+42≤base u slot
  have top:=TickWorkspace.apart (u:=u) slotHigh
  omega

theorem protected_low (u : ℕ) (B : TraceBucketAtom.Layout) (z : HistoryInitialSeed.Site)
    (sep : Separated (initial u B) z) (start len : ℕ) (room : start+len≤base u 12) :
    Protected (initial u B) z start len := by
  apply Protected.of_span sep (Or.inl ?_)
  change start+len≤base u 12+_
  omega

theorem immutable_regions (u cells dictionaryRows maskCount : ℕ) (B : TraceBucketAtom.Layout)
    (z : HistoryInitialSeed.Site) (im : RAM.PhysicalPrelude.Image F w) (loc : TraceSuffixOracle.Locations)
    (sep : Separated (initial u B) z) (room : volume u+42 ≤ stride u)
    (ids : B.tableIds=base u 54) (dict : B.dictionary=base u 56) (masks : B.masks=base u 55)
    (two : 2≤base u 12) (description : loc.description+im.advice≤base u 12)
    (parameters : loc.parameters+im.parameters≤base u 12)
    (table : loc.table+w*FixedTraceImage.count im.G≤base u 12) :
    Immutable (initial u B) z B cells dictionaryRows maskCount im loc := by
  refine ⟨protected_low u B z sep 0 2 two,?_,?_,?_,protected_low u B z sep _ _ description,
    protected_low u B z sep _ _ parameters,protected_low u B z sep _ _ table⟩
  · rw [ids];exact protected_high u B z sep room _ _ (by decide)
  · rw [dict];exact protected_high u B z sep room _ _ (by decide)
  · rw [masks];exact protected_high u B z sep room _ _ (by decide)


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
