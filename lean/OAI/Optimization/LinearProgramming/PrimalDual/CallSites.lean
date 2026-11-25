import OAI.Optimization.LinearProgramming.PrimalDual.CallAlignment
import OAI.Optimization.LinearProgramming.PrimalDual.CallSegmentsRoute

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace SubroutineCalls

open RAM RAM.Call RAM.Block CallSegments Bridge

def originalSite (p : Program) (C E : ℕ) : Site :=
  ⟨(firstPrelude p C E).size,firstReturn (firstReturnBase p C E)⟩

def jointSite (p : Program) (C E : ℕ) : Site :=
  let off := firstReturnBase p C E
  ⟨endingBlocks.callPC off,endingBlocks.secondRet off⟩

private theorem image_size (p : Program) (base : ℕ) (ret : ℕ → ℕ) :
    (Call.subroutine p base ret).length = (p.map Call.width).sum :=
  Layout.assemble_length p Call.width _ _ (Call.emit_length _)

theorem original_limit (p : Program) (C E : ℕ) : (originalSite p C E).limit p = firstReturnBase p C E := by
  unfold Site.limit originalSite firstReturnBase
  rw [image_size]

private def middle (bs : EndBlocks) (off : ℕ) : Program :=
  EndBlocks.stopCode bs.infeasible off 0 ++ EndBlocks.stopCode bs.optimum (bs.optPC off) 1 ++
    EndBlocks.stopCode bs.ray (bs.rayPC off) 2 ++ bs.stage.compile (bs.stagePC off) ++ bs.prepare.compile (bs.prepPC off)

private theorem middle_size (bs : EndBlocks) (off : ℕ) : off+(middle bs off).length = bs.callPC off := by
  simp only [middle,List.length_append,EndBlocks.length_stopCode,Block.length_compile,EndBlocks.callPC,
    EndBlocks.prepPC,EndBlocks.stagePC,EndBlocks.rayPC,EndBlocks.optPC]
  omega

private theorem middle_emit (bs : EndBlocks) (p : Program) (off : ℕ) :
    bs.emit p off = middle bs off ++ Call.subroutine p (bs.callPC off) (bs.secondRet off) := by
  simp only [EndBlocks.emit,middle,List.append_assoc]

private def reserveProbe (reserve : ℕ) : Program := [.addrConst 0 reserve]

private theorem probe_budget (reserve : ℕ) : addressBudget (reserveProbe reserve) = reserve := by
  simp [reserveProbe,addressBudget,Instr.addressBudget]

private theorem prelude_equal {p q : Program} (C E : ℕ) (budget : addressBudget p = addressBudget q) :
    firstPrelude p C E = firstPrelude q C E := by
  have headers : firstHeaders p C E = firstHeaders q C E := by unfold firstHeaders; rw [budget]
  have cap : firstStatic p C E = firstStatic q C E := by unfold firstStatic; rw [headers]
  simp only [firstPrelude,firstHeaderBlock,headers,cap]

/-- The address reserve is passed as a number. The template never receives
or inspects the guest instruction list when producing either ordinary part. -/
def family (reserve C E : ℕ) : Template :=
  ⟨(firstPrelude (reserveProbe reserve) C E).compile 0,middle endingBlocks,firstReturn,endingBlocks.secondRet⟩

private theorem positions (bs : EndBlocks) (off : ℕ) : off < bs.optPC off ∧ bs.optPC off < bs.rayPC off ∧
    bs.rayPC off < bs.stagePC off ∧ bs.stagePC off ≤ bs.prepPC off ∧ bs.prepPC off ≤ bs.callPC off := by
  exact ⟨by unfold EndBlocks.optPC; omega,by unfold EndBlocks.rayPC; omega,
    by unfold EndBlocks.stagePC; omega,Nat.le_add_right ..,Nat.le_add_right ..⟩

theorem registered (p : Program) (C E : ℕ) : Registered (family (addressBudget p) C E)
    (program p C E) p (originalSite p C E) (jointSite p C E) := by
  let t := family (addressBudget p) C E
  let off := firstReturnBase p C E
  have prefixEq : t.«prefix» = (firstPrelude p C E).compile 0 :=
    congrArg (fun b : Block => b.compile 0) (prelude_equal C E (probe_budget (addressBudget p)))
  have offset : t.afterFirst p = off := by
    change t.«prefix».length+(p.map Call.width).sum = (firstPrelude p C E).size+(p.map Call.width).sum
    rw [prefixEq,Block.length_compile]
  have first : t.firstSite p = originalSite p C E := by
    change Site.mk t.«prefix».length (firstReturn (t.afterFirst p)) = Site.mk (firstPrelude p C E).size (firstReturn off)
    rw [prefixEq,Block.length_compile,offset]
  have second : t.secondSite p = jointSite p C E := by
    rw [Template.secondSite,offset]
    change Site.mk (off+(middle endingBlocks off).length) (endingBlocks.secondRet off) =
      Site.mk (endingBlocks.callPC off) (endingBlocks.secondRet off)
    rw [middle_size]
  have site := withFirstCall_locations p C E firstReturn (endingCode p)
  have ends := EndBlocks.placed (bs:=endingBlocks) site.2.2
  obtain ⟨a,b,c,d,e⟩ := positions endingBlocks off
  refine ⟨?_,first.symm,second.symm,site.2.1,ends.callee,?_⟩
  · change program p C E = t.assemble p
    rw [Template.assemble,first,second,prefixEq,offset]
    change (firstPrelude p C E).compile 0 ++ Call.subroutine p (firstPrelude p C E).size (firstReturn off) ++
      endingBlocks.emit p off = (firstPrelude p C E).compile 0 ++
      Call.subroutine p (firstPrelude p C E).size (firstReturn off) ++ middle endingBlocks off ++
      Call.subroutine p (endingBlocks.callPC off) (endingBlocks.secondRet off)
    simp only [middle_emit,List.append_assoc]
  · rw [original_limit]
    change off ≤ endingBlocks.callPC off
    omega

theorem width_positive {p : Program} {C E bC bE : ℕ} (solve : Solver p C E bC bE) :
    0 < (p.map Call.width).sum := by
  cases p with
  | nil =>
    let A : Matrix (Fin 1) (Fin 1) ℚ := 0
    let b : Fin 1 → ℚ := 0
    obtain ⟨k,tr,run,_,_,valid⟩ := solve 1 1 (by decide) (by decide) A b
    obtain ⟨tag,h⟩ : ∃ tag,(tr (Fin.last k)).output = some tag := valid.elim (fun x => ⟨0,x.1⟩) (fun x => ⟨1,x.1⟩)
    cases k with
    | zero => have initial : tr (Fin.last 0) = start [1,1] (lpInput A b) := run.1; rw [initial] at h; cases h
    | succ k =>
      have edge := run.2 0
      have initial : tr ((0 : Fin (k+1)).castSucc) = start [1,1] (lpInput A b) := run.1
      rw [initial] at edge
      simp [RAM.step,start] at edge
  | cons op tail =>
    have pos : 0 < Call.width op := by cases op <;> simp [Call.width]
    simp only [List.map_cons,List.sum_cons]
    omega

theorem erased_itinerary {m d : ℕ} (p : Program) (C E : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (c : Fin d → ℚ) (a : Answer) :
    (itinerary p C E A b c a).map erase = plan A b c (originalSite p C E) (jointSite p C E) a.tag := by
  cases a <;> rfl

/-- Ordinary prefix, preparation and terminal bytes are disjoint from both
registered guest images. A taken guest always returns outside its own entry. -/
theorem separated_itinerary {m d : ℕ} (p : Program) (C E : ℕ) (positive : 0 < (p.map Call.width).sum)
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (answer : Answer) :
    ∀ op ∈ itinerary p C E A b c answer, Separated p (originalSite p C E) (jointSite p C E) op := by
  let f := originalSite p C E
  let s := jointSite p C E
  let off := firstReturnBase p C E
  have limit : f.limit p = off := original_limit p C E
  have firstRoom : f.entry < off := by
    change (firstPrelude p C E).size < (firstPrelude p C E).size+(p.map Call.width).sum
    omega
  have loc : s.entry = endingBlocks.callPC off := rfl
  obtain ⟨o,r,g,pr,ca⟩ := positions endingBlocks off
  have e0 : off+firstCertificate.size+1 = endingBlocks.optPC off := Nat.add_assoc ..
  have e1 : endingBlocks.optPC off+secondOptimum.size+1 = endingBlocks.rayPC off := Nat.add_assoc ..
  have e2 : endingBlocks.rayPC off+secondRay.size+1 = endingBlocks.stagePC off := Nat.add_assoc ..
  have e3 : endingBlocks.stagePC off+stageJoint.size = endingBlocks.prepPC off := rfl
  have e4 : endingBlocks.prepPC off+prepareCallInputs.size = endingBlocks.callPC off := rfl
  have late {low high : ℕ} (l : off ≤ low) (h : high ≤ s.entry) :
      ∀ q,low ≤ q → q < high → ¬ f.Inside p q ∧ ¬ s.Inside p q := by
    intro q ql qh
    constructor
    · intro inside
      have top : q < off := by simpa only [limit] using inside.2
      exact (not_lt_of_ge (l.trans ql)) top
    · intro inside
      exact (not_lt_of_ge inside.1) (qh.trans_le h)
  have prepEnd : endingBlocks.prepPC off ≤ s.entry := by simpa only [loc] using ca
  have stageEnd : endingBlocks.stagePC off ≤ s.entry := pr.trans prepEnd
  have rayBefore : endingBlocks.rayPC off < s.entry := g.trans_le stageEnd
  have optBefore : endingBlocks.optPC off < s.entry := r.trans rayBefore
  have offBefore : off < s.entry := o.trans optBefore
  have offStage : off ≤ endingBlocks.stagePC off := ((o.trans r).trans g).le
  have firstOK (tag : ℕ) : ∀ op ∈ firstParts p C E A b tag, Separated p f s op := by
    intro op mem
    simp only [firstParts,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl
    · intro q _ high
      change q < 0+f.entry at high
      have below : q < f.entry := by simpa only [Nat.zero_add] using high
      exact ⟨fun inside => (not_lt_of_ge inside.1) below,
        fun inside => (not_lt_of_ge inside.1) ((below.trans firstRoom).trans offBefore)⟩
    · change (if tag=0 then endingBlocks.stagePC off else off) ≠ f.entry
      split
      · exact ne_of_gt (firstRoom.trans_le offStage)
      · exact ne_of_gt firstRoom
  have stageOK : Separated p f s (.fixed (endingBlocks.stagePC off) stageJoint) :=
    late (high := endingBlocks.stagePC off+stageJoint.size) offStage (by simpa only [e3] using prepEnd)
  have prepOK : Separated p f s (.fixed (endingBlocks.prepPC off) prepareCallInputs) :=
    late (high := endingBlocks.prepPC off+prepareCallInputs.size) (offStage.trans pr) (le_of_eq (e4.trans loc.symm))
  have jointOK (tag : ℕ) : ∀ op ∈ jointParts p C E A b c tag, Separated p f s op := by
    intro op mem
    simp only [jointParts,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact stageOK
    · exact prepOK
    · change (if tag=0 then endingBlocks.optPC off else endingBlocks.rayPC off) ≠ s.entry
      split
      · exact ne_of_lt optBefore
      · exact ne_of_lt rayBefore
  have certOK : Separated p f s (.terminal off firstCertificate 0) :=
    late (high := off+firstCertificate.size+1) (le_refl off) (by simpa only [e0] using optBefore.le)
  have optOK : Separated p f s (.terminal (endingBlocks.optPC off) secondOptimum 1) :=
    late (high := endingBlocks.optPC off+secondOptimum.size+1) o.le (by simpa only [e1] using rayBefore.le)
  have rayOK : Separated p f s (.terminal (endingBlocks.rayPC off) secondRay 2) :=
    late (high := endingBlocks.rayPC off+secondRay.size+1) (o.trans r).le (by simpa only [e2] using stageEnd)
  have single {a : Part} (ok : Separated p f s a) : ∀ q ∈ [a], Separated p f s q := by
    intro q mem
    obtain rfl := List.mem_singleton.mp mem
    exact ok
  have join {xs ys : List Part} (x : ∀ q ∈ xs, Separated p f s q) (y : ∀ q ∈ ys, Separated p f s q) :
      ∀ q ∈ xs++ys, Separated p f s q := fun q mem => (List.mem_append.mp mem).elim (x q) (y q)
  cases answer with
  | certificate => exact join (firstOK 1) (single certOK)
  | optimum => exact join (firstOK 0) (join (jointOK 0) (single optOK))
  | ray => exact join (firstOK 0) (join (jointOK 1) (single rayOK))

end SubroutineCalls
end PrimalDual
end LinearProgramming
end Optimization
end OAI
