import OAI.Hierarchy.DescentVenueShape
import OAI.Hierarchy.DescentOverlapRAM
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentResetStemProjectExprGather
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # Changing the lane width of a predecessor's evaluated packed columns -/
namespace Hierarchy.DescentVenueSlabs.ExprInputs
open DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM DescentSixParty.Chronology
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (s : Shape) (src : Fin s.pages→Expr)
local notation "N₀" => s.hosts*chunks s.groups s.sourceLanes
local notation "N₁" => s.hosts*chunks s.groups s.targetLanes
local notation "V" => s.pages*s.hosts

def passes (base : ℕ) := DescentResetStemProjectExpr.passes src s.hosts s.groups s.sourceLanes base
def program (base w : ℕ) := (ProtocolRAM.program w (passes s src base)).seq
  (Overlap.program (work s base) V s.groups s.sourceLanes s.targetLanes s.bits w (gathered s base))
def ticks (base : ℕ) := clock (passes s src base)+
  Overlap.ticks (work s base) V s.groups s.sourceLanes s.targetLanes s.bits (gathered s base)
def image (base : ℕ) (m : Memory w) := Overlap.result (work s base) V s.groups s.sourceLanes s.targetLanes
  s.bits (gathered s base) (result (passes s src base) m)

theorem cheap (base w : ℕ) : CheapCode (program s src base w) :=by
  apply cheap_seq
  · exact @ProtocolRAM.program_cheap w (passes s src base)
  · apply cheap_seq
    · apply cheap_seq <;> apply DescentOrdinaryAtomFieldRAM.ROM.cheap
    · apply scan_cheap

def phase (base w : ℕ) : NativePhase w :=
  ⟨program s src base w,ticks s src base,image s src base,@cheap s src base w⟩

private theorem space (base w : ℕ) (room : endAddress s base<2^w) :
    (gathered s base).Fits w (work s base) ∧ s.pages*N₀ ≤ (gathered s base).size ∧
    base+s.pages*N₀≤ work s base ∧
    work s base≤Overlap.finish (work s base) V s.groups s.sourceLanes s.targetLanes s.bits ∧
    Overlap.finish (work s base) V s.groups s.sourceLanes s.targetLanes s.bits≤ endAddress s base :=by
  have cap : s.pages*N₀ ≤ span (s.pages*N₀):=Nat.le_pow_clog (by decide) _
  have endRoom : Overlap.endAddress (work s base) V s.groups s.sourceLanes s.targetLanes s.bits<2^w:=
    (Nat.le_add_right ..).trans_lt room
  have fit:=Overlap.output_fits (work s base) V s.groups s.sourceLanes s.targetLanes s.bits w endRoom
  have before : work s base≤Overlap.finish (work s base) V s.groups s.sourceLanes s.targetLanes s.bits:=by
    unfold Overlap.finish Overlap.dest Overlap.dictBase;omega
  have past : Overlap.finish (work s base) V s.groups s.sourceLanes s.targetLanes s.bits≤ endAddress s base:=
    fit.2.2.trans (Nat.le_add_right ..)
  have early : work s base<2^w:=before.trans_lt (past.trans_lt room)
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt early,le_rfl⟩,
    cap,Nat.add_le_add_left cap _,before,past⟩

/-- The physical CPU and its write interval apply to every initial tape. -/
theorem any (base : ℕ) (m : Memory w) (fit : ∀j,(src j).Fits w base) (room : endAddress s base<2^w) :
    (phase s src base w).Runs m ∧
      ∀a,a< base ∨ endAddress s base≤ a→image s src base m a=m a :=by
  obtain ⟨bank,_,copied,up,stop⟩:=space s base w room
  let scan:=passes s src base
  let mid:=result scan m
  let es:=List.ofFn src
  have length_ : es.length=s.pages:=List.length_ofFn
  have ready : ∀e∈es,e.Fits w base:=by
    intro e h
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h
    exact fit j
  have gatheredRun : (ProtocolRAM.program w scan).Exec m mid (clock scan):=
    ProbeStage.Native.columns_exec es m (ProbeStage.Native.columns_safe es (le_refl base) ready
      (by simpa only [length_] using (copied.trans (up.trans stop)).trans_lt room))
  obtain ⟨done,frame,_⟩:=Overlap.any (work s base) V s.groups s.sourceLanes s.targetLanes s.bits
    (gathered s base) mid bank (stop.trans_lt room)
  refine ⟨?_,?_⟩
  · intro pcN regN pubN machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then gatheredRun done machine pc regs pubs exit rom advice cfg memory enter same
  · rintro a (lo|hi)
    · exact (frame _ (.inl (lo.trans_le (Nat.le_add_right ..)))).trans
        (ProbeStage.Native.columns_frame (n:=N₀) es m (.inl lo))
    · have high:=copied.trans (up.trans (stop.trans hi))
      exact (frame _ (.inr (stop.trans hi))).trans
        (ProbeStage.Native.columns_frame es m (.inr (by simpa only [length_] using high)))

/-- The physical output pages use the original actor and group ordinals at the new lane width. -/
theorem issued (base : ℕ) (m : Memory w) (x : Fin s.pages→Fin s.hosts→Fin s.groups→Cell s.bits)
    (fit : ∀j,(src j).Fits w base) (read : ∀j,Source (src j) (x j) s.sourceLanes m)
    (old : 0< s.sourceLanes) (room : endAddress s base<2^w) :
    (phase s src base w).Runs m ∧
      (∀j,Reads (page s base j.val) (x j) s.targetLanes (image s src base m)) ∧
      ∀a,a< base ∨ endAddress s base≤ a→image s src base m a=m a :=by
  obtain ⟨cpu,frame⟩:=any s src base m fit room
  obtain ⟨bank,capacity,copied,up,stop⟩:=space s base w room
  obtain ⟨_,values,_⟩:=DescentResetStemProjectExpr.gather_run base src x m fit read
    ((copied.trans (up.trans stop)).trans_lt room)
  refine ⟨cpu,?_,frame⟩
  rintro j ⟨v,r⟩
  have value:=Overlap.read (work s base) (gathered s base) (result (passes s src base) m)
    (DescentResetStemProject.together x) old bank (by simpa only [Overlap.rows,Nat.mul_assoc] using capacity)
    values (stop.trans_lt room) (finProdFinEquiv (j,v),r)
  have placement:=DescentResetStemProject.combine_row j ((v,r) : Row s.hosts s.groups s.targetLanes)
  simpa only [image,page,Overlap.outputBank,placement,←Nat.add_assoc,data,
    DescentResetStemProject.together,Equiv.symm_apply_apply] using value

end
end Hierarchy.DescentVenueSlabs.ExprInputs

end OAI
