import OAI.Hierarchy.DescentVenueSlabs
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! Execution and memory bounds for rectangular banks of packed rows. -/
open ThreeFlat.RAM.PhysicalProcedure
namespace Hierarchy.DescentVenueSlabs
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProbeStage.Native
open DescentSixParty.Chronology
noncomputable section
variable (s:Shape) (pages:Fin s.pages→Bank)
local notation "n₀"=>s.hosts*chunks s.groups s.sourceLanes
local notation "n₁"=>s.hosts*chunks s.groups s.targetLanes
local notation "V"=>s.pages*s.hosts

theorem cheap (base w:ℕ):CheapCode (program s pages base w) :=by
  apply cheap_seq
  · exact @ProtocolRAM.program_cheap _ _
  · apply cheap_seq
    · apply cheap_seq <;> apply DescentOrdinaryAtomFieldRAM.ROM.cheap
    · apply scan_cheap

variable {w : ℕ}

theorem any (base:ℕ) (m:Memory w) (source:∀j,(pages j).Fits w base) (room:endAddress s base<2^w):
    (program s pages base w).Exec m (image s pages base m) (ticks s pages base) ∧
    ∀z,z<base ∨ endAddress s base≤z→image s pages base m z=m z :=by
  let es:=exprs s pages
  let ps:=passes s pages base
  have size_:es.length=s.pages:=by simp [es,exprs]
  have mean:s.pages*n₀ ≤ span (s.pages*n₀):=Nat.le_pow_clog (by decide) _
  have start:work s base≤Overlap.endAddress (work s base) V s.groups s.sourceLanes s.targetLanes s.bits:=by
    simp only [Overlap.endAddress,Overlap.dest,Overlap.dictBase,Nat.add_assoc]
    exact Nat.le_add_right ..
  have endSpace:Overlap.endAddress (work s base) V s.groups s.sourceLanes s.targetLanes s.bits<2^w:=
    (Nat.le_add_right ..).trans_lt room
  have fit:(gathered s base).Fits w (work s base):=⟨Nat.two_pow_pos _,
    (Nat.le_add_left ..).trans_lt (start.trans_lt endSpace),le_rfl⟩
  have pass: (ProtocolRAM.program w ps).Exec m (ProtocolRAM.result ps m) (ProtocolRAM.clock ps):=by
    apply program_exec
    apply columns_safe (src:=base) es le_rfl
    · intro e he;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he;exact ⟨source j,True.intro⟩
    · rw [size_];exact (Nat.add_le_add_left mean _).trans_lt (start.trans_lt endSpace)
  have finalBound:=(Overlap.output_fits (work s base) V s.groups s.sourceLanes s.targetLanes s.bits w endSpace).2.2
  obtain ⟨final,keep,_⟩:=Overlap.any (work s base) V s.groups s.sourceLanes s.targetLanes s.bits
    (gathered s base) (ProtocolRAM.result ps m) fit (finalBound.trans_lt endSpace)
  refine ⟨by
    intro P R K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then pass final machine pc regs pubs exit rom advice cfg memory enter same,?_⟩
  rintro z (lt|hi)
  · exact (keep z (.inl (lt.trans_le (Nat.le_add_right ..)))).trans (columns_frame es m (.inl lt))
  · have past:Overlap.endAddress (work s base) V s.groups s.sourceLanes s.targetLanes s.bits≤z:=(Nat.le_add_right ..).trans hi
    have copied:base+es.length*n₀≤z:=by rw [size_];exact (Nat.add_le_add_left mean _).trans (start.trans past)
    exact (keep z (.inr (finalBound.trans past))).trans (columns_frame es m (.inr copied))

theorem output_room (base:ℕ) (space:endAddress s base<2^w) (j:Fin s.pages) :
    (page s base j.val).Fits w (endAddress s base) ∧ n₁≤(page s base j.val).size:=by
  have endSpace:Overlap.endAddress (work s base) V s.groups s.sourceLanes s.targetLanes s.bits<2^w:=
    (Nat.le_add_right ..).trans_lt space
  have limit:=(Overlap.output_fits (work s base) V s.groups s.sourceLanes s.targetLanes s.bits w endSpace).2.2
  have loc:j.val*n₁≤Overlap.rows V s.groups s.targetLanes:=by
    simpa [Overlap.rows,Nat.mul_assoc] using Nat.mul_le_mul_right n₁ j.isLt.le
  have before: (page s base j.val).base≤Overlap.endAddress (work s base) V s.groups s.sourceLanes s.targetLanes s.bits:=
    (Nat.add_le_add_left loc _).trans limit
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt space,Nat.add_le_add_right before _⟩,Nat.le_pow_clog (by decide) _⟩

end
end Hierarchy.DescentVenueSlabs

namespace Hierarchy.DescentVenueSlabs
open DescentSIMDLookup ProtocolRAM
theorem page_room (s:Shape)(base w:ℕ)(j:Fin s.pages)(fit:endAddress s base<2^w):
    (page s base j.val).Fits w (endAddress s base) ∧
    s.hosts*chunks s.groups s.targetLanes≤(page s base j.val).size:=by
  exact output_room s base fit j
end Hierarchy.DescentVenueSlabs

end OAI
