import OAI.Hierarchy.DescentVenueShape
import OAI.Hierarchy.DescentActorRechunk
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Moving the actual signed or paid columns to the lane width of the following date -/
open ThreeFlat.RAM.PhysicalProcedure
namespace Hierarchy.DescentVenueSlabs
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentActorRaster ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

variable (s : Shape)
local notation "n₀" => s.hosts*chunks s.groups s.sourceLanes
local notation "n₁" => s.hosts*chunks s.groups s.targetLanes
local notation "Q" => s.pages
local notation "V" => s.pages*s.hosts
variable (pages : Fin s.pages→Bank)
def exprs :=List.ofFn (fun j:Fin s.pages=>Expr.lookup (pages j) Expr.row)
def passes (base:ℕ):=ProbeStage.Native.columns n₀ base (exprs s pages)
def program (base w:ℕ):=(ProtocolRAM.program w (passes s pages base)).seq
  (Overlap.program (work s base) V s.groups s.sourceLanes s.targetLanes s.bits w (gathered s base))
def ticks (base:ℕ):=ProtocolRAM.clock (passes s pages base)+
  Overlap.ticks (work s base) V s.groups s.sourceLanes s.targetLanes s.bits (gathered s base)

variable {w : ℕ}

def image (base:ℕ) (m:Memory w):=Overlap.result (work s base) V s.groups s.sourceLanes s.targetLanes s.bits
  (gathered s base) (ProtocolRAM.result (passes s pages base) m)

theorem run (base:ℕ) (m:Memory w) (x:Fin s.pages→Fin s.hosts→Fin s.groups→Cell s.bits)
    (source : ∀j,(pages j).Fits w base) (extent : ∀j,n₀≤(pages j).size)
    (read : ∀j,Reads (pages j) (x j) s.sourceLanes m) (pos : 0<s.sourceLanes)
    (room : endAddress s base<2^w) :
    let after:=image s pages base m
    (program s pages base w).Exec m after (ticks s pages base) ∧
     (∀j,Reads (page s base j.val) (x j) s.targetLanes after) ∧
     (∀j:Fin Q,(page s base j.val).Fits w (endAddress s base) ∧ n₁≤(page s base j.val).size) ∧
     (∀z,z<base ∨ endAddress s base≤z→after z=m z) ∧ CheapCode (program s pages base w) := by
  let es:=exprs s pages
  let ps:=passes s pages base
  let middle:=ProtocolRAM.result ps m
  have len:es.length=Q:=by simp [es,exprs]
  have copyFit : ∀e∈es,e.Fits w base:=by
    intro e he
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
    exact ⟨source j,True.intro⟩
  have mean : Q*n₀ ≤ span (Q*n₀):=Nat.le_pow_clog (by decide) _
  have endSpace:Overlap.endAddress (work s base) V s.groups s.sourceLanes s.targetLanes s.bits<2^w:=
    (Nat.le_add_right ..).trans_lt room
  have safe:=Overlap.output_fits (work s base) V s.groups s.sourceLanes s.targetLanes s.bits w endSpace
  have upcoming:work s base≤Overlap.endAddress (work s base) V s.groups s.sourceLanes s.targetLanes s.bits:=by
    simp only [Overlap.endAddress,Overlap.dest,Overlap.dictBase,Nat.add_assoc]
    exact Nat.le_add_right ..
  have nextSpace : work s base<2^w:=upcoming.trans_lt endSpace
  have native: (ProtocolRAM.program w ps).Exec m middle (ProtocolRAM.clock ps):=by
    apply program_exec
    apply columns_safe (src:=base) _ le_rfl copyFit
    rw [len];exact (Nat.add_le_add_left mean _).trans_lt nextSpace
  have contiguous (j:Fin Q) (p:Row s.hosts s.groups s.sourceLanes):
      middle ((gathered s base).base+j.val*n₀+(row _ _ _ p).val)=((data (x j) p).val:Word w):=by
    have seen:=columns_read es m (src:=base) (base:=base) le_rfl copyFit j.val (len.symm ▸ j.isLt) (row _ _ _ p)
    have selected : es[j.val]'(len.symm ▸ j.isLt)=Expr.lookup (pages j) .row:=by simp [es,exprs]
    rw [selected] at seen
    exact seen.trans ((bank_read _ m ((row s.hosts s.groups s.sourceLanes p).isLt.trans_le (extent j)) (source j)).trans (read j p))
  have gatherFit:(gathered s base).Fits w (work s base):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt nextSpace,le_rfl⟩
  obtain ⟨ran,out,hold,cheap⟩:=change_pitch x (work s base) (gathered s base) middle pos gatherFit
    (by simpa only [Nat.mul_assoc,gathered,Bank.size,span] using mean) (safe.2.2.trans_lt endSpace) contiguous
  refine ⟨by
    intro P R K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then native ran machine pc regs pubs exit rom advice cfg memory enter same,fun j p=>out j p,?_,?_,cheap_seq (ProtocolRAM.program_cheap w ps) cheap⟩
  · intro j
    have atEnd : j.val*n₁≤Overlap.rows V s.groups s.targetLanes:=by
      simpa [Overlap.rows,Nat.mul_assoc] using Nat.mul_le_mul_right n₁ j.isLt.le
    have bottom : (page s base j.val).base≤Overlap.endAddress (work s base) V s.groups s.sourceLanes s.targetLanes s.bits:=
      (Nat.add_le_add_left atEnd _).trans safe.2.2
    exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt room,Nat.add_le_add_right bottom _⟩,Nat.le_pow_clog (by decide) _⟩
  · rintro z (lo|hi)
    · exact (hold _ (.inl (lo.trans_le (Nat.le_add_right ..)))).trans (columns_frame es m (.inl lo))
    · have past:=((Nat.le_add_right ..).trans hi)
      have copied:base+es.length*n₀≤z:=by rw [len];exact (Nat.add_le_add_left mean _).trans (upcoming.trans past)
      exact (hold _ (.inr (safe.2.2.trans past))).trans (columns_frame es m (.inr copied))

end
end Hierarchy.DescentVenueSlabs

end OAI
