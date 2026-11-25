import OAI.Computability.BorderVNP.DiagonalTallyAllocationRate
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedCube

/-! # Installing and consuming the concrete report and lookup pointer fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyAllocation

open VPVNP.BurstRAM RoutingISA DiagonalTallyCellReports

/-- The genuine owned-cell scanner layout for the two scratch partitions. -/
def reportLayout (pre : BeforeTasks) (post : AfterTasks) (frame control h H body zeroAddr : ℕ) : ReportLayout :=
  ⟨frame,control,pre.six,pre.bundleTable,h,post.bound.gadgets,post.bound.countWidth,H,body,zeroAddr,
    pre.tailWidths,pre.supplement,pre.bound.supplementStride,pre.counters⟩

/-- The initial scan always writes to the first free words of the three reserved report banks. -/
def AfterTasks.reportCursor (a : AfterTasks) : ReportCursor := ⟨a.packed,a.descriptors,a.refs,0⟩

/-- The report program reads exactly the concrete control values installed from length-only
parameters and the genuine owned count emitted by the independent header scan. -/
theorem report_seed (pre : BeforeTasks) (post : AfterTasks) (frame control h H body zeroAddr owned : ℕ)
    (m previous : ℕ → ℕ)
    (p92 : m (frame+92)=control) (p90 : m (frame+90)=owned) (p95 : m (frame+95)=h)
    (p81 : m (frame+81)=zeroAddr) (p44 : m (frame+44)=post.frameFields previous 44)
    (ctl : ∀ i < 28, m (control+i)=post.controls H body (pre.controls previous) i) :
    (reportLayout pre post frame control h H body zeroAddr).seed post.reportCursor owned m :=
  ⟨p92,p90,p95,p81,p44,ctl 17 (by decide),ctl 19 (by decide),ctl 22 (by decide),
    ctl 23 (by decide),ctl 24 (by decide),ctl 25 (by decide),ctl 26 (by decide),ctl 27 (by decide)⟩

/-- Reconstruct the concrete lookup frame from the initialized dynamic pointers and the
earlier producer's true owned count and triples base. The static finite tables and literal
words have the same addresses across all processor inputs. -/
theorem AfterTasks.packet_resident (a : AfterTasks) (pub : Arg → ℕ) (m previous : ℕ → ℕ)
    (count triples recipes zeroAddr oneAddr vertices : ℕ)
    (p46 : m (pub 0+46)=count) (p78 : m (pub 0+78)=triples) (p79 : m (pub 0+79)=recipes)
    (p80 : m (pub 0+80)=a.frameFields previous 80) (p45 : m (pub 0+45)=a.frameFields previous 45)
    (p81 : m (pub 0+81)=zeroAddr) (p82 : m (pub 0+82)=oneAddr)
    (p83 : m (pub 0+83)=a.bound.cubeWidth) (p84 : m (pub 0+84)=vertices) :
    (a.packetFrame count triples recipes zeroAddr oneAddr vertices).resident pub m :=
  ⟨p46,p78,p79,p80,p45,p81,p82,p83,p84⟩

/-- The right-aligned subtotal start installed in frame 34 is the exact endpoint needed by the
count-dependent native aligner, including counts strictly below the length ceiling. -/
theorem AfterTasks.aligned_seed {w : ℕ} (a : AfterTasks) (pub : Arg → Word w) (m : Memory w)
    (raw dim teams team width count : ℕ) (hc : count ≤ a.bound.operands)
    (p33 : (m ((pub 0).val+33)).val=dim) (p34 : (m ((pub 0).val+34)).val=a.localBase)
    (p35 : (m ((pub 0).val+35)).val=count) (p36 : (m ((pub 0).val+36)).val=raw)
    (p38 : (m ((pub 0).val+38)).val=teams) (p39 : (m ((pub 0).val+39)).val=team)
    (p40 : (m ((pub 0).val+40)).val=width) (p44 : (m ((pub 0).val+44)).val=a.descriptors)
    (p101 : (m ((pub 0).val+101)).val=w) :
    (a.arenaFor count raw dim teams team width).alignedSeed pub m a.descriptors := by
  have bound : 2*count ≤ a.localBase := by unfold localBase; omega
  refine ⟨p33,?_,p35,p36,p38,p39,p40,p44,p101⟩
  change (m ((pub 0).val+34)).val=a.localBase-2*count+2*count
  rwa [Nat.sub_add_cancel bound]

end DiagonalTallyAllocation

end BorderVNP
end Computability
end OAI
