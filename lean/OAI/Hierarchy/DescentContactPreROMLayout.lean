import OAI.Hierarchy.DescentContactProbeBook
import OAI.Hierarchy.DescentContactProbePitch
import OAI.Hierarchy.DescentContactProbeRead
import OAI.Hierarchy.DescentReservedProbeInputs
import OAI.Hierarchy.DescentResetCandidateDate

namespace OAI
/-! # Physical address range of the raw public-contact marker before the peer ROM -/
namespace Hierarchy.DescentContactPreROM
open DescentSIMDLookup DescentPackedColony DescentSharedCableNames DescentResetLocalRoster DescentReservedProbeInputs
open DescentPackedFallbackTree.Image DescentPacking.PackedMatch.Local.Gather DescentRotorWindowArchive
open DescentResetCandidateDate ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  first : ℕ
  hosts : ℕ
  shapes : ℕ
  groups : ℕ
  batch : ℕ
  degree : ℕ
  lows : ℕ
  cap : ℕ
  n : ℕ
  residual : ℕ
  height : ℕ
  fieldBits : ℕ
  outputBits : ℕ

namespace Layout
variable (A : Layout)
def half:=A.lows*(2*A.cap)
def sockets:=2*(rootSlots A.residual (2^A.n)*(2^A.n+2^A.height))
def donors:=2*A.half
def jobs:=A.sockets*A.donors
def oldFields:=count A.degree A.lows A.cap
def viewCount:=2*(A.half*2)
def viewBits:=A.fieldBits*A.viewCount
def old : DescentResetCandidateDate.Shape:=⟨A.first,1,A.batch,A.hosts,A.groups⟩
def viewBank:=A.old.output A.oldFields A.fieldBits 0
def projectionBase:=A.old.endAddress A.oldFields A.fieldBits
def pitchBase:=DescentContactProbeBook.stop A.viewCount 1 A.viewBits A.hosts A.groups A.batch A.projectionBase
def markerBase:=A.pitchBase+DescentContactProbePitch.extent A.hosts A.shapes A.groups A.batch
def scratchBase:=DescentContactProbeBook.stop A.sockets 8 A.fieldBits (A.hosts*A.shapes) A.groups A.batch A.markerBase
def rows:=(A.hosts*A.shapes)*chunks A.groups A.batch
def slab:=2^(Nat.clog 2 A.rows)
def mid (j : ℕ):=A.scratchBase+j*(2*A.slab)
def output (j : ℕ) : Bank:=⟨A.mid j+A.slab,Nat.clog 2 A.rows⟩
def endAddress:=A.scratchBase+A.jobs*(2*A.slab)

def oldValue (raw : Fin A.oldFields→Cell A.fieldBits) : Cell A.viewBits :=
  encode A.fieldBits A.viewCount (fun j=>
    let ij:=finProdFinEquiv.symm j
    let sf:=finProdFinEquiv.symm ij.2
    value A.n A.residual (finTwoEquiv ij.1) (D:=A.degree) (L:=A.lows) (cap:=A.cap) (fun k=>raw (ix k))
      (finProdFinEquiv.symm sf.1) sf.2)

def view (side : Bool) (lo : Fin A.half) (field : Fin 2) : Fin A.viewCount :=
  finProdFinEquiv (finTwoEquiv.symm side,finProdFinEquiv (lo,field))

theorem old_value_read (raw : Fin A.oldFields→Cell A.fieldBits) (side : Bool) (j : Fin A.half) (f : Fin 2) :
    (encode A.fieldBits A.viewCount).symm (A.oldValue raw) (A.view side j f)=
    value A.n A.residual side (D:=A.degree) (L:=A.lows) (cap:=A.cap) (fun k=>raw (ix k)) (finProdFinEquiv.symm j) f:=by
  simp only [oldValue,view,Equiv.symm_apply_apply,Equiv.apply_symm_apply]

def projectionLaw (j : Fin A.viewCount) (v : Cell (A.viewBits*1)) : Cell A.fieldBits :=
  (encode A.fieldBits A.viewCount).symm ((encode A.viewBits 1).symm v 0) j

/-- A projection takes a single whole view as an input to the dictionary, so its 1-field
encoding uses the canonical width cast. -/
theorem projection_encoded (j : Fin A.viewCount) (v : Cell A.viewBits) :
    A.projectionLaw j (encode A.viewBits 1 (fun _=>v))=(encode A.fieldBits A.viewCount).symm v j:=by
  simp [projectionLaw]

def query (q : Fin A.sockets) : Option (Bool×Root A.residual (2^A.n)×Fin (2^A.n+2^A.height)) :=
  if hit : ∃p,localPrivateId A.residual (2^A.n) (2^A.n+2^A.height) p=q then some hit.choose else none

def index (query : Fin A.sockets) (donor : Fin A.donors) : Fin A.jobs :=finProdFinEquiv (query,donor)

def marker {ports : ℕ} (board : NonlinearExpanders.Graph A.n ports) (q : Fin A.sockets)
    (x : Fin 8→Cell A.fieldBits) : Cell A.outputBits :=
  match A.query q with
  | none=>0
  | some (side,root,z)=>DescentReservedPeerMarker.mark board A.residual A.height side root z
      (x 7).val (x 0).val (x 1).val (x 2).val (x 3).val (x 4).val (x 5).val (x 6).val

def law {ports : ℕ} (board : NonlinearExpanders.Graph A.n ports) (q : Fin A.sockets) :=
  A.marker board q ∘ (encode A.fieldBits 8).symm

def termPage {ports : ℕ} (board : NonlinearExpanders.Graph A.n ports) (q : Fin A.sockets)
    (reads : Fin 8→Expr) (j : Fin A.jobs) :=
  (DescentContactProbeBook.page (A.law board) q reads).terms
    (DescentContactProbeBook.pageBase 8 A.fieldBits (A.hosts*A.shapes) A.groups A.batch A.markerBase q)
    (A.hosts*A.shapes) A.groups A.batch ⟨A.mid j.val,Nat.clog 2 A.rows⟩

theorem ordered : A.first≤A.projectionBase ∧ A.projectionBase≤A.pitchBase ∧ A.pitchBase≤A.markerBase ∧
    A.markerBase≤A.scratchBase ∧ A.scratchBase≤A.endAddress := by
  have raw:=A.old.ordered A.oldFields A.fieldBits
  exact ⟨raw.1.trans ((Nat.le_add_right ..).trans (raw.2.1.trans raw.2.2)),Nat.le_add_right ..,
    Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩

theorem block (j : Fin A.jobs) : A.mid j.val+A.rows≤(A.output j.val).base ∧
    (A.output j.val).base+A.rows≤A.scratchBase+(j.val+1)*(2*A.slab) ∧
    A.scratchBase+(j.val+1)*(2*A.slab)≤A.endAddress := by
  have small : A.rows≤A.slab:=Nat.le_pow_clog (by decide) _
  refine ⟨Nat.add_le_add_left small _,?_,Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) _⟩
  change A.scratchBase+j.val*(2*A.slab)+A.slab+A.rows≤_
  rw [Nat.succ_mul j.val (2*A.slab)]
  omega

end Layout
end
end Hierarchy.DescentContactPreROM

end OAI
