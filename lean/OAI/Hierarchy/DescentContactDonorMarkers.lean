import OAI.Hierarchy.DescentContactDonorFront
import OAI.Hierarchy.DescentContactPreROM

namespace OAI
/-! # Both contact phases read and advance a single physical memory -/
namespace Hierarchy.DescentContactDonorFront.Shape
open DescentPackedZip DescentPackedColony DescentSIMDLookup DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (A : Shape) (base seats bits : ℕ) {k w : ℕ}
variable (u : DescentContactSenderDate.Prior A.degree A.lows A.cap A.n A.residual)
local notation "sender" => A.sender base
local notation "N" => DescentRotorWindowArchive.count A.degree A.lows A.cap
local notation "H" => A.hosts
local notation "G" => A.groups
local notation "M" => A.batch
local notation "b" => A.fieldBits

def markers : DescentContactPreROM.Layout:=
  ⟨A.endAddress base,H,seats,G,M,A.degree,A.lows,A.cap,A.n,A.residual,A.height,b,bits⟩
def oldBoard (i : Fin N) := u.board (finSumFinEquiv (.inl i))

local notation "C" => A.markers base seats bits
local notation "survey" => A.priorSensor base
variable (board : NonlinearExpanders.Graph A.n k) (room : A.Space base u w)

include room in
theorem markerSpace (end_ : (C).endAddress<2^w) (packed : M*max (b*8) bits≤w/2) :
    (C).Space (A.oldBoard u) survey w where
  extent:=end_
  marker:=packed
  oldRow i:=ProtocolRAMGeneratedWrite.fits_mono _ ((A.ordered base).1.trans
    ((A.ordered base).2.1.trans (A.ordered base).2.2)) (room.sender.board (finSumFinEquiv (.inl i)))
  priorRow:=A.priorSensor_fits base u room

variable (xs : Fin A.hosts→Fin A.groups→Fin (DescentOldContactSender.count A.degree A.lows A.cap A.n A.residual)→Cell A.fieldBits)
    (prev : Fin A.hosts→Fin A.degree→Option (Fin A.hosts))
    (raw : Fin A.lows→Fin (2*A.cap)→Fin A.hosts→Fin A.groups→Cell A.fieldBits)

def boardValues (h : Fin H) (g : Fin G) (i : Fin N) := xs h g (finSumFinEquiv (.inl i))
local notation "S₀" => A.memory base u
local notation "marks" => A.sensorValue base xs prev raw
variable (end_ : (A.markers base seats bits).endAddress<2^w) (packed : A.batch*max (A.fieldBits*8) bits≤w/2)
local notation "space" => A.markerSpace base seats bits u room end_ packed

def period := (A.program base u w).seq ((C).program board (A.oldBoard u) survey space)
def result (m : Memory w) := (C).memory board (A.oldBoard u) survey space (S₀ m)
def clock := A.ticks base u+(C).ticks board (A.oldBoard u) survey space

theorem period_any (m : Memory w) :
    (A.period base seats bits u board room end_ packed).Exec m (A.result base seats bits u board room end_ packed m)
      (A.clock base seats bits u board room end_ packed) ∧ CheapCode (A.period base seats bits u board room end_ packed) ∧
    ∀addr,addr<base ∨ (C).endAddress≤addr→A.result base seats bits u board room end_ packed m addr=m addr := by
  have first:=A.any base u room m
  have second:=(C).any board (A.oldBoard u) survey space (S₀ m)
  have start : base≤(C).first:=(A.ordered base).1.trans ((A.ordered base).2.1.trans (A.ordered base).2.2)
  obtain ⟨a,b',c,d,e⟩:=(C).ordered
  have last : (C).first≤(C).endAddress:=a.trans (b'.trans (c.trans (d.trans e)))
  exact ⟨Procedure.Exec.then first.1 second.1,cheap_seq first.2.1 second.2.1,fun addr outside=>
    (second.2.2 addr (outside.imp (fun h=>h.trans_le start) id)).trans
      (first.2.2 addr (outside.imp id (fun h=>last.trans h)))⟩

theorem period_sources (m : Memory w) (previous : (sender).Before u xs prev raw m) (jobs : (sender).Packed w)
    (big : M*max (b*N) (C).viewBits≤w/2) :
    ∀j,Source (.lookup ((C).output j.val) .row)
      (fun h g=>(C).marker board (finProdFinEquiv.symm j).1
        ((C).values (A.boardValues xs) marks j h g)) M (A.result base seats bits u board room end_ packed m) := by
  have held:=A.sources base u room xs prev raw m jobs previous
  have before (addr : ℕ) (low : addr<base) : S₀ m addr=m addr:=(A.any base u room m).2.2 _ (.inl low)
  have old (i : Fin N) : Source (A.oldBoard u i) (fun h g=>A.boardValues xs h g i) M (S₀ m):=fun j=>
    (eval_below _ _ m (S₀ m) (room.sender.board _) before).trans (previous.input _ j)
  exact (C).sources board (A.oldBoard u) survey space (S₀ m) jobs.positive big (A.boardValues xs) marks old held

end
end Hierarchy.DescentContactDonorFront.Shape

end OAI
