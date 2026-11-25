import OAI.Hierarchy.DescentContactProbeSpace
import OAI.Hierarchy.DescentResetWindowJobs
import OAI.Hierarchy.DescentResetCatalog

namespace OAI
/-! # One dated scan of all public contact markers on the expanded host and shape rectangle -/
namespace Hierarchy.DescentContactPreROM.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentFallbackPeriod.Projected DescentIssuedGoodHeaders
open DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable (A : Layout) {ports w : ℕ} (board : NonlinearExpanders.Graph A.n ports)
local notation "H" => A.hosts*A.shapes
local notation "G" => A.groups
local notation "M" => A.batch
local notation "K" => A.sockets

/-- Five original columns consist of the near/far issued joints, near/far genuine book heights
and the old signed peer port. Both remaining donor fields come from the shared gathered view. -/
def rowFields (prior : Bool→Fin A.half→Fin 5→Expr) (measured : Bool→Fin A.half→Fin 2→Expr)
    (shape : Expr) (j : Fin A.jobs) (i : Fin 8) : Expr :=
  let (q,k):=finProdFinEquiv.symm j
  let (side,donor):=finProdFinEquiv.symm k
  match A.query q with
  | some (s,_,_)=>if finTwoEquiv side=s then
      ![prior s donor 0,prior s donor 1,measured s donor 0,measured s donor 1,
        prior s donor 2,prior s donor 3,prior s donor 4,shape] i
    else .lit 0
  | none=>.lit 0

def markerImage :=DescentContactProbeBook.book (A.law board) H G M A.markerBase w
variable (reads : Fin A.jobs→Fin 8→Expr)
variable (held : ∀j i,(reads j i).Fits w A.markerBase) (room : A.endAddress<2^w)
    (packed : A.batch*max (A.fieldBits*8) A.outputBits≤w/2)

def markerJob (j : Fin A.jobs) : Shelf w :=
  let q:=(finProdFinEquiv.symm j).1
  let t:=A.termPage board q (reads j) j
  let ok:=A.marker_space board q (reads j) j (held j) room packed
  let bounds:=A.block j
  Shelf.window («H» := H) («G» := G) («M» := M) t.tables (reads j) t.menu (A.mid j.val) (A.output j.val).base
    (DescentPacking.PackedMatch.Local.Gather.fits t.tables (reads j) (A.mid j.val) ok.bounds (List.finRange 8))
    ok.lookupFits (bounds.1.trans_lt (((Nat.le_add_right ..).trans (bounds.2.1.trans bounds.2.2)).trans_lt room))
    (bounds.2.1.trans_lt (bounds.2.2.trans_lt room))

def markerPhase := Shelf.series (Shelf.catalog (A.markerJob board reads held room packed))

local notation "phase" => A.markerPhase board reads held room packed
local notation "job" => A.markerJob board reads held room packed

theorem marker_range (j : Fin A.jobs) :
    A.scratchBase+(2*A.slab)*j.val≤(job j).first ∧ (job j).limit≤A.scratchBase+(2*A.slab)*(j.val+1) := by
  change _≤ min (A.mid j.val) (A.output j.val).base ∧ max (A.mid j.val+A.rows) ((A.output j.val).base+A.rows)≤_
  have bounds:=A.block j
  have baseEq : A.scratchBase+(2*A.slab)*j.val=A.mid j.val:=by simp [mid,Nat.mul_comm]
  rw [baseEq,Nat.mul_comm (2*A.slab) (j.val+1)]
  exact ⟨le_min le_rfl (Nat.le_add_right ..),max_le (bounds.1.trans ((Nat.le_add_right ..).trans bounds.2.1)) bounds.2.1⟩

def markerCode :=(A.markerImage (w:=w) board).program.seq (phase).program
def markerResult (m : Memory w) :=(phase).image ((A.markerImage board).output m)
def markerClock :=(4+10*(K*DescentContactProbeBook.step 8 A.fieldBits H G M))+
    ((∑j : Fin A.jobs,(job j).ticks)+4)

theorem marker_any (m : Memory w) :
    (A.markerCode board reads held room packed).Exec m (A.markerResult board reads held room packed m)
      (A.markerClock board reads held room packed) ∧
    CheapCode (A.markerCode board reads held room packed) ∧
    ∀a,a<A.markerBase ∨ A.endAddress≤a→A.markerResult board reads held room packed m a=m a := by
  have cap:=A.ordered.2.2.2.2
  obtain ⟨rom,cheap,_,low⟩:=DescentContactProbeBook.run (A.law board) H G M A.markerBase m (cap.trans_lt room)
  obtain ⟨go,clock,_,keep⟩:=Shelf.issued_catalog job A.scratchBase (2*A.slab)
    (A.marker_range board reads held room packed) ((A.markerImage board).output m)
  refine ⟨?_,cheap_seq cheap (phase).cheap,?_⟩
  · unfold markerClock
    rw [←clock]
    exact rom.then go
  · intro addr away
    rcases away with lo|hi
    · exact (keep addr (.inl (lo.trans_le A.ordered.2.2.2.1))).trans (low addr (.inl lo))
    · have final : A.scratchBase+(2*A.slab)*A.jobs≤addr:=by simpa [endAddress,Nat.mul_comm] using hi
      exact (keep addr (.inr final)).trans (low addr (.inr (cap.trans hi)))

theorem marker_words (m : Memory w) (positive : 0<M)
    (raw : Fin A.jobs→Fin H→Fin G→Fin 8→Cell A.fieldBits)
    (source : ∀j i,Source (reads j i) (fun h g=>raw j h g i) M m) :
    ∀j,Reads (A.output j.val) (fun h g=>A.marker board (finProdFinEquiv.symm j).1 (raw j h g)) M
      (A.markerResult board reads held room packed m) := by
  intro j
  let q:=(finProdFinEquiv.symm j).1
  let t:=A.termPage board q (reads j) j
  let post:=(A.markerImage board).output m
  have cap:=A.ordered.2.2.2.2
  obtain ⟨_,_,printed,low⟩:=DescentContactProbeBook.run (A.law board) H G M A.markerBase m (cap.trans_lt room)
  obtain ⟨constants,rom⟩:=DescentContactProbeBook.fixed (A.law board) H G M A.markerBase post printed
    (cap.trans_lt room) q (reads j) ⟨A.mid j.val,Nat.clog 2 A.rows⟩
  have src (i : Fin 8) : Source (reads j i) (fun h g=>raw j h g i) M post:=fun r=>
    (eval_below _ _ m post (held j i) (fun a before=>low a (.inl before))).trans (source j i r)
  have ok:=A.marker_space board q (reads j) j (held j) room packed
  have limits:=A.block j
  have lower : A.mid j.val+A.rows<2^w:=limits.1.trans_lt (((Nat.le_add_right ..).trans (limits.2.1.trans limits.2.2)).trans_lt room)
  have actual:=gathered_words (A.marker board q) t.tables (reads j) t.menu (A.mid j.val)
    (A.output j.val).base (raw j) positive post ok.bounds constants src lower ok.fit rom ok.dictLow ok.maskLow ok.wire
  obtain ⟨_,_,all,_⟩:=Shelf.issued_catalog job A.scratchBase (2*A.slab)
    (A.marker_range board reads held room packed) post
  intro rowId
  let x:=(A.output j.val).base+(row H G M rowId).val
  have k : (job j).first≤x:=(min_le_right _ _).trans (Nat.le_add_right ..)
  have l : x<(job j).limit:=(Nat.add_lt_add_left (row H G M rowId).isLt _).trans_le (le_max_right _ _)
  exact (all j x k l).trans (actual.2.1 rowId)

theorem output_fits (j : Fin A.jobs) (room : A.endAddress<2^w) : (A.output j.val).Fits w A.endAddress := by
  have stop : (A.output j.val).base+A.slab≤A.endAddress:=by
    change A.scratchBase+j.val*(2*A.slab)+A.slab+A.slab≤_
    have last:=(A.block j).2.2
    rw [Nat.succ_mul] at last
    omega
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (stop.trans_lt room),stop⟩

theorem marker_sources (m : Memory w) (positive : 0<M)
    (raw : Fin A.jobs→Fin H→Fin G→Fin 8→Cell A.fieldBits)
    (source : ∀j i,Source (reads j i) (fun h g=>raw j h g i) M m) :
    ∀j,Source (.lookup (A.output j.val) .row)
      (fun h g=>A.marker board (finProdFinEquiv.symm j).1 (raw j h g)) M
      (A.markerResult board reads held room packed m) :=
  fun j=>source_column _ _ (A.output_fits j room) _ _ (Nat.le_pow_clog (by decide) _) <|
    A.marker_words board reads held room packed m positive raw source j

end
end Hierarchy.DescentContactPreROM.Layout

end OAI
