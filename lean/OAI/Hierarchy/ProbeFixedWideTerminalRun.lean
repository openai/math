import OAI.Hierarchy.ProbeFixedWideTerminalSeated
import OAI.Hierarchy.ProtocolRAMTurnRoleRanks

namespace OAI
/-! # Original charges, paid occurrence ranks, and the fixed party's final shelf in one program -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open RouteSettlement CoreRoute HistoryRoles RoleProgram ProtocolRAMTurnChart
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical Fin.CommRing
private theorem rank_limits {work old edges slots firstSpan secondSpan groupCap finalCap rank floor wordRoom : ℕ}
    (rank_eq : rank = work+4*old+4*edges+3*old+firstSpan+secondSpan)
    (floor_eq : floor = rank+groupCap+groupCap+2*(edges+slots)+3*(edges+slots)+4*(edges+slots)+edges+3+finalCap)
    (limit : floor < wordRoom) : old ≤ wordRoom ∧ edges ≤ wordRoom ∧ edges+slots ≤ wordRoom ∧ work ≤ floor := by
  omega

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits rom work : ℕ)
local notation "T" => v.wideTerminal h width bits rom work
local notation "L" => v.wideTurnWindow h width bits work
local notation "board" => v.wideTerminalBoard h width bits work
local notation "D" => 2^v.W
local notation "P" => v.widePlacement h width
local notation "e" => (P).catalogue.rows
local notation "roles" => WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "names" => (ProtocolRAMTurnGeometry.sourceOrder e h D k).symm
local notation "order" => wideRouteOrder h D k
local notation "u" => ProtocolRAMTurnGeometry.header order roles names
local notation "len" => ProtocolRAMTurnGeometry.length ∘ names
local notation "raw" => ProtocolRAMTurnOrder.raw len
local notation "pos" => ProtocolRAMTurnGeometry.sourceOrder e h D k
local notation "port" => Public v.sampler h v.W k v.wideJobs

variable {w:ℕ} {π : Equiv.Perm (Fin (2^h))}
  (B : Mount (S:=v.sampler) π (name (h:=h) (W:=v.W) (k:=k))
    (v.widePlacement h width).catalogue.rows)
  (pad : Chord (siteLast h (2^v.W) k+1))
local notation "inj" => (siteNumber h D k).injective
local notation "visit" => ProtocolRAMVisitAdjacency.vertex len (fun a=>ProtocolRAMTurnEdges.visit B inj pad (names a))
local notation "edge" => ProtocolRAMTurnOccurrence.edgeAt B inj pad order
local notation "ends" => ProtocolRAMTurnOccurrence.endsAt B inj pad

local notation "markFor" => Marks h v.W k v.wideJobs
local notation "ow" => fun i : Fin (T).edges => pos (.inl i)

local notation "lw" => v.wideWidthLayout h width (v.widePaidSlices h width bits)
local notation "last" => (events v.mesh).length
local notation "paidAtLast" => (lw).bank last
local notation "ledger" => (T).accounts
local notation "matrix" => B.matrixLayout inj pad
local notation "entries" => Fintype.card (Slots h D k)
local notation "native" => (matrix).nativeEdge (CoreRoute.enum B order)
local notation "lo" => v.wideTerminalRankStart h width bits work

theorem wide_terminal_run (mark : markFor) (unique : Exclusive mark) (initial archive m : Memory w) {paidSource : Memory w}
    (ci : Goods h v.W k → ℕ) (cj : Catalysts h v.W k → ℕ)
    (directory : Directory ledger archive (CoreRoute.enum B order) ci cj)
    (receipts : ∀c∈[(ledger).index,(ledger).kind,(ledger).stock,(ledger).reserved,(ledger).used],c.base+c.size≤(lw).archive)
    (retained : ∀x<(lw).archive,m x=archive x)
    (paid : ∀i:Fin e,(m ((paidAtLast).base+i.val)).val=
      PaidWidths.total ((events v.mesh).flatMap (v.wideEventSlices h width bits)) paidSource i)
    (paidBefore : (paidAtLast).base+e≤work)
    (inputs : ∀c∈[paidAtLast,(ledger).index,(ledger).kind,(ledger).stock,(ledger).reserved,(ledger).used],c.Fits w lo)
    (budget : ∀j,actual (ledger).used archive (cj j)≤actual (ledger).reserved archive (cj j))
    {old : Fin (board).old→ℕ} {report : Fin (board).edges→ℕ}
    {before : ∀i,0<old i→Bool→port} {after : ∀i,0<report i→Bool→port}
    (resolved : ((board).extended (T).stock w).Exec m ((board).extendedState (T).stock m) ((board).extendedTime (T).stock) ∧
      (board).LiveReads v.sampler old report before after ((board).extendedState (T).stock m))
    («public» : ∀a,rom≤a→a<v.wideTerminalROMEnd h width bits rom work→
      m a=v.wideTerminalWords h width bits rom work initial a)
    (hro : v.wideTerminalROMEnd h width bits rom work≤work)
    (room : v.wideTerminalWorkEnd h width bits work≤2^w)
    (siteWord : (T).sites≤2^w) (lenWord : ∀a,len a<2^w)
    (first : ∀a (on : 0<old (pos (names a))),
      (name (HistoryRoles.site v.sampler (before (pos (names a)) on false))).val=
        ProtocolRAMTurnEdges.visit B inj pad (names a) 0)
    (used : ∀a,0<old (pos (names a))→∀j<len a,
      let x:=edge (ProtocolRAMTurnGeometry.origin order (names a)+j)
      ∃f:Fin (board).edges,∃on:0<report f,f.val=x ∧
        ProtocolRAMTurnOperands.printed v.sampler true (after f on) false true=(ends x).1 ∧
        ProtocolRAMTurnOperands.printed v.sampler true (after f on) true true=(ends x).2)
    (ident : {i : Fin (T).edges // 0<old (ow i)} ↪ Catalogue v.sampler π v.depth mark)
    (aligned : ∀i : {i : Fin (T).edges // 0<old (ow i)},filledChord B.actual pad i.val=
      HistoryRoles.sorted v.sampler π v.depth mark (.inl (ident i)))
    (paidPorts : ∀i : {i : Fin (T).edges // 0<old (ow i)},∃flip : Bool,∀side,
      before (ow i.val) i.property side=.inl (HistoryRoles.paid v.sampler π v.depth mark unique (ident i,if flip then !side else side))) (archiveRows : Bool := false) :
    let fixed:=fun i : Fin (T).edges=>old (ow i)
    let loads:=(matrix).nativeWidth (CoreRoute.enum B order)
      (fun i=>PaidWidths.total ((events v.mesh).flatMap (v.wideEventSlices h width bits)) paidSource i)
      (fun i=>actual (ledger).stock archive (ci i)) (fun j=>actual (ledger).reserved archive (cj j))
      (fun j=>actual (ledger).used archive (cj j))
    ∃mid : Memory w,
      let cols:=ProtocolRAMTurnInstalled.columns (record u (captured (T).columns mid) visit) (ProtocolRAMTurnSnapshot.values (T).walk mid)
      ∃(kept : ∀j : ProtocolRAMTurnShelf.Live cols, ProtocolRAMLiveTurnOrder.retain fixed
          (ProtocolRAMPaidTurnPlacement.rawItem names j.val).1) (out : Memory w),
      ((T).code w paidAtLast).Exec m out ((T).ticks paidAtLast) ∧
      (∀f:Fin 5,∀s:ProtocolRAMTurnShelf.Seats (T).sites (T).seats,
        out ((T).base+f.val*((T).sites*(T).seats)+s.1.val*(T).seats+s.2.val)=ProtocolRAMTurnShelf.entry cols
          (ProtocolRAMPaidTurnPlacement.chartPut v.sampler π v.depth mark unique B pad fixed ident names cols kept) f s) ∧
      (∀x<work,out x=m x) ∧ (∀x<(L).floor,out x=mid x) ∧
      (board).LiveReads v.sampler old report before after mid ∧
      (∀i : Fin (e+entries), mid (ProtocolRAMTurnReplayed.ranks lo (e+entries) e+4*i.val+3)=
        (TaggedShorterCommonScan.earlier native loads i.val (native i):Word w)) ∧
      (∀i : Fin (e+entries), mid (lo+i.val)=((native i).val:Word w)) ∧
      let masses:=∀i : Fin (e+entries),mid ((ProtocolRAMTurnReplayed.weight lo (e+entries)).base+i.val)=(loads i:Word w)
      if archiveRows then (∀a<lo,mid a=(board).extendedState (T).stock m a) ∧ masses else masses := by
  intro fixed loads
  have start : lo=work+4*(board).old+4*e+3*(board).old+
      ProtocolRAMPurchaseSampler.span (board).old+ProtocolRAMPurchaseSampler.span e := rfl
  have bound : (L).floor=lo+2^ProtocolRAMPackedRanked.groupBits (e+entries)+2^ProtocolRAMPackedRanked.groupBits (e+entries)+
      2*(e+entries)+3*(e+entries)+4*(e+entries)+e+3+2^ProtocolRAMPackedRanked.groupBits (4*(e+entries)) := rfl
  have stopWord : (L).stop≤2^w := room
  have win := (L).bounds
  have hi : (L).floor<2^w := by omega
  obtain ⟨oldFit,edgeFit,allFit,workFloor⟩ := rank_limits start bound hi
  have afterBoard : (board).endAt+3*(board).old≤lo := by
    change work+4*(board).old+4*e+3*(board).old≤lo
    omega
  obtain ⟨mid,ranks,live,origins,low,keys,sourceFrame,values⟩ := ProtocolRAMTurnReplayed.rank_after_roles_last
    v.sampler board (T).stock matrix (CoreRoute.enum B order) v.mesh (v.wideEventSlices h width bits)
    lw lo ledger archive m ci cj directory receipts retained paid paidBefore afterBoard oldFit edgeFit inputs hi
    (by omega) budget old report before after resolved true
  have lookup (t : ℕ) (cap : t<e+entries) : (T).walk.edge.read mid (t:Word w)=(edge t:Word w) := by
    let i : Fin (e+entries):=⟨t,cap⟩
    have size := ProtocolRAMPackedRanked.group_capacity (e+entries)
    have word : t<2^w := cap.trans_le allFit
    change mid (lo+(t:Word w).val%2^ProtocolRAMPackedRanked.groupBits (e+entries))=_
    rw [Fin.val_cast_of_lt word,Nat.mod_eq_of_lt (cap.trans_le size)]
    simpa only [ProtocolRAMTurnOccurrence.edgeAt,dite_eq_left cap] using keys i
  have held (x : ℕ) (loR : rom≤x) (up : x<v.wideTerminalROMEnd h width bits rom work) :=
    (low x (up.trans_le hro)).trans («public» x loR up)
  have endsRead (a : Fin (board).old) (on : 0<old (pos (names a))) (j : ℕ) (hj : j<len a) :
      let x:=edge (ProtocolRAMTurnGeometry.origin order (names a)+j)
      (T).walk.tailSite.read mid (x:Word w)=((ends x).1:Word w) ∧
        (T).heads.read mid (x:Word w)=((ends x).2:Word w) := by
      obtain ⟨f,paidF,equal,one,two⟩:=used a on j hj
      have read := ProtocolRAMTurnSnapshot.reported_ends v.sampler board live f paidF _ _ one two
      rw [equal] at read
      exact read
  obtain ⟨kept,out,walk,stored,frame⟩ := v.wide_terminal_seated h width bits rom work B pad mark unique
    initial mid live held hro room siteWord lenWord first lookup endsRead ident aligned paidPorts
  have span : ProtocolRAMTurnReplayed.time lo e entries ledger paidAtLast=66+539*(e+entries)+6*e :=
    ProtocolRAMTurnPaidCost.rank_clock ..
  rw [←span] at ranks
  exact ⟨mid,kept,out,ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec.then ranks walk,stored,
    fun x hx=>(frame x (.inl (hx.trans_le workFloor))).trans (low x hx),fun x hx=>frame x (.inl hx),live,origins,keys,by cases archiveRows <;> first | exact values | exact ⟨sourceFrame,values⟩⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
