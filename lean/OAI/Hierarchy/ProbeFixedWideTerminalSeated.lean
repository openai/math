import OAI.Hierarchy.ProbeFixedWideTerminalWalk
import OAI.Hierarchy.ProtocolRAMPaidTurnCoordinates

namespace OAI
/-! # Stored age, role and offset selectors at the original paid site and seat -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open CoreRoute HistoryRoles RoleProgram ProtocolRAMTurnChart
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical Fin.CommRing
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

theorem wide_terminal_seated (mark : markFor) (unique : Exclusive mark) (initial m : Memory w)
    {old : Fin (board).old→ℕ} {report : Fin (board).edges→ℕ}
    {before : ∀i,0<old i→Bool→port} {after : ∀i,0<report i→Bool→port}
    (live : (board).LiveReads v.sampler old report before after m)
    (keep : ∀a,rom≤a→a<v.wideTerminalROMEnd h width bits rom work→
      m a=v.wideTerminalWords h width bits rom work initial a)
    (hro : v.wideTerminalROMEnd h width bits rom work≤work)
    (room : v.wideTerminalWorkEnd h width bits work≤2^w)
    (siteWord : (T).sites≤2^w) (lenWord : ∀a,len a<2^w)
    (first : ∀a (on : 0<old (pos (names a))),
      (name (HistoryRoles.site v.sampler (before (pos (names a)) on false))).val =
        ProtocolRAMTurnEdges.visit B inj pad (names a) 0)
    (keys : ∀t<e+Fintype.card (Slots h D k),(T).walk.edge.read m (t:Word w)=(edge t:Word w))
    (used : ∀a,0<old (pos (names a))→∀j<len a,
      let x:=edge (ProtocolRAMTurnGeometry.origin order (names a)+j)
      (T).walk.tailSite.read m (x:Word w)=((ends x).1:Word w) ∧ (T).heads.read m (x:Word w)=((ends x).2:Word w))
    (ident : {i : Fin (T).edges // 0<old (ow i)} ↪ Catalogue v.sampler π v.depth mark)
    (aligned : ∀i : {i : Fin (T).edges // 0<old (ow i)},filledChord B.actual pad i.val=
      HistoryRoles.sorted v.sampler π v.depth mark (.inl (ident i)))
    (paidPorts : ∀i : {i : Fin (T).edges // 0<old (ow i)},∃flip : Bool,∀side,
      before (ow i.val) i.property side=.inl (HistoryRoles.paid v.sampler π v.depth mark unique (ident i,if flip then !side else side))) :
    let fixed:=fun i : Fin (T).edges=>old (ow i)
    let cols:=ProtocolRAMTurnInstalled.columns (record u (captured (T).columns m) visit) (ProtocolRAMTurnSnapshot.values (T).walk m)
    ∃ (retained : ∀j : ProtocolRAMTurnShelf.Live cols, ProtocolRAMLiveTurnOrder.retain fixed
          (ProtocolRAMPaidTurnPlacement.rawItem names j.val).1) (out : Memory w),
      ((L).program w (T).header (T).rom (T).columns (T).heads (T).walk).Exec m out (72+6096*(T).turns+30*((T).sites*(T).seats)) ∧
      (∀f:Fin 5,∀s:ProtocolRAMTurnShelf.Seats (T).sites (T).seats,
        out ((T).base+f.val*((T).sites*(T).seats)+s.1.val*(T).seats+s.2.val)=ProtocolRAMTurnShelf.entry cols
          (ProtocolRAMPaidTurnPlacement.chartPut v.sampler π v.depth mark unique B pad fixed ident names cols retained) f s) ∧
      ∀a,a<(L).floor ∨ v.wideTerminalWorkEnd h width bits work≤a → out a=m a := by
  intro fixed cols
  let d:=(T).columns
  let words:=captured d m
  let ranks:=ProtocolRAMTurnSnapshot.values (T).walk m
  have widthAt (i:Fin (T).edges) : words.width (ow i).val=fixed i:=live.width (ow i)
  have kept := ProtocolRAMPaidTurnPlacement.record_keep (S:=v.sampler) (π:=π) (B:=B) (pad:=pad) (fixed:=fixed)
      (attempts:=v.wideJobs) (words:=words) («order»:=names) order ranks widthAt
  let physical := ProtocolRAMPaidTurnPlacement.chartPut v.sampler π v.depth mark unique B pad fixed ident names cols kept
  have bankWord := (v.wide_terminal_banks h width bits rom work hro room).1.half.2.1
  have within := ProtocolRAMSupergroupDirectory.slotFits (2*roles)
  have halfFits : 2*roles≤2^w := within.le.trans bankWord.le
  have coded := ProtocolRAMPaidTurnPlacement.captured_fixed_ordered (S:=v.sampler) (π:=π) (depth:=v.depth)
    (mark:=mark) (uni:=unique) (fixed:=fixed) (ident:=ident) board (L).site (T).columns.half live halfFits
    (fun i=>ow i.val) (fun _=>rfl) (fun i=>i.property) paidPorts
  have coordinate := ProtocolRAMPaidTurnPlacement.loc (S:=v.sampler) (π:=π) (depth:=v.depth)
    (mark:=mark) (uni:=unique) (B:=B) (pad:=pad) (fixed:=fixed) (ident:=ident)
    (aligned:=aligned) («order»:=names) (col:=cols) (kept:=kept) (words:=words) (fixedWords:=coded) order
  obtain ⟨out,ran,records,frame⟩ := v.wide_terminal_walk h width bits rom work B pad initial m live keep hro room
    siteWord lenWord first keys used physical coordinate
  exact ⟨kept,out,ran,records,frame⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
