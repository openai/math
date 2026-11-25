import OAI.Hierarchy.ProbeFixedWideTerminalReads
import OAI.Hierarchy.ProtocolRAMTurnLiveGeometry

namespace OAI
/-! # The fixed shelf's five native words along the actual original occurrence walks -/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open CoreRoute HistoryRoles RoleProgram ProtocolRAMTurnChart
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical Fin.CommRing
private abbrev mountedEnds {n w : ℕ} (weight length origin : Fin n → ℕ)
    (lookup : ℕ → ℕ) (endpoints : ℕ → ℕ × ℕ) (tails heads : Bank) (m : Memory w) : Prop :=
  ∀ a, 0 < weight a → ∀ j < length a,
    let x := lookup (origin a + j)
    tails.read m (x : Word w) = ((endpoints x).1 : Word w) ∧
      heads.read m (x : Word w) = ((endpoints x).2 : Word w)

private theorem board_base_le_rank (b : Board) :
    b.base ≤ b.endAt+3*b.old+b.widthBank.size+(b.newRole true).size := by
  simp only [Board.endAt,Board.newBase]
  omega

private theorem replay_base_le_end (base count edges : ℕ) :
    base ≤ ProtocolRAMTurnReplayed.endAt base count edges := by
  change base ≤ base+2^ProtocolRAMPackedRanked.groupBits count+2^ProtocolRAMPackedRanked.groupBits count+
    2*count+3*count+4*count+edges+3+2^ProtocolRAMPackedRanked.groupBits (4*count)
  simp only [Nat.add_assoc]
  exact Nat.le_add_right ..

private theorem walk_rom_ranges (layout : ProtocolRAMTurnWindow.Layout) (rom roles work w : ℕ)
    (ready : layout.readOnlyEnd rom roles ≤ work) (placed : work ≤ layout.floor) (word : layout.stop ≤ 2^w) :
    layout.directoryBase rom ≤ layout.floor ∧ layout.halfBase rom ≤ layout.floor ∧
      layout.readOnlyEnd rom roles ≤ 2^w := by
  have bounds := layout.bounds
  have half : layout.halfBase rom ≤ layout.readOnlyEnd rom roles := Nat.le_add_right ..
  have directory : layout.directoryBase rom ≤ layout.halfBase rom := Nat.le_add_right ..
  exact ⟨directory.trans (half.trans (ready.trans placed)),half.trans (ready.trans placed),by omega⟩

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
local notation "len" => ProtocolRAMTurnGeometry.length (h:=h) (d:=D) (k:=k) (edges:=e) ∘ names
local notation "raw" => ProtocolRAMTurnOrder.raw len
local notation "pos" => ProtocolRAMTurnGeometry.sourceOrder e h D k
local notation "port" => Public v.sampler h v.W k v.wideJobs

variable {w:ℕ} {π : Equiv.Perm (Fin (2^h))}
  (B : Mount (S:=v.sampler) π (name (h:=h) (W:=v.W) (k:=k))
    (v.widePlacement h width).catalogue.rows)
  (pad : Chord (siteLast h (2^v.W) k+1))
local notation "inj" => (siteNumber h D k).injective
local notation "visit" => ProtocolRAMVisitAdjacency.vertex len (fun a=>ProtocolRAMTurnEdges.visit B inj pad (names a))
local notation "edge" => ProtocolRAMTurnOccurrence.edgeAt (h:=h) (d:=D) (k:=k) (edges:=e) B inj pad order
local notation "ends" => ProtocolRAMTurnOccurrence.endsAt (h:=h) (d:=D) (k:=k) (edges:=e) B inj pad

theorem wide_visit_bound (a : ProtocolRAMTurnGeometry.Source e h D k) (j : ℕ) :
    ProtocolRAMTurnEdges.visit B inj pad a j < siteLast h D k+1 :=
  match a with
  | .inl i => by
    change (if j = 0 then (filledChord B.actual pad i).1.1.val else (filledChord B.actual pad i).1.2.val) < _
    split
    · exact (filledChord B.actual pad i).1.1.isLt
    · exact (filledChord B.actual pad i).1.2.isLt
  | .inr (.inl i) => ((siteNumber h D k) (WordSeats.site π (WordSeats.commodityTurn i j))).isLt
  | .inr (.inr c) => ((siteNumber h D k) (WordSeats.site π (WordSeats.reserveTurn c j))).isLt


theorem wide_terminal_walk (initial m : Memory w)
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
    (used : mountedEnds (n:=Fintype.card (ProtocolRAMTurnGeometry.Source e h D k))
      (fun a => old (pos (names a))) len
      (fun a => ProtocolRAMTurnGeometry.origin (h:=h) (d:=D) (k:=k) (edges:=e) order (names a))
      edge ends (T).walk.tailSite (T).heads m)
    (put : ProtocolRAMTurnShelf.Live (ProtocolRAMTurnInstalled.columns (record u (captured (T).columns m) visit)
      (ProtocolRAMTurnSnapshot.values (T).walk m)) ↪ ProtocolRAMTurnShelf.Seats (T).sites (T).seats)
    (loc : ∀z,(put z).1.val=(record u (captured (T).columns m) visit z.val).site ∧
      (put z).2.val=(record u (captured (T).columns m) visit z.val).seat) :
    let rows:=ProtocolRAMTurnInstalled.columns (record u (captured (T).columns m) visit) (ProtocolRAMTurnSnapshot.values (T).walk m)
    ∃out,((L).program w (T).header (T).rom (T).columns (T).heads (T).walk).Exec m out (72+6096*(T).turns+30*((T).sites*(T).seats)) ∧
      (∀f:Fin 5,∀s:ProtocolRAMTurnShelf.Seats (T).sites (T).seats,
        out ((T).base+f.val*((T).sites*(T).seats)+s.1.val*(T).seats+s.2.val)=ProtocolRAMTurnShelf.entry rows put f s) ∧
      ∀a,a<(L).floor ∨ v.wideTerminalWorkEnd h width bits work≤a → out a=m a := by
  intro rows
  have floor : work ≤ (L).floor :=
    (board_base_le_rank board).trans
      (replay_base_le_end (v.wideTerminalRankStart h width bits work) ((T).edges+(T).routeEntries) (T).edges)
  obtain ⟨headerBefore,romBefore,roWord⟩ := walk_rom_ranges L rom roles work w hro floor room
  obtain ⟨hdr,dir,sources,amount,words⟩ := v.wide_terminal_reads h width bits rom work initial m live keep roWord
  obtain ⟨safe,banks⟩ := v.wide_terminal_banks h width bits rom work hro room
  let amt (a : Fin (board).old) := old (pos (names a))
  have initialSite (a : Fin (board).old) (on : 0<amt a) := live.rawSite (pos (names a)) on false
  have beginAt (a : Fin (board).old) (on : 0<amt a) : (T).columns.rawSource.read m ((pos (names a)).val:Word w)=
      (ProtocolRAMTurnEdges.visit B inj pad (names a) 0 : Word w) := by
    exact (initialSite a on).trans (congrArg (fun z : ℕ=>(z:Word w)) (first a on))
  have calcEnd := ProtocolRAMTurnMap.live_endpoint B inj pad order names (T).header (T).headerBits roles (T).columns
    (T).walk.edge (T).walk.tailSite (T).heads m amt hdr lenWord beginAt keys used
  have auth (i : Fin (T).turns) : (captured (T).columns m).width (u i).item=amt (raw i).1 :=
    words (pos (names (raw i).1))
  have sz (i:Fin (T).turns) : visit i<2^w :=
    (wide_visit_bound v h width B pad (names (raw i).1) (raw i).2.val).trans_le siteWord
  refine (L).run (T).header (T).rom (T).columns (T).heads (T).walk u (captured (T).columns m) visit m
    hdr sources amount safe rfl headerBefore romBefore
    (ProtocolRAMTurnGeometry.within order roles names) (fun i=>lenWord (raw i).1)
    (ProtocolRAMTurnOrder.has_previous len) (fun i hp hi=>?_)
    (fun i hi=>calcEnd i ((auth i) ▸ hi)) banks (fun i _=>sz i) put loc dir
    (fun i=>Fin.isLt _) room
  let j : Fin (T).turns := ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩
  have earlier := congrArg Sigma.fst (ProtocolRAMTurnOrder.previous_eq len i hp)
  have previousWidth := (auth j).trans (congrArg amt earlier)
  exact lt_of_lt_of_eq hi ((auth i).trans previousWidth.symm)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
