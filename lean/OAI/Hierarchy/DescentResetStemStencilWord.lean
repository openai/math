import OAI.Hierarchy.DescentResetSignedStencilRun
import OAI.Hierarchy.DescentSignedChartAddress

namespace OAI
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals
open DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPacking.PackedMatch.Local ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "fits" => frame.enough.trans (Nat.sub_le m g)
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "H" => Host J V k
local notation "src" => DescentIssuedFallbackPanel.endSite (W:=W) A
local notation "shortT" => fun t=>shortName c (T.code t)

open DescentPlainTerminal DescentPlainTerminal.Suffix
local notation "degreeAt" => fun u=>Z.placement.b (frame.host u)
local notation "limit" => fun u=>Nat.le_trans (Z.placement.depth (frame.host u)) (Nat.le_of_eq frame.extent)
local notation "sourceIx" => StarKeys.filled W.graph A.pos A.block digits
local notation "physicalSite" => home A
local notation "yAt" => fun u=>rearrange frame.basis (sourceIx u)
local notation "upperAt" => fun u=>high fits (yAt u)
local notation "lowerAt" => fun u=>@DescentPlainTerminal.low m T.commonDepth (yAt u)

/-- Reconstruct the previous physical endpoint's assigned high group and low digit from
the measured matrix, then read its actual untagged stencil integer. -/
def stencilWordAt {w B H' nBits M' : ℕ} (map : Layout m) (small : B≤ m) (host : V↪Fin H')
    (column : ℕ) (last : Memory w) (positive : 0<M') (p : Host J V k) : ℕ :=
  let y:=rearrange map (oldBlock digits p)
  let hi:=high small y
  let lo:=@DescentPlainTerminal.low m B y
  digit nBits lo.val (digit (nBits*2^(m-B)) (lane hi positive).val (last (column+(DescentSIMDLookup.row H' (2^B) M'
      (position (host p.1.2) hi positive)).val)).val)

variable {w slots n t Δ B K wire f M cap : ℕ}
variable (rank : V↪Fin slots) (vertex : V↪ℕ) (near : V→Finset V)
    (wt : V→Block m→ℕ) (traffic : V→V→Block m→ℕ) (inc : V→List V)
    (port : V→Fin Δ→Option V) (listed : ∀v u,u∈near v ↔ ∃j,port v j=some u)
    (recip : ∀v u,u∈near v→v∈near u)
local notation "q₀" => (Δ+Δ)
local notation "vec" => ContactRoster.ports near port listed recip
local notation "pnl" => Stencil.measured (n:=n) fits near degreeAt frame.basis wt traffic A.hub Δ f B K g cap vec inc

theorem stem_stencil_word (roster : ResetInput.SourceFrame.Roster Z T (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g frame vertex near Z.n f B wire K (fun v u j=>(traffic v u j:ℝ)) Δ wt)
    (incoming : ∀u z,u∈inc z ↔ z∈near u) (smallWeight : ∀v x,wt v x<2^n) (smallTraffic : ∀v z x,traffic v z x≤cap)
    (floorBits : m-c<2^n) (positiveBits : 1<2^n) (stackBits : 2^(m-c)*cap<2^n)
    (codeBits : 2*DescentFallbackShapeTable.rows (m-c) (2^Z.n)≤2^t)
    (hB : 0<B) (hK : 0<K) (hD : 0<32*Nat.clog 2 (2*Δ))
    (tabs : Fin (Stencil.count (m-c) q₀)→Tables) (field : Stencil.Slot (m-c) q₀→Expr)
    (banks : Banks) (out : ℕ) (mem : Memory w) (positive : 0<M)
    (fit : DescentSIMDLookup.Fits banks (n*Stencil.count (m-c) q₀) (t*2^(m-c)) M slots (2^c) w out)
    (bounds : Gather.Bounds (w:=w) (d:=n) (M:=M) tabs (fun j=>field (Stencil.slotName (m-c) q₀ j)) banks.source.base)
    (space : banks.source.base+slots*chunks (2^c) M<2^w)
    (dictionaries : ∀j,Static (tabs j) (Gather.setField (d:=n) j) M mem)
    (physical : Fin slots→Block c→Stencil.panel (m-c) q₀ n)
    (actor : ∀v hi,physical (rank v) hi=pnl v hi)
    (source : ∀s,Source (field s) (fun v hi=>physical v hi s) M mem)
    (table : resident (Stencil.lookup (m-c) q₀ n t f B (2^Z.n)) banks slots (2^c) M mem)
    (beforeTable : banks.dictionary.base+banks.dictionary.size≤banks.source.base)
    (beforeMask : banks.mask.base+banks.mask.size≤banks.source.base) :
    ∃dst,(Stencil.execute tabs field banks out slots (2^c) M w).Exec mem dst (Stencil.cost tabs field slots (2^c) M) ∧
      (∀s (e : E),stencilWordAt (nBits:=t) digits frame.basis fits rank out dst positive (home A (endSite A s e))=
        peerShapeWord A S ready digits Z T frame s (home A (endSite A s e))) ∧
      (∀z<banks.source.base,dst z=mem z) ∧ ∀z,out+slots*chunks (2^c) M≤z→dst z=mem z := by
  obtain ⟨dst,ran,sample,early,late⟩:=signed_stencil_run A S ready digits Z T frame rank vertex near wt traffic inc port listed recip roster incoming smallWeight smallTraffic floorBits positiveBits stackBits codeBits hB hK hD tabs field banks out mem positive fit bounds space dictionaries physical actor source table beforeTable beforeMask
  refine ⟨dst,ran,?_,early,late⟩
  intro s e
  simpa only [stencilWordAt,oldBlock,StarKeys.filled,home,peerShapeWord,chartShape,
    DescentSharedBookScan.shapeCell,frame.extent] using sample s e

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
