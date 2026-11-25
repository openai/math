import OAI.Hierarchy.ProbeFixedWideTerminal
import OAI.Hierarchy.TaggedWireLiveRoleSides
import OAI.Hierarchy.TaggedWideCalendarTurnRank
import OAI.Hierarchy.TaggedWireChronologicalMatrix

namespace OAI
/-! # Physical turn fields read from the funded rank and role banks -/
noncomputable section
open scoped Fin.CommRing
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open CoreRoute HistoryRoles RoleProgram ProtocolRAMTurnItinerary ProtocolRAMTurnStepOrder
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits rom work : ℕ)
local notation "S" => v.sampler
local notation "D" => 2^v.W
local notation "K" => siteLast h D k+1
local notation "name" => siteNumber h D k
local notation "pad" => publicChord h D k
local notation "w" => Native.wordBits h D Native.copies
local notation "board" => v.wideTerminalBoard h width bits work
local notation "T" => v.wideTerminal h width bits rom work
local notation "edges" => (v.widePlacement h width).catalogue.rows
local notation "entries" => Fintype.card (Slots h D k)
local notation "n" => edges+entries
local notation "lo" => v.wideTerminalRankStart h width bits work
local notation "keys" => ProtocolRAMTurnReplayed.key lo n
local notation "base" => ProtocolRAMTurnReplayed.ranks lo n edges
local notation "rank" => ProtocolRAMTurnReplayed.rank lo n edges
local notation "o" => wideRouteOrder h D k
local notation "names" => (ProtocolRAMTurnGeometry.sourceOrder edges h D k).symm
local notation "port" => Public S h v.W k v.wideJobs
variable {π : Equiv.Perm (Fin (2^h))}
  (B : Mount («S» := v.sampler) π (siteNumber h (2^v.W) k) (v.widePlacement h width).catalogue.rows)
local notation "L" => B.matrixLayout (name).injective pad
variable (fixed : Fin (v.widePlacement h width).catalogue.rows→ℕ)
  (stock : Commodity (Fin (2^h)) (Stages h (2^v.W)) k→ℕ)
  (reserved used : Columns h (2^v.W)×Fin k→ℕ)
  (outWidth : Fin (v.widePlacement h width).catalogue.rows→ℕ)
local notation "mass" => SettledMatrix.Layout.bits fixed stock reserved used
local notation "key" => (L).nativeEdge (enum B o)
local notation "loads" => (L).nativeWidth (enum B o) fixed stock reserved used
variable (before : ∀i,0<SettledMatrix.Layout.bits fixed stock reserved used i→
    Bool→Public v.sampler h v.W k v.wideJobs)
  (after : ∀e,0<outWidth e→Bool→Public v.sampler h v.W k v.wideJobs)
local notation "oldCode" => liveCode S false mass before
local notation "newCode" => liveCode S true outWidth after

/-- Reading a single physical seven-field record at its canonical chronological boundary.
The previous/next branch of either selector uses the rank tape at the original occurrence,
including when an edge appears more than once in a route. -/
theorem wide_turn_field_pair (m : Memory w) (t : Turn)
    (i : Fin (board).old) (on : 0< mass i)
    (sp : Spine (rowGraph (L).edge) ((L).family i).1.1 ((L).routes i) ((L).family i).1.2)
    (j : Fin (((L).routes i).length+1))
    (it : t.item=i.val) (orig : t.origin=ProtocolRAMTurnGeometry.origin o (names i))
    (len : t.length=ProtocolRAMTurnGeometry.length (names i))
    (rev : t.reverse=reverse B (name).injective pad (names i)) (pos : t.position=j.val)
    (loc : t.site=(sp.visit j).val)
    (auth : (board).LiveReads S mass outWidth before after m)
    (storedKey : ∀a : Fin n,m (lo+a.val)=((key a).val:Word w))
    (storedRank : ∀a : Fin n,m (base+4*a.val+3)=(TaggedShorterCommonScan.earlier key loads a.val (key a):Word w))
    (wordRoom : 4*n≤2^w) (siteRoom : K≤2^w)
    (oldFits : ∀b,ProtocolRAMTurnOperands.printed S false (before i on) b false<2^w)
    (newFits : ∀e (live : 0<outWidth e) b,ProtocolRAMTurnOperands.printed S true (after e live) b false<2^w)
    (paid : ∀a : Fin ((L).routes i).length,0<outWidth (((L).routes i).get a))
    (tailSite : ∀e (live : 0<outWidth e),
      ProtocolRAMTurnOperands.printed S true (after e live) false true=((L).edge e).1.1.val)
    (small : ∀a : Fin ((L).routes i).length,routeLoad (L).routes mass (((L).routes i).get a)<2^w) :
    let col:=t.field (ProtocolRAMTurnSnapshot.values (T).walk m)
    let atSide:=fun b : Bool=>let z:=sp.sides (.inl false) (.inl true) 0 j
      if b then z.2 else z.1
    ∀b : Bool,col (if b then 1 else 0)=refRole (L).routes oldCode newCode i (atSide b) ∧
      col (if b then 3 else 2)=refStart (L).routes mass ((L).nativeOrder (enum B o)) i (atSide b) := by
  intro col atSide b
  have nRoom : n≤2^w := by omega
  have edgeRoom : edges≤2^w := by omega
  have roles:=native_live_roles S board B (name).injective pad o names i mass outWidth before after
    on paid m keys rank auth storedKey nRoom (ProtocolRAMPackedRanked.group_capacity n) edgeRoom
    oldFits newFits siteRoom sp j t it orig len rev pos loc (fun a=>tailSite _ (paid a))
  have starts:=live_starts S board B (name).injective pad o fixed stock reserved used keys base
    (ProtocolRAMPackedRanked.groupBits (4*n)) m wordRoom (ProtocolRAMPackedRanked.group_capacity (4*n))
    i on small storedRank sp j t orig len rev pos
  cases b
  · exact ⟨roles.1,starts.1⟩
  · exact ⟨roles.2,starts.2⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
