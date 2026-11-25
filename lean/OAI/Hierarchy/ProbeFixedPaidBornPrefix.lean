import OAI.Hierarchy.ProbeFixedPaidBirthOrdinal
import OAI.Hierarchy.ProbeFixedPriorForest
import OAI.Hierarchy.ProbeFixedWideCoreOnly
import OAI.Hierarchy.ProbePaidPrefixPositive
import OAI.Hierarchy.TaggedWireDatedLedger

namespace OAI
/-! # A positive purchased row in the prefix was acquired at an earlier date -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "f" => v.nativeFormats P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A))
local notation "start" => v.catalystStaticStart P h width
local notation "page" => v.wideSignedPage h width stock
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "banks" => TerminalLayout.settlement page stock
local notation "order" => wideRouteOrder h D k
local notation "route" => source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "recipe" => routeBanks start cnt r
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh A f (P).joint.initial width v.keepLimit

local notation "ownerBank" => sinkBank start cnt r (P).catalogue.rows
local notation "paidO" => v.catalystPairOwners P h width
local notation "paidP" => v.catalystPairParity P h width
local notation "floor" => (A).endAddress v.mesh
local notation "who" => v.nativeBoards P h width
local notation "tree" => v.nativeTrees P h width
local notation "sink" => (P).catalogue.sink r banks (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) ownerBank

local notation "es" => events v.mesh
local notation "until" => fun e=>(A).base v.mesh e+(A).stride

local notation "rows" => (P).catalogue.rows
local notation "chk" => fun m=> checkedOut C floor m
local notation "memAt" => fun m j=> StockBound.state C m j
local notation "stamp" => fun a=>(f a).labelSource sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
  (StripChart.id F who (P).catalogue a)
local notation "regular" => fun a=> PaidWidths.paidDirect (f a).pricedArea (f a).stockSource (stamp a)
local notation "secondary" => fun a u v'=> PaidWidths.paidMate (f a).pricedArea (f a).stockSource u v'
local notation "broadcasting" => fun (bits : ℕ) a=> PaidWidths.paidBroadcast (f a).pricedArea
  (tree a).positions (tree a).owner (tree a).parity (tree a).edge (tree a).sourceRow (f a).board.batch.copies bits

local notation "B" => (P).catalogue
local notation "dir" => (P).routes.directory
local notation "heads" => (dir).header h D k v.sampler.degree v.depth
local notation "ports" => max (Fintype.card (StripDirectory.PayloadRole N k))
  (Fintype.card (StripDirectory.PurchasedRole v.depth k))

/-- For a bought row the immutable birth coordinates identify an original
outer attempt strictly preceding the date at which its ID received a positive
width. Zero padding and every core-only role are excluded by the native ID. -/
theorem wire_born_before_charge (m : Memory w) (hdr : ∀a,Event.attempt a∈es→(StripChart.header F who a).Loaded m)
    (endWord : floor<2^w) (room : (B).rows<2^w) (fields : ports≤2^w)
    (core : v.CoreSpillRows h width m) (bits j : ℕ) (u : Fin (B).boughtRows)
    (paid : 0 < v.wirePaidAt h width bits j m ((B).boughtIndex u)) :
    ∃p : Fin v.wideJobs,∃t : Fin (es).length,
      (es).get t=.attempt (v.sourceAttempt p) ∧ t.val+1 < j ∧ ∃z : Fin (heads).ports,(heads).enum ⟨p,z⟩=u := by
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  obtain ⟨t,early,s,found,i,hit,_⟩:=PaidWidths.positive_in_prefix es (v.wideEventSlices h width bits) j m
    ((B).boughtIndex u) paid
  have notCore (r₀ : Word w) (same : r₀.val=((B).boughtIndex u).val)
      (code : (B).CoreOrPad r₀) : False := by
    have inRange:=((B).boughtIndex u).isLt
    change (B).coreRows+u.val<(B).rows at inRange
    change r₀.val=(B).coreRows+u.val at same
    change r₀.val<(B).coreRows ∨ r₀.val=(B).rows at code
    omega
  have dated:=(es).get_mem t
  cases event : (es).get t with
  | feed b =>
    rw [event] at found
    change s∈((lay b).columns).map _ at found
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp found
    exact False.elim (notCore _ hit (Or.inl (core.2 b c hc i)))
  | attempt a =>
    rw [event] at found dated
    change s∈(f a).paidSlices sink (B).idBase (StripChart.header F who a).fieldTerm
      (StripChart.id F who B a) (tree a) (v.paidSpillPath P h width recipe route order a) bits at found
    have bought (r₀ : Fin (f a).pricedArea.occurrences)
        (foundAt : ((stamp a).edge.eval m (r₀.val:Word w)).val=((B).boughtIndex u).val) :
        ∃p : Fin v.wideJobs,∃t : Fin (es).length,(es).get t=.attempt (v.sourceAttempt p) ∧ t.val+1 < j ∧
          ∃z : Fin (heads).ports,(heads).enum ⟨p,z⟩=u := by
      obtain ⟨p,r₁,_,_,z,_,released,before⟩:=v.paid_direct_birth h width a dated m (hdr a dated) fields room r₀ u foundAt
      let p₀ : Fin v.wideJobs:=finProdFinEquiv (p,r₁)
      have tag : v.sourceAttempt p₀=.outer p.val r₁.val := by
        simp [sourceAttempt,sourceOuter,p₀]
      have occurred : Event.attempt (.outer p.val r₁.val)∈es :=
        List.mem_flatMap.mpr ⟨p.val,List.mem_range.mpr p.isLt,List.mem_append_left _
          (List.mem_flatMap.mpr ⟨r₁.val,List.mem_range.mpr r₁.isLt,List.mem_cons_self ..⟩)⟩
      obtain ⟨t₀,marked⟩:=List.mem_iff_get.mp occurred
      have now : position v.mesh ((es).get t)=t.val:=by simpa only [List.get_eq_getElem] using position_at v.mesh t.isLt
      have orig : position v.mesh ((es).get t₀)=t₀.val:=by simpa only [List.get_eq_getElem] using position_at v.mesh t₀.isLt
      rw [event] at now
      rw [marked] at orig
      exact ⟨p₀,t₀,by rw [tag];exact marked,by omega,z,released⟩
    have forestCore (r₀ : Word w) : (B).CoreOrPad ((tree a).edge.eval m r₀) := by
      obtain ⟨_,old,eq,_,clamped⟩:=v.elapsed_forest_words h width a dated ((A).base v.mesh (.attempt a))
        le_rfl (((Nat.le_add_right ..).trans ((A).within v.mesh _ dated)).trans_lt endWord) room
      rw [eq]
      have good:=clamped m r₀
      let k₀ : Fin (B).coreRows:=⟨(old.eval m r₀).val,good⟩
      rw [(B).checked_core old m r₀ k₀ room rfl]
      left
      simpa only [Fin.val_cast_of_lt (show k₀.val<2^w by have := k₀.isLt;unfold Board.rows at room;omega)] using k₀.isLt
    cases issued : (tree a).catalystMate with
    | none =>
      simp only [Format.paidSlices,Format.mateSlices,issued,Option.toList_none,List.map_nil,
        List.cons_append,List.nil_append,List.mem_cons,List.mem_nil_iff,or_false] at found
      rcases found with rfl|rfl|rfl
      · exact bought i hit
      · exact False.elim (notCore _ hit (forestCore _))
      · exact False.elim (notCore _ hit (Or.inl (core.1 a i)))
    | some pair =>
      simp only [Format.paidSlices,Format.mateSlices,issued,Option.toList_some,List.map_cons,List.map_nil,
        List.cons_append,List.nil_append,List.mem_cons,List.mem_nil_iff,or_false] at found
      rcases found with rfl|rfl|rfl|rfl
      · exact bought i hit
      · exact False.elim (notCore _ hit (v.prior_mate_range h width a dated endWord room pair.1 pair.2 issued m _))
      · exact False.elim (notCore _ hit (forestCore _))
      · exact False.elim (notCore _ hit (Or.inl (core.1 a i)))

theorem wire_born_in_prefix (m : Memory w) (hdr : ∀a,Event.attempt a∈es→(StripChart.header F who a).Loaded m)
    (endWord : floor<2^w) (room : (B).rows<2^w) (fields : ports≤2^w)
    (core : v.CoreSpillRows h width m) (bits j : ℕ) (u : Fin (B).boughtRows)
    (paid : 0 < v.wirePaidAt h width bits j m ((B).boughtIndex u)) :
    ∃p : Fin v.wideJobs,∃t : Fin (es).length,
      (es).get t=.attempt (v.sourceAttempt p) ∧ t.val < j ∧ ∃z : Fin (heads).ports,(heads).enum ⟨p,z⟩=u := by
  obtain ⟨p,t,date,earlier,rel,id⟩:=v.wire_born_before_charge h width m hdr endWord room fields core bits j u paid
  exact ⟨p,t,date,by omega,rel,id⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
