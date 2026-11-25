import OAI.Hierarchy.ProbeFixedCatalystBirth
import OAI.Hierarchy.ProbeFixedBirthFees
import OAI.Hierarchy.ProtocolRAMCalendarPrefixInterval
import OAI.Hierarchy.ProtocolRAMCalendarEventPrices

namespace OAI
/-! # Purchased parent archive reconstructed from strictly earlier calendar events -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory PurchaseFrozen PurchaseCT StockBound
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "d" => 2^v.W
local notation "W" => wordBits z d copies
local notation "G" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "B" => v.nativeBoards P z width
local notation "keys" => stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase

set_option maxHeartbeats 1000000 in
def catalyst_birth_before (initial : Memory W) (π : Equiv.Perm (Fin (2^z)))
    (p a j t : ℕ) (prior tail : List Event)
    (split : events v.mesh=prior++Event.attempt (.inner p a j t)::tail)
    (past : Calendar.mounted C prior initial)
    (geometry : Shelf.Geometry π initial) (heap : heapEnd z d copies≤(G).first)
    (room : (keys).stop≤(G).first) («public» : (keys).Loaded initial) :
    PurchasedBirth ((B).outer p a).market.shelf (B).sampler π v.depth ((B).stratumHeader p a)
      (run C prior initial) k := by
  apply Classical.choice
  let es:=events v.mesh
  let child:=Event.attempt (.inner p a j t)
  let a₀:=Attempt.outer p a
  let parent:=Event.attempt a₀
  let mkt:=v.frozenMarket P z width p a
  have later : child∈es := by rw [show es=prior++child::tail from split];simp
  obtain ⟨inList,ord⟩:=StockBound.parent_before v.mesh child a₀ later rfl
  obtain ⟨index,atParent⟩:=event_at v.mesh inList
  let i : Fin es.length:=⟨position v.mesh parent,index⟩
  have event : es[i.val]=parent := atParent
  have atChild:=PrefixInterval.split_position v.mesh child prior tail split
  have early : i.val<prior.length := by
    change position v.mesh parent<prior.length
    rw [←atChild]
    exact ord
  have length : prior.length≤es.length := by rw [show es=prior++child::tail from split]; simp
  have pre : es.take prior.length=prior := by rw [show es=prior++child::tail from split,List.take_left]
  have live : Calendar.mounted C (es.take prior.length) initial := by rw [pre];exact past
  let entry:=state C initial i.val
  let input:=(guard C a₀).apply entry
  let frozen:=mkt.failures.pass.apply input
  have ready : Calendar.ready C parent entry := by
    have hr:=PrefixInterval.ready_at C initial i early live
    change Calendar.ready C (es[i.val]) entry at hr
    rwa [event] at hr
  have earlier:=PrefixInterval.mounted_prefix C initial early.le live
  have bounded:=v.catalyst_birth_room P z width a₀
  have firstAt (e : Event) : (G).first≤(G).base v.mesh e := Nat.le_add_right ..
  have first := firstAt parent
  have frame (x : ℕ) (small : x<(G).first) : frozen x=initial x := by
    have source : entry x=initial x :=
      PrefixInterval.before_at C initial i.val x i.isLt.le earlier
        (fun u _=>(v.event_prefix P z width r banks src tab dst owners (es[u.val]'u.isLt) x
          (small.trans_le (firstAt _))).1)
    have guardLow : x<(C).stopAt a₀ := (small.trans_le first).trans_le (bounded.1.trans (min_le_left ..))
    have failureLow : x < mkt.failures.base := (small.trans_le first).trans_le (bounded.1.trans (min_le_right ..))
    change image mkt.failures.base mkt.failures.rows _ input x=initial x
    rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl failureLow)]
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl guardLow)).trans source
  have g:=Shelf.geometry_of_frame π initial frozen geometry (fun x hx=>frame x (hx.trans_le heap))
  have hdr : (keys).Loaded frozen := «public».frame (fun x _ hx=>frame x (hx.trans_le room))
  have Mready : mkt.ready input := ready.2.1
  obtain ⟨_,fixture,sample,prepared⟩:=Mready.2.2.2.2
  have incoming : mkt.shelf.Incoming (k:=k) v.sampler π v.depth mkt.phase mkt.temperature mkt.kind frozen := by
    refine ⟨sample.dimensions,?_,sample.table,sample.bankEnd,sample.stockEnd,sample.afterCT⟩
    intro u
    obtain ⟨enc,seen⟩ := g (PurchaseFrozen.stage u)
    exact ⟨enc,seen.group,seen.input,seen.output⟩
  have start : (keys).stop≤ mkt.shelf.firstBase := room.trans (first.trans bounded.2.1)
  have saved:=priced_purchase_after v.mesh v.finish (v.basePhase width) f
    (feedColumns (N:=Stages z d) v.mesh G f P.joint.initial width v.keepLimit)
    (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
    (fun e=>(StripChart.header F B e).fieldTerm) (StripChart.id F B P.catalogue) entry p a
    ((B).stratumHeader p a) π fixture ready incoming prepared start hdr
  refine ⟨⟨mkt.shelf.stockBase,mkt.phase,mkt.temperature,mkt.kind,frozen,?_⟩⟩
  apply saved.change
  intro x touched
  have fit : x<(G).base v.mesh parent+(G).stride :=
    (archiveCell_lt (show 1≤d from Nat.one_le_two_pow) start touched).trans_le bounded.2.2
  have paid : x<(G).base v.mesh es[i.val]+(G).stride := by rw [event];exact fit
  have keep:=PrefixInterval.after_arena C initial G i prior.length x early length live paid
    (fun u _ _ hx=>(v.event_prefix P z width r banks src tab dst owners (es[u.val]'u.isLt) x hx).1)
  change run C (es.take prior.length) initial x=after C es[i.val] entry x at keep
  change run C prior initial x = after C parent entry x
  rw [pre,event] at keep
  exact keep

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
