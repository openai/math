import OAI.Hierarchy.ProbeFixedCatalystBirth
import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProbeFixedStockWindow
import OAI.Hierarchy.ProtocolRAMCalendarStripChoices
import OAI.Hierarchy.ProtocolRAMCalendarAlphabetCap
import OAI.Hierarchy.ProtocolRAMCatalystArchiveMaster

namespace OAI
/-! # Real read addresses that determine the next private alphabet -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe StripChart StripDirectory PurchaseFrozen
open ThreeFlat.RAM
open CatalystArchive
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width : ℕ)
local notation "d" => 2^v.W
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "sized" => v.sized (v.seed P z width) width
local notation "slab" => v.slab (v.seed P z width) P width
local notation "B" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "H" => v.publicHeader P z width
local notation "w" => wordBits z d copies

private theorem vector_end {phases D : ℕ} (t : DiscrepancyROM.Table phases D) (i : Fin phases) :
    (t.bank i).base+(t.bank i).size≤t.stop := by
  change t.base+i.val*t.size+t.size≤t.base+phases*t.size
  rw [Nat.add_assoc,←Nat.succ_mul]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) _

private theorem scalar_end {phases : ℕ} (t : ScalarROM.Table phases) (i : Fin phases) :
    (t.bank i).base+(t.bank i).size≤t.stop := by
  change t.base+i.val*t.size+t.size≤t.base+phases*t.size
  rw [Nat.add_assoc,←Nat.succ_mul]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) _

private theorem score_end (b : JointHeader.Board) (c : Mesh) (z stageCount k : ℕ) (a : Attempt) :
    GlobalTests.stop (DeadlineROM.scorePage c (JointHeader.scores b z stageCount k) z stageCount k a) z stageCount k≤
      JointHeader.stop b z stageCount k (DeadlineROM.count c) := by
  unfold DeadlineROM.scorePage
  rw [GlobalTests.page_stop]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (DeadlineROM.index c a).isLt) _

theorem alphabet_words :
    let s:=v.configured (v.seed P z width)
    let bound:=(catalogue F s v.cost).alphabet
    (∀i a,(H).menus.leftAlphabet.word i a≤bound) ∧ (∀i a,(H).menus.rightAlphabet.word i a≤bound) := by
  intro s bound
  constructor
  · apply MenuROM.alphabet_cap
    intro j
    exact (catalogue F s v.cost).alphabet_ge (.inl j)
  · apply MenuROM.alphabet_cap
    intro j
    exact (catalogue F s v.cost).alphabet_ge (.inr j)

/-- The last padded cell of every scalar-price, score, recommendation, alphabet
and discrepancy bank is below its own private attempt page. -/
theorem election_public (a : Attempt) :
    let i:=DeadlineROM.index v.mesh a
    let limit:=(A).base v.mesh (.attempt a)
    ((H).scalar.bank i).base+((H).scalar.bank i).size≤limit ∧
    GlobalTests.stop (DeadlineROM.scorePage v.mesh (JointHeader.scores P.joint z N k) z N k a) z N k+
      2^(GlobalTests.bits z N k)≤limit ∧
    ((H).menus.left.bank i).base+((H).menus.left.bank i).size≤limit ∧
    ((H).menus.right.bank i).base+((H).menus.right.bank i).size≤limit ∧
    ((H).menus.leftAlphabet.bank 0).base+((H).menus.leftAlphabet.bank 0).size≤limit ∧
    ((H).menus.rightAlphabet.bank 0).base+((H).menus.rightAlphabet.bank 0).size≤limit ∧
    ((H).payload.bank i).base+((H).payload.bank i).size≤limit ∧
    ((H).bought.bank i).base+((H).bought.bank i).size≤limit := by
  intro i limit
  have o:=economic_ordered F sized v.cost v.mesh P.joint P.catalogue P.routes v.finish (v.basePhase width)
    v.digitRadix v.digitRadix v.precision v.precision
  change (H).Ordered at o
  have afterHeader : (H).stop+2^(GlobalTests.bits z N k)≤limit := by
    exact (v.header_scoreEnd_le_first P z width).trans (Nat.le_add_right ..)
  have bound : (H).stop≤limit:=(Nat.le_add_right ..).trans afterHeader
  have scoreStart : JointHeader.stop P.joint z N k (DeadlineROM.count v.mesh)=(H).ports.base:=rfl
  have scoreBound : JointHeader.stop P.joint z N k (DeadlineROM.count v.mesh)≤(H).stop :=
    scoreStart.le.trans ((Nat.le_add_right ..).trans (economic_ports_end H o))
  have last : (H).menus.rightAlphabet.stop≤(H).stop:=o.payloadTreeBase.le.trans
    ((Nat.le_add_right ..).trans (o.boughtTreeBase.le.trans (Nat.le_add_right ..)))
  have right:=last.trans bound
  have left:=o.menuOrdered.third.trans ((Nat.le_add_right ..).trans right)
  have mr:=o.menuOrdered.second.trans ((Nat.le_add_right ..).trans left)
  have ml:=o.menuOrdered.first.trans ((Nat.le_add_right ..).trans mr)
  have d₂:=o.menusBase.le.trans ((Nat.le_add_right ..).trans ml)
  have d₁:=o.boughtBase.le.trans ((Nat.le_add_right ..).trans d₂)
  have sc:=o.payloadBase.le.trans ((Nat.le_add_right ..).trans d₁)
  refine ⟨(scalar_end _ _).trans sc,?_,(vector_end _ _).trans ml,(vector_end _ _).trans mr,
    (vector_end _ _).trans left,(vector_end _ _).trans right,(vector_end _ _).trans d₁,(vector_end _ _).trans d₂⟩
  exact (Nat.add_le_add_right ((score_end ..).trans scoreBound) _).trans afterHeader

set_option cleanup.letToHave false in
set_option maxHeartbeats 2000000 in
/-- Installing the private slab again preserves the fully mounted native board. -/
theorem nativeBoards_install : Slab.install slab B v.mesh = B := rfl

set_option cleanup.letToHave false in
set_option maxHeartbeats 1200000 in
theorem election_pages (a : Attempt)
    (cap : v.menu.maximum<2^w) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^w)
    (core : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial) :
    Slab.beforeTables slab B F v.mesh P.joint.initial a := by
  have actualArena : Slab.arena slab B = A := rfl
  simp only [Slab.beforeTables,v.nativeBoards_install P z width,actualArena]
  have pub:=v.election_public P z width a
  obtain ⟨pr,sc,ml,mr,al,ar,df,dg⟩:=pub
  have old:=v.stock_padded_old P z width a
  have sz:=v.stock_raw_old_size P z width a
  have maxWord:=(v.ordinary_dimensions P z width a).1.trans_lt cap
  cases a with
  | outer p h=>
    refine ⟨pr,sc,?_,ml,al,df,maxWord,threshold⟩
    exact (Nat.add_le_add_left sz.le _).trans old
  | inner p h j u=>
    refine ⟨⟨pr,sc,?_,mr,ar,dg,maxWord,threshold⟩,?_⟩
    · exact (Nat.add_le_add_left sz.le _).trans old
    · obtain ⟨flags,tiles⟩:=v.catalyst_bought_bank_room P z width p h j u
      apply purchased_before ((B).outer p h).market.shelf (B).sampler v.depth ((B).stratumHeader p h)
        ((A).base v.mesh (.attempt (.inner p h j u))) tiles flags
      let hd:=stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase
      have first:=v.catalyst_initial_le_first P z width
      have upto : hd.stop≤(A).base v.mesh (.attempt (.inner p h j u)) :=
        core.trans (first.trans (Nat.le_add_right ..))
      have columns (start small large bound : ℕ) (hi : start+2*small+large+large≤bound) :
          start+small≤bound ∧ start+small+small≤bound := by omega
      exact columns hd.start hd.small hd.large _ upto

/-- The archive directory was installed on the original boot before the
initial inventory, using the same fixed key ordinals as both strip types. -/
theorem election_key_room (slot classes height R : ℕ) (b : JointHeader.Board) (cat : CatalogueRows.Board)
    (orig : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
    (allocated : CoreRoute.stop v.sampler z v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)
      v.depth slot classes height R≤b.initial) :
    let P:=v.catalystPlacement z slot classes height R b cat orig
    (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial := by
  let base:=CoreCatalogue.top z v.W slot classes height R
  let n:=(v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
  exact (BoughtSockets.Public.borders v.sampler base z v.W k n v.depth).2.trans
    ((Nat.le_add_right ..).trans allocated)

theorem native_measured (r : ℕ) (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
    (es : List Event) (a : Attempt) (boot : Boot.Tape z d)
    (origin : (H).menus.leftAlphabet.Capped (catalogue F (v.configured (v.seed P z width)) v.cost).alphabet boot ∧
      (H).menus.rightAlphabet.Capped (catalogue F (v.configured (v.seed P z width)) v.cost).alphabet boot)
    (ok : Calendar.mounted (v.nativeChart P z width r banks src tbl dst owners) es boot)
    (readyNow : ready (v.nativeChart P z width r banks src tbl dst owners) (.attempt a)
      (run (v.nativeChart P z width r banks src tbl dst owners) es boot))
    (i : Fin ((v.nativeChart P z width r banks src tbl dst owners).layout a).candidates) :
    WireTelescope.CalendarTape.CounterROM.measured (C:=v.nativeChart P z width r banks src tbl dst owners)
      a (run (v.nativeChart P z width r banks src tbl dst owners) es boot) i≤
      (catalogue F (v.configured (v.seed P z width)) v.cost).alphabet := by
  let C:=v.nativeChart P z width r banks src tbl dst owners
  have ls : (H).menus.leftAlphabet.stop≤(A).first ∧ (H).menus.rightAlphabet.stop≤(A).first := by
    have o:=economic_ordered F sized v.cost v.mesh P.joint P.catalogue P.routes v.finish (v.basePhase width)
      v.digitRadix v.digitRadix v.precision v.precision
    change (H).Ordered at o
    have h:(H).stop≤(A).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
    have r:=o.payloadTreeBase.le.trans ((Nat.le_add_right ..).trans (o.boughtTreeBase.le.trans ((Nat.le_add_right ..).trans h)))
    exact ⟨o.menuOrdered.third.trans ((Nat.le_add_right ..).trans r),r⟩
  have safe (t : DiscrepancyROM.Table 1 1) (early : t.stop≤(A).first) (x : ℕ)
      (_ : t.base≤x) (last : x<t.stop) (e : Event) : protected C x e :=
    (v.event_prefix P z width r banks src tbl dst owners e x (last.trans_le (early.trans (Nat.le_add_right ..)))).1
  cases a with
  | outer p h=>
    exact measured_alphabet C es boot (.outer p h) (H).menus.leftAlphabet rfl origin.1 ok readyNow
      (fun x lo hi e _=>safe _ ls.1 x lo hi e) i
  | inner p h j t=>
    exact measured_alphabet C es boot (.inner p h j t) (H).menus.rightAlphabet rfl origin.2 ok readyNow
      (fun x lo hi e _=>safe _ ls.2 x lo hi e) i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
