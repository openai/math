import OAI.Hierarchy.ProtocolRAMCalendarStripBootSize
import OAI.Hierarchy.ProtocolRAMCalendarStripSeen

namespace OAI
/-! # The private selector rectangle survives every earlier native calendar event -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage
open StripDirectory
open scoped Classical Fin.CommRing
variable {z d k q depth r : ℕ}
local notation "stageCount" => List.length (Fabric.shapes (permutationFabric z d))
local notation "W" => wordBits z d copies
variable (v : Slab) (s : Boards z d k q depth) (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (c : Mesh) (initial width cap : ℕ) (finish : ℝ) (prices : PhasePrice) (catalogue : CatalogueRows.Board)
  (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
local notation "A" => arena v s
local notation "B" => install v s c
local notation "S" => catalogue.sink r banks src tbl dst owners
local notation "C" => chart F c A initial width cap B finish prices catalogue r banks src tbl dst owners
local notation "profiles" => formats F c A initial B

structure Bounds {wordWidth letters ports : ℕ} (program : Chart wordWidth letters ports) (a : Attempt) (cut : ℕ) : Prop where
  guard : program.stopAt a+1≤cut
  frozen : (program.frozen a).stop≤cut
  excess : (repair program a).tests.excess.out+(repair program a).tests.excess.rows+1≤cut
  payload : (repair program a).tests.payload.out+(repair program a).tests.payload.rows+1≤cut
  discrepancy : (repair program a).tests.discrepancy.out+((repair program a).tests.discrepancy.rows+1)≤cut
  mask : (repair program a).repairBits.base+(program.layout a).candidates≤cut
  keys : (repair program a).keys+(program.layout a).candidates≤cut
  tally : (repair program a).tally+2≤cut
  writes : ∀p∈PurchaseStage.writes (program.layout a) (repair program a),p.out+p.rows≤cut
  verdict : (repair program a).verdict+1≤cut

theorem bounds (a : Attempt) (x : ℕ) (afterEnd : (A).base c (.attempt a)+(A).stride≤x) : Bounds C a x := by
  let p := profiles a
  let L := (C).layout a
  let T := repair C a
  have finishFit := (fit v s F c initial a).trans afterEnd
  have vend : p.board.verdict+1≤x := (verdict_before p).trans_le finishFit
  have native (b : Pass) (inList : b∈writes L T) : b.out+b.rows≤p.board.verdict := by
    have shape : PostLayout.place L T p.maskStart p.indexBits=T := by rfl
    rw [←shape] at inList
    obtain ⟨i,hi,o,n⟩ := PostLayout.listed L T _ _ b inList
    rw [o,n]
    change PostLayout.startColumns p.maskStart p.indexBits L.candidates+i*L.candidates+L.candidates≤
      PostLayout.startColumns p.maskStart p.indexBits L.candidates+PostLayout.columnsCount T*L.candidates
    have h := Nat.mul_le_mul_right L.candidates (Nat.succ_le_of_lt hi)
    simpa only [Nat.succ_mul,Nat.add_assoc] using Nat.add_le_add_left h
      (PostLayout.startColumns p.maskStart p.indexBits L.candidates)
  have cols : PostLayout.startColumns p.maskStart p.indexBits p.market.rows≤p.board.verdict :=
    Nat.le_add_right ..
  have card := sizes v s F c initial a
  have n := card.1
  have rowsFit : p.market.rows≤2^p.indexBits := by
    rw [card.2.2.2.2.2.1,n]
    change rowFactor s*2^z≤2^(z+rowFactor s)
    rw [Nat.pow_add,Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.le_of_lt (Nat.lt_two_pow_self))
  have bottom : p.testsStart+1≤p.maskStart := by
    unfold Format.maskStart PostLayout.afterTests
    omega
  have fail : p.market.failures.base+p.market.failures.rows≤p.testsStart := by
    have same : p.market.failures.rows=p.market.rows := by cases a <;> rfl
    rw [same,card.2.1,Format.testsStart,card.2.2.2.2.1,n]
    apply Nat.add_le_add_right
    unfold flags first
    exact (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans
      (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have maskHi : p.maskStart+p.market.rows≤x := by
    unfold PostLayout.startColumns at cols
    omega
  have tallyHi : p.maskStart+2^p.indexBits+p.market.rows+2≤x := cols.trans (by omega)
  let tests := (testedBoard p.market.failures p.batch).tests
  let stop := p.testsStart+1
  let limit := stop+(tests.excess.rows+1)+(tests.payload.rows+1)+(tests.discrepancy.rows+1)
  have maskEnd : limit=p.maskStart := rfl
  have ends (n e y d : ℕ) :
      n+e+1≤n+(e+1)+(y+1)+(d+1) ∧
      n+e+1+y+1≤n+(e+1)+(y+1)+(d+1) ∧
      n+e+1+y+1+(d+1)=n+(e+1)+(y+1)+(d+1) := ⟨by omega,by omega,by omega⟩
  obtain ⟨exEnd,pyEnd,dcEnd⟩ := ends stop tests.excess.rows tests.payload.rows tests.discrepancy.rows
  have ex : T.tests.excess.out+T.tests.excess.rows+1≤p.maskStart := calc
    _ = stop+tests.excess.rows+1 := rfl
    _ ≤ limit := exEnd
    _ = _ := maskEnd
  have py : T.tests.payload.out+T.tests.payload.rows+1≤p.maskStart := calc
    _ = stop+tests.excess.rows+1+tests.payload.rows+1 := rfl
    _ ≤ limit := pyEnd
    _ = _ := maskEnd
  have dc : T.tests.discrepancy.out+(T.tests.discrepancy.rows+1)=p.maskStart := calc
    _ = stop+tests.excess.rows+1+tests.payload.rows+1+(tests.discrepancy.rows+1) := rfl
    _ = limit := dcEnd
    _ = _ := maskEnd
  have hi : p.maskStart≤x := by omega
  refine ⟨(bottom.trans hi),?_,ex.trans hi,py.trans hi,dc.le.trans hi,maskHi,?_,tallyHi,
    fun b hb=>(native b hb).trans (by omega),vend⟩
  · change max (p.market.failures.base+p.market.failures.rows) p.testsStart≤x
    exact max_le (by omega) (by omega)
  · change p.maskStart+2^p.indexBits+p.market.rows≤x
    omega

/-- Even a later address which was initialized in the original binary input
survives writes to the current event, including failure, audit and stock scans. -/
theorem past_writes (e : Event) (x : ℕ) (afterEnd : (A).base c e+(A).stride≤x) : outside C x e := by
  cases e with
  | feed b =>
    let L := FeedLayout.atEvent (N:=stageCount) c A profiles initial width cap b
    intro p member
    have bound := L.generated_extent C b rfl p member
    right
    apply bound.trans
    change (A).base c (.feed b)+goods z d k+goods z d k≤x
    have reserves : goods z d k+goods z d k≤(A).stride := by
      change goods z d k+goods z d k≤ stride v s
      unfold stride
      omega
    omega
  | attempt a =>
    let h := bounds (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners a x afterEnd
    refine ⟨Or.inr h.guard,Or.inr h.frozen,Or.inr (by simpa only [Nat.add_assoc] using h.excess),
      Or.inr (by simpa only [Nat.add_assoc] using h.payload),Or.inr h.discrepancy,Or.inr h.mask,?_,
      Or.inr h.verdict,?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl|rest
      · exact ⟨Or.inr h.keys,Or.inr h.tally⟩
      · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp rest
        exact Or.inr (h.writes p hp)
    · exact StockCommit.priced_keeps _ _ _ _ x le_rfl (Or.inr ((fit v s F c initial a).trans afterEnd))

theorem selector_protected (a : Attempt) (x : ℕ) (inBank : x<(A).base c (.attempt a)+q*rows s) :
    protected C x (.attempt a) ∧ outside C x (.attempt a) := by
  have param:=sizes v s F c initial a
  have room : q*rows s≤ selectorSpan s := selector_room s
  have firstArea : x<(profiles a).market.shelf.firstBase := by
    rw [param.2.2.2.1]
    unfold first
    exact inBank.trans_le (((Nat.add_le_add_left room _).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..))
  apply priced_attempt_floor
  · rw [param.2.1]
    omega
  · exact firstArea
  · exact firstArea.trans_le (Format.tests_after_sampler _)

theorem selector_entry (mem atSlot : Memory W) (a : Attempt) {prior tail : List Event}
    (cut : Slot C mem (.attempt a) prior tail atSlot) (x : ℕ) (lo : (A).base c (.attempt a)≤x) :
    atSlot x=mem x := by
  rw [←cut.entry]
  apply run_outside _ _ _ _ cut.prefixReady
  intro e member
  exact past_writes v s F c initial width cap finish prices catalogue banks src tbl dst owners e x
    (((A).apart c (cut.earlier e member)).trans lo)

end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
end

end OAI
