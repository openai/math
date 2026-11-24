import OAI.Computability.VPVNP.CompressorShrinkCurrentBranch
import OAI.Computability.VPVNP.CompressorShrinkScheduledGeometry
import OAI.Computability.VPVNP.CompressorShrinkScheduledFinish
import OAI.Computability.VPVNP.CompressorShrinkOutputHeaders
import OAI.Computability.VPVNP.CompressorShrinkOutputCharges

/-! # Running every shrinking visit from the common native selection state

At each reachable level the deterministic prefix leads to one fixed term
input memory. For any admitted selection the following native packet and all
of its deterministic continuations build and publish the actual output graph.
The full suffix has exactly the length prescribed by this script's window.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledRun

open BurstRAM Compression ShrinkBlockInputs BlockPlanner DescriptorSpace SourceOnline
open ShrinkOutput
open scoped Fin.CommRing

private theorem post_before_marker {U : Script} {w : ℕ} (m : Memory w)
    (ps : List (Packet U w)) (mark : Packet U w) (rest : List (Packet U w))
    (input : post m ps = mark.input) :
    post m (ps++mark::rest) = post mark.output rest := by
  rw [post_append,input]
  simp only [post,List.flatMap_cons,SourceWalk.after_append,SourceWalk.Packet.output]

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable (start positions blocks round : ℕ) (live : round < blocks)

/-- The destination level of shrink step `i` in a live block round, one level past its source. -/
def next : Fin (BlockProgram.layout B start positions blocks).levels :=
  ⟨(S.steps+1)*round+i.val+1,by
    change (S.steps+1)*round+i.val+1 < 1+(S.steps+1)*blocks
    have mul := Nat.mul_le_mul_left (S.steps+1) live
    rw [Nat.mul_succ] at mul
    have hi := i.isLt
    omega⟩

/-- The source level of shrink step `i` in a live block round, at offset `i.val` from the
round's first level. -/
def old : Fin (BlockProgram.layout B start positions blocks).levels :=
  ⟨(S.steps+1)*round+i.val,Nat.lt_of_succ_lt ((next B i start positions blocks round live).isLt)⟩

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable {g w : ℕ} (X : GreedyArena.ShrinkingState (a i) g) (base : Word w) (m : Memory w)
variable (fuel cap : ℕ)
local notation "src" => old B i (Fin.val base) positions blocks round live
local notation "dst" => next B i (Fin.val base) positions blocks round live
local notation "L" => BlockProgram.layout B (Fin.val base) positions blocks
local notation "prog" => BlockProgram.script B
local notation "begin₀" => ShrinkForward.first B i round
local notation "count₀" => directoryRows L
local notation "inc" => packedIncidence L w src (DemandRAM.oldCount X)
local notation "origin" => tableBase L src (0 : Fin 6)
local notation "pt" => Workspace.ports (Schedule.arity (Script.catalog prog)) base
local notation "Pkt" => Packet prog w

/-- Every real column used by a pass lies in the descriptor data suffix. -/
theorem column_lower (sites : X.positions ≤ positions) (room : endAddress L < 2^w) (c : Fin 6) :
    levelStart L 0 ≤ ((inc).column c).val := by
  have positionsEq : Fintype.card X.Base*2^(packingLaneBits (a i) g) = X.positions := by
    simp only [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv _),Fintype.card_fin]
  have deg : 2^(a i) ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j)
      (Finset.mem_univ i.castSucc)).trans (le_max_right ..)
  have size : DemandRAM.oldCount X ≤ slotCapacity L := by
    change Fintype.card X.Base*2^(packingLaneBits (a i) g)*2^(a i) ≤ positions*slotDegree S
    rw [positionsEq]; exact Nat.mul_le_mul sites deg
  have endFit := packed_incidence_room L room src size
  have mul := Nat.mul_le_mul_right (DemandRAM.oldCount X) c.isLt.le
  have address : incidenceBase L src (DemandRAM.oldCount X) c < 2^w :=
    (Nat.add_le_add_left mul _).trans_lt endFit
  rw [packed_column]
  change levelStart L 0 ≤ incidenceBase L src (DemandRAM.oldCount X) c % 2^w
  rw [Nat.mod_eq_of_lt address]
  exact (levelStart_mono L (Nat.zero_le _)).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))

variable (common : ShrinkCurrentBranch.Common B f hf i X base.val positions blocks
  (old B i base.val positions blocks round live) (next B i base.val positions blocks round live) m fuel)
variable (sel : SelectedScore.Selection B X) (tape : List Bool)
local notation "chosen" => Classical.choice (common.selected sel)
local notation "selectedPost" => ShrinkBranch.Selected.beforeOutput chosen
local notation "headBank" => PortRefresh.TraversalHeaders.HeadBank

/-- Facts of the physical shrinking interval. Keeping their component types
as parameters also lets the kernel check each large stage separately. -/
structure PacketFacts (G F U N Q W M : Prop) : Prop where
  geometry : G
  finish : F
  suffix : U
  suffixLength : N
  quiet : Q
  whole : W
  final : M

set_option maxHeartbeats 1800000 in
/-- Complete native packets and the physical readbacks needed by the next
level and by the terminal traversal. -/
abbrev Result (pre : List Pkt) (marker : Pkt) (geom p₅ p₆ p₇ p₈ ms tail : List Pkt) (r : TablesRun w) :=
  PacketFacts
    (ShrinkScheduledGeometry.Result B f hf i X sel tape base positions blocks round src dst m fuel
      common.pre chosen cap pre marker geom)
    (ShrinkScheduledFinish.Finish B i X sel base positions blocks round cap selectedPost p₅ p₆ p₇ p₈ ms tail r)
    (Group prog L base cap (begin₀+22) count₀ marker.output (geom++((((p₅++p₆)++p₇)++p₈)++tail)))
    (22 + (geom++((((p₅++p₆)++p₇)++p₈)++tail)).length = (BlockProgram.shrink B i).length)
    (∀ q ∈ geom++((((p₅++p₆)++p₇)++p₈)++tail), ∀ bs ∈ q.stage.choices, bs = [])
    (Group prog L base cap begin₀ count₀ m ((pre++marker::geom)++((((p₅++p₆)++p₇)++p₈)++tail)))
    (post marker.output (geom++((((p₅++p₆)++p₇)++p₈)++tail)) =
      post (post selectedPost (((p₅++p₆)++p₇)++p₈)) tail)

set_option maxHeartbeats 2400000 in
theorem run (fits : ShrinkBranch.PrefixFits B X inc origin (10 : Word w) fuel)
    (heads : headBank L src (DemandRAM.oldCount X) m) (low : ∀ c, levelStart L 0 ≤ ((inc).column c).val)
    (sites : X.positions ≤ positions) (room : endAddress L < 2^w)
    (rows : m (pt).rows.val=(count₀ : Word w)) (pitch : m ((pt).directory-1).val=(levelWords L : Word w))
    (arithmetic : TableArithmetic B i X w)
    (headerClock : ShrinkHeaderGreedyPackets.clock B i ≤ cap)
    (denseClock : scanCap prog (ShrinkBundlePackets.maxFuel B i) ≤ cap)
    (termClock : scanCap prog fuel ≤ cap) (fixedClock : scanCap prog 95 ≤ cap) :
    ∃ pre marker geom p₅ p₆ p₇ p₈ ms tail r,
      Result B i positions blocks round live f hf X base m fuel cap common sel tape pre marker geom p₅ p₆ p₇ p₈ ms tail r := by
  have clock (q : ℕ) (small : q ≤ 95) : scanCap prog q ≤ cap := by
    unfold scanCap at fixedClock ⊢; omega
  obtain ⟨pre,marker,geom,geo⟩ := ShrinkScheduledGeometry.run B f hf i X sel tape base positions blocks round
    src dst m fuel common.pre chosen rfl rfl (common.header sel tape) fits heads low room sites live rows pitch cap
    headerClock denseClock termClock (clock 65 (by decide))
  obtain ⟨p₅,p₆,p₇,p₈,r,out⟩ := ScheduledShrink.output B i X sel base positions blocks round fuel cap common.pre
    chosen fits geo.header geo.oldHeads geo.nextHeads geo.rows geo.pitch live sites room arithmetic fixedClock
  let body := ((p₅++p₆)++p₇)++p₈
  have h := out.tail_inputs live sites room
  obtain ⟨ms,tail,pubs⟩ := ShrinkScheduledTail.run B base positions blocks round cap i X (post selectedPost body)
    inc h.header sites live room h.rows h.pitch (clock 42 (by decide))
  have done := ShrinkScheduledFinish.join B i X sel base positions blocks round cap out pubs
  have intoMarker : post m pre = marker.input := geo.prefixPost.trans geo.selectInput.symm
  have atBody : post marker.output geom = selectedPost :=
    (post_before_marker m pre marker geom intoMarker).symm.trans geo.final
  have offset : (begin₀+22)+geom.length = begin₀+36 := by rw [geo.suffixLength]
  have suffix := geo.suffix.append (show Group prog L base cap ((begin₀+22)+geom.length) count₀
      (post marker.output geom) (body++tail) by
    rw [offset,atBody]; exact done.group)
  have whole := geo.whole.append (by rw [geo.length,geo.final]; exact done.group)
  refine ⟨pre,marker,geom,p₅,p₆,p₇,p₈,ms,tail,r,geo,done,suffix,?_,?_,whole,?_⟩
  · rw [List.length_append,geo.suffixLength]
    have size := done.length
    omega
  · intro q hq bs hb
    rcases List.mem_append.mp hq with hq|hq
    · exact geo.suffixEmpty q hq bs hb
    rcases List.mem_append.mp hq with hq|hq
    · have hbs : bs ∈ body.flatMap (fun z => z.stage.choices) := List.mem_flatMap.mpr ⟨q,hq,hb⟩
      rw [show body.flatMap (fun z => z.stage.choices) = _ from out.tapes] at hbs
      exact (List.mem_replicate.mp hbs).2
    · have hbs : bs ∈ tail.flatMap (fun z => z.stage.choices) := List.mem_flatMap.mpr ⟨q,hq,hb⟩
      rw [pubs.tapes] at hbs
      exact (List.mem_replicate.mp hbs).2
  · rw [post_append,atBody,post_append]

end CompressorRecords.ShrinkScheduledRun

end

end VPVNP
end Computability
end OAI
