import OAI.Computability.BorderVNP.CubeISAOwnedProgram
import OAI.Computability.BorderVNP.CubeISAOwnedStageInverse
import OAI.Computability.BorderVNP.CubeISAOwnedVertexStage

/-! # Full execution of an incident strict symbol row

The RAM reads the same delivered selector and crossing lists for either
incident group. It guesses that group's physical private bits, stores the
two ordered singleton families, and writes the exact three-word directory
records obtained by reading the packet bank that this execution produced.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open Cube Cube.Scatter Physical Physical.Owned Cube.Tally VPVNP.BurstRAM DiagonalResidueRAM Owned

variable {w n d blocks b h K s : ℕ}

/-- Physical addresses and singleton bits for an incident strict row. -/
structure SideData (n d blocks b h : ℕ) where
  /-- Address of the consecutive public powers of the alphabet size. -/
  power : ℕ
  /-- Address of the installed secondary header. -/
  header : ℕ
  /-- Start of the separate ordered singleton banks. -/
  bank : ℕ
  /-- Current append position in the vertex directory. -/
  out : ℕ
  /-- Actual routed singleton values for both orientations. -/
  value : Label (n+1) d × Label (n+1) d → Fin (blocks*(h*b)) → Bool

variable (D : PacketRowData n d blocks b h K s) (A : SideData n d blocks b h)

/-- The three physical memory updates before writing the directory. -/
def scattered (m : Memory w) : Memory w :=
  let p := D.before m (packetTrials n d blocks)
  let a := D.singletonRow D.pair.val.1 D.pair.val.2 A.bank p.sel p.cross A.value
  let e := a.before p.mem (singlePairTrials n d)
  let c := D.singletonRow D.pair.val.2 D.pair.val.1 A.bank p.sel e.1 A.value
  (c.before e.2 (singlePairTrials n d)).2

/-- Number of native instructions needed for the packet and ordered singleton
scatters, both orientation swaps, and the directory traversal. -/
def sideCost : ℕ :=
  let a := D.singletonRow D.pair.val.1 D.pair.val.2 A.bank 0 0 A.value
  let c := D.singletonRow D.pair.val.2 D.pair.val.1 A.bank 0 0 A.value
  packetStageCost n d blocks b h K s + (singleStageCost a+(3+(singleStageCost c+3))) +
    vertexStageCost n d blocks b h K s

/-- All real words, operands and disjoint addressed ranges needed by the native program. -/
structure SideReady (pub : Arg → Word w) (src : Set ℕ) (r : Bank w) (m : Memory w) : Prop where
  entry : Entry D.axis D.pair.val.1 D.pair.val.2 r
  group : readings r 3 = (if D.high then D.pair.val.2 else D.pair.val.1).val
  sel : r 36 = word w D.selector
  cross : r 37 = word w D.crossing
  output : readings r 7 = A.out
  stride : D.stride = bankWidth n b h K s
  loaded : (layout D A.power A.header).Loaded n (readings pub) (readings m)
  fit : PacketRoom (layout D A.power A.header) w n b h K s (pub 0).val
  singleFit : SingleRoom w n d (blocks*(h*b)) (pub 0).val A.bank
  protect : Protected (layout D A.power A.header) n (pub 0).val src
  frameZ : (pub 0).val+56 ∈ src
  frameBank : (pub 0).val+88 ∈ src
  zAt : readings m ((pub 0).val+56) = d^(n+1)
  bankAt : readings m ((pub 0).val+88) = A.bank
  sels : Resident src m D.selector (commonSelectors D.select D.axis D.pair)
  crosses : Resident src m D.crossing (commonCrossings b D.axis D.pair D.select D.supply (fun z => A.value z.1.val z.2))
  packetDest : ∀ p : Packet n d blocks, p.1.1 D.axis = D.pair → ∀ j < bankWidth n b h K s,
    OwnedVertex.bankAt D.base D.stride p+j ∉ src ∧ OwnedVertex.bankAt D.base D.stride p+j < 2^w
  singleDest : ∀ u v : Label (n+1) d, ∀ j < blocks*(h*b),
    let addr := singleBase A.bank (d^(n+1)) (blocks*(h*b)) (finFunctionFinEquiv u).val (finFunctionFinEquiv v).val+j
    addr ∉ src ∧ addr < 2^w
  packetsBeforeSingletons : D.base+(d*d)^(n+1)*2*blocks*D.stride ≤ A.bank
  singletonsBeforeDirectory : A.bank+d^(n+1)*d^(n+1)*(blocks*(h*b)) ≤ A.out
  directoryRoom : A.out+(2*blocks*(d.choose 2)^n)*(3*2^n) < 2^w

/-- Exact outer control registers, two stream cursors, dense directory append
position and the full memory, including all previous directory words. -/
structure SideResult (src : Set ℕ) (r : Bank w) (m : Memory w) (t : Bank w) (mt : Memory w) : Prop where
  keep : ∀ j, Control j → j ≠ 7 → t j = r j
  selector : t 36 = word w (D.selector+(commonSelectors D.select D.axis D.pair).length)
  crossing : t 37 = word w (D.crossing+(commonCrossings b D.axis D.pair D.select D.supply (fun z => A.value z.1.val z.2)).length)
  output : readings t 7 = A.out+(2*blocks*(d.choose 2)^n)*(3*2^n)
  image : readings mt = (OwnedVertex.rowImage (blocks := blocks) D.axis D.pair D.high D.base D.stride
    (selectorWidth n K h) A.out (readings (scattered D A m)) (packetTrials n d blocks)).2
  source : ∀ j ∈ src, j < A.out → mt j = m j
  above : ∀ j ∈ src, A.out+(2*blocks*(d.choose 2)^n)*(3*2^n) ≤ j → mt j = m j

/-- All packet selector words survive both later singleton passes. -/
theorem scattered_stored (m : Memory w) (positive : 1 < 2^w) (stride : bankWidth n b h K s ≤ D.stride)
    (separate : D.base+(d*d)^(n+1)*2*blocks*D.stride ≤ A.bank) (p : Packet n d blocks) (hp : p.1.1 D.axis = D.pair) :
    SelectorRead.Stored (readings (scattered D A m)) (OwnedVertex.bankAt D.base D.stride p) (D.select p) := by
  let t := (packetRowEquiv D.axis D.pair).symm ⟨p,hp⟩
  have he : (packetRowEquiv D.axis D.pair t).val = p := congrArg Subtype.val (Equiv.apply_symm_apply ..)
  have idx := trialPacketIndex_lt D.axis D.pair t.val
  rw [trialPacketIndex_eq D.axis D.pair t,he] at idx
  have step := Nat.mul_le_mul_right D.stride idx
  change (packetIndex p+1)*D.stride ≤ _ at step
  rw [Nat.add_mul,one_mul] at step
  have width : selectorWidth n K h ≤ D.stride := by unfold bankWidth supplyBase at stride; omega
  intro j
  have below : OwnedVertex.bankAt D.base D.stride p+j.val < A.bank := by
    unfold OwnedVertex.bankAt
    have bound := j.isLt
    omega
  unfold scattered readings
  rw [SingleRowData.before_below_bank _ _ _ _ below,SingleRowData.before_below_bank _ _ _ _ below]
  exact D.final_stored m positive stride p hp j

/-- On each incident side, the native row realizes the prescribed physical
private choices and appends the records for exactly its owned half-cubes. -/
theorem strictSide_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (r : Bank w) (m : Memory w) (ready : SideReady D A pub src r m) :
    TraceRun pub mac (strictSide n b h K s) r m (rowChoices packetTrialValid D.choices) (sideCost D A)
      (SideResult D A src r m) := by
  let np := packetTrials n d blocks
  let ns := singlePairTrials n d
  let ep := D.before m np
  let a := D.singletonRow D.pair.val.1 D.pair.val.2 A.bank ep.sel ep.cross A.value
  let ea := a.before ep.mem ns
  let c := D.singletonRow D.pair.val.2 D.pair.val.1 A.bank ep.sel ea.1 A.value
  let ec := c.before ea.2 ns
  let l := layout D A.power A.header
  have start := strictScatter_run D pub mac src r m A.power A.header A.bank A.value ready.entry ready.group
    ready.sel ready.cross ready.stride ready.loaded ready.fit ready.singleFit ready.protect ready.frameZ ready.frameBank
    ready.zAt ready.bankAt ready.sels ready.crosses ready.packetDest ready.singleDest
  change TraceRun pub mac (strictScatter n b h K s) r m
    (rowChoices packetTrialValid D.choices ++ (rowChoices a.selected a.localBits ++ rowChoices c.selected c.localBits)) _ _ at start
  rw [strictChoices a D.pair.property.ne,strictChoices c D.pair.property.ne',List.append_nil,List.append_nil] at start
  have run := start.seq (Q := SideResult D A src r m) (fun u mu ⟨keep,hs,hc,hm,ending,unchanged⟩ => by
    have hu : mu = scattered D A m := hm
    have positive : 1 < 2^w := by have := ready.fit.layout.primary; omega
    have stored := scattered_stored D A m positive ready.stride.ge ready.packetsBeforeSingletons
    have bound : D.base+(d*d)^(n+1)*2*blocks*D.stride ≤ A.out :=
      ready.packetsBeforeSingletons.trans ((Nat.le_add_right ..).trans ready.singletonsBeforeDirectory)
    apply (vertexStage_run l D pub mac u mu A.out (ready.entry.keep keep) ((congrArg Fin.val (keep 3 (by decide))).trans ready.group)
      (ready.protect.loaded ready.loaded unchanged) ready.fit rfl ready.stride ((congrArg Fin.val (keep 7 (by decide))).trans ready.output)
      bound ready.directoryRoom (hu ▸ stored)).mono le_rfl
    rintro t mt ⟨rest,h36,h37,output,image⟩
    have low := (OwnedVertex.rowImage_frame (blocks := blocks) D.axis D.pair D.high D.base D.stride
      (selectorWidth n K h) A.out (readings mu) np).2
    have high := OwnedVertex.rowImage_above (blocks := blocks) D.axis D.pair D.high D.base D.stride
      (selectorWidth n K h) A.out (readings mu) np
    dsimp only at high
    rw [OwnedVertex.rowImage_cursor,OwnedVertex.selectedPrefix_end] at high
    exact ⟨fun j hj h7 => (rest j hj h7).trans (keep j hj),
      h36.trans (hs.trans (congrArg (word w) (D.final_cursors m).1)),
      h37.trans (hc.trans (congrArg (word w) ending)),output,hu ▸ image,
      fun j hj hlow => Fin.ext (((congrFun image j).trans (low j hlow)).trans (congrArg Fin.val (unchanged j hj))),
      fun j hj hhigh => Fin.ext (((congrFun image j).trans (high j hhigh)).trans (congrArg Fin.val (unchanged j hj)))⟩)
  have ticks : packetStageCost n d blocks b h K s +
      (singleStageCost a+(3+(singleStageCost c+3))) + vertexStageCost n l.d l.blocks b h K s = sideCost D A := rfl
  change TraceRun pub mac (strictSide n b h K s) r m (_ ++ []) (packetStageCost n d blocks b h K s +
    (singleStageCost a+(3+(singleStageCost c+3))) + vertexStageCost n l.d l.blocks b h K s) _ at run
  rwa [List.append_nil,ticks] at run

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
