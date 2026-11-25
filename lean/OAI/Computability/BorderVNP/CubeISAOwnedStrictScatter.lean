import OAI.Computability.BorderVNP.CubeISAOwnedPacketStage
import OAI.Computability.BorderVNP.CubeISAOwnedDoubleStage
import OAI.Computability.BorderVNP.CubeScatterCommonPrepared

/-! # All three scatters at one incident side of a strict group row

The copied common words supply every routed bit in public packet order
followed by both ordered singleton families. The two oriented passes
restore the symbol registers before the vertex-directory pass.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open Cube Cube.Scatter Physical Physical.Owned Cube.Tally VPVNP.BurstRAM DiagonalResidueRAM Owned

variable {w n d blocks b h K s : ℕ} (D : PacketRowData n d blocks b h K s)

/-- Layout of one complete physical row under the installed frame and power table. -/
def layout (power header : ℕ) : OwnedRowSetup.Layout :=
  ⟨d,blocks,h*b,power,header,D.base⟩

/-- Packet scatter followed by both ordered singleton passes. -/
def strictScatter (n b h K s : ℕ) : Code := .seq (packetStage n b h K s) (doubleStage n)

/-- Data and allocation bounds for the singleton reservation and the real source words. -/
structure SingleRoom (w n d len frame bank : ℕ) : Prop where
  /-- Highest primary singleton frame operand. -/
  frameFit : frame+88 < 2^w
  /-- All product label-pair keys fit. -/
  keys : d^(n+1)*d^(n+1) ≤ 2^w
  /-- The whole singleton output interval, including its sentinel. -/
  allocation : bank+d^(n+1)*d^(n+1)*len < 2^w

/-- The full native scatter starting from the routed strict-row lists. Every
call consumes the correct private choices and the end of the crossing stream
is the actual end of the common list. -/
theorem strictScatter_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (r : Bank w) (m : Memory w) (power header bank : ℕ)
    (value : Label (n+1) d × Label (n+1) d → Fin (blocks*(h*b)) → Bool)
    (entry : Entry D.axis D.pair.val.1 D.pair.val.2 r)
    (group : readings r 3 = (if D.high then D.pair.val.2 else D.pair.val.1).val)
    (sel : r 36 = word w D.selector) (cross : r 37 = word w D.crossing)
    (stride : D.stride = bankWidth n b h K s)
    (loaded : (layout D power header).Loaded n (readings pub) (readings m))
    (fit : PacketRoom (layout D power header) w n b h K s (pub 0).val)
    (singleFit : SingleRoom w n d (blocks*(h*b)) (pub 0).val bank)
    (protect : Protected (layout D power header) n (pub 0).val src)
    (frameZ : (pub 0).val+56 ∈ src) (frameBank : (pub 0).val+88 ∈ src)
    (zAt : readings m ((pub 0).val+56) = d^(n+1)) (bankAt : readings m ((pub 0).val+88) = bank)
    (sels : Resident src m D.selector (commonSelectors D.select D.axis D.pair))
    (crosses : Resident src m D.crossing (commonCrossings b D.axis D.pair D.select D.supply (fun z => value z.1.val z.2)))
    (packetDest : ∀ p : Packet n d blocks, p.1.1 D.axis = D.pair → ∀ j < bankWidth n b h K s,
      OwnedVertex.bankAt D.base D.stride p+j ∉ src ∧ OwnedVertex.bankAt D.base D.stride p+j < 2^w)
    (singleDest : ∀ u v : Label (n+1) d, ∀ j < blocks*(h*b),
      let addr := singleBase bank (d^(n+1)) (blocks*(h*b)) (finFunctionFinEquiv u).val (finFunctionFinEquiv v).val+j
      addr ∉ src ∧ addr < 2^w) :
    let N := singlePairTrials n d
    let endP := D.before m (packetTrials n d blocks)
    let first := D.singletonRow D.pair.val.1 D.pair.val.2 bank endP.sel endP.cross value
    let endA := first.before endP.mem N
    let second := D.singletonRow D.pair.val.2 D.pair.val.1 bank endP.sel endA.1 value
    let endB := second.before endA.2 N
    TraceRun pub mac (strictScatter n b h K s) r m
      (rowChoices packetTrialValid D.choices ++ (rowChoices first.selected first.localBits ++
        rowChoices second.selected second.localBits))
      (packetStageCost n d blocks b h K s+(singleStageCost first+(3+(singleStageCost second+3)))) (fun t mt =>
        Keeps r t ∧ t 36 = word w endP.sel ∧ t 37 = word w endB.1 ∧ mt = endB.2 ∧
        endB.1 = D.crossing+(commonCrossings b D.axis D.pair D.select D.supply (fun z => value z.1.val z.2)).length ∧
        ∀ j ∈ src, mt j = m j) := by
  intro N endP first endA second endB
  obtain ⟨pReady,aReady,bReady,fullEnd,unchanged⟩ := D.strictRows_prepared src m bank value sels crosses packetDest singleDest
  have prefixRun := packetStage_run (layout D power header) D pub mac src r m entry group sel cross loaded fit
    rfl stride pReady
  let post (t : Bank w) (mt : Memory w) := Keeps r t ∧ t 36 = word w endP.sel ∧ t 37 = word w endB.1 ∧
    mt = endB.2 ∧ endB.1 = D.crossing+(commonCrossings b D.axis D.pair D.select D.supply (fun z => value z.1.val z.2)).length ∧
    ∀ j ∈ src, mt j = m j
  apply prefixRun.seq (Q := post)
  rintro u mu ⟨keep,h36,h37,hm⟩
  subst mu
  have source j hj := D.before_source m pReady (packetTrials n d blocks) j hj
  have load := protect.loaded loaded source
  have secondRun := doubleStage_run pub mac (layout D power header) first second src u endP.mem
    (entry.keep keep) rfl rfl rfl rfl rfl rfl h36 h37 load fit.layout protect aReady bReady frameZ frameBank
    ((congrArg Fin.val (source _ frameZ)).trans zAt) ((congrArg Fin.val (source _ frameBank)).trans bankAt)
    singleFit.frameFit singleFit.keys singleFit.allocation
  apply secondRun.mono le_rfl
  rintro t mt ⟨rest,rs,rc,mem⟩
  exact ⟨fun j hj => (rest j hj).trans (keep j hj),rs,rc,mem,fullEnd,fun j hj =>
    (congrFun mem j).trans (unchanged j hj)⟩

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
