import OAI.Computability.BorderVNP.CubeISAOwnedRowSetupPacket
import OAI.Computability.BorderVNP.CubeISAOwnedRowSelectors
import OAI.Computability.BorderVNP.CubeISAOwnedStageFrame

/-! # Packet scatter and vertex stages from the installed side of an owned row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open Cube Cube.Scatter Cube.Physical.Owned Cube.Tally DiagonalResidueRAM VPVNP.BurstRAM Owned OwnedVertex

variable {w n b h K s : ℕ} (l : OwnedRowSetup.Layout)
variable (D : PacketRowData n l.d l.blocks b h K s)

/-- Fixed native packet scatter including its register initialization. -/
def packetStage (n b h K s : ℕ) : Code :=
  .seq (OwnedRowSetup.packet n b h K s) (rowLoop (packetCandidate n) (ownedPacket n b h K s))

/-- Cost of initializing and traversing the packet candidates with their actual callback. -/
def packetStageCost (n d blocks b h K s : ℕ) : ℕ :=
  (OwnedRowSetup.packet n b h K s).slots +
    ((∑ t : Fin (packetTrials n d blocks), (6*n+22 + if packetTrialValid t then ownedPacketCost n b h K s else 1))+1)

/-- Common word-fit conditions for both the packet scatter and the later vertex pass. -/
structure PacketRoom (l : OwnedRowSetup.Layout) (w n b h K s frame : ℕ) : Prop where
  /-- Frame addresses and local mixed-radix operands. -/
  layout : l.Fits w n frame
  /-- Local packet counter bound fits. -/
  trials : packetTrials n l.d l.blocks < 2^w
  /-- Selector and physical vertex ranges fit the actual machine word. -/
  keys : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w
  /-- The fixed packet bank stride fits the machine word. -/
  stride : bankWidth n b h K s < 2^w
  /-- The packet bank has at least one physical position. -/
  positive : 0 < bankWidth n b h K s
  /-- The exclusive end of the full stable packet bank. -/
  bank : l.bank+(l.d*l.d)^(n+1)*2*l.blocks*bankWidth n b h K s ≤ 2^w

/-- Scalar and memory effects of the real setup, including all inputs subsequently
consumed by the packet scatter and the vertex-directory callback. -/
theorem preparePacketStage (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (entry : Entry D.axis D.pair.val.1 D.pair.val.2 r)
    (group : readings r 3 = (if D.high then D.pair.val.2 else D.pair.val.1).val)
    (loaded : l.Loaded n (readings pub) (readings m)) (fit : PacketRoom l w n b h K s (pub 0).val)
    (base : D.base = l.bank) (stride : D.stride = bankWidth n b h K s) :
    TraceRun pub mac (OwnedRowSetup.packet n b h K s) r m [] (OwnedRowSetup.packet n b h K s).slots
      (fun t mt => packetReady (blocks := l.blocks) D.axis D.pair D.stride D.base 0 (.ofWords t mt) ∧
        readings t 3 = (if D.high then D.pair.val.2 else D.pair.val.1).val ∧
        readings t 5 = n ∧ readings t 8 = selectorWidth n K h ∧
        readings t 9 = Fintype.card (Selector n K h) ∧
        (∀ j, OwnedRowSetup.Held j → readings t j = readings r j) ∧ mt = m) := by
  have count : Fintype.card (Selector n K h) < 2^w := (le_max_left ..).trans_lt fit.keys
  have width : selectorWidth n K h < 2^w := (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)).trans_lt count
  apply (traceRun_unsigned (OwnedRowSetup.packet_run pub mac r m l D.axis D.pair b h K s loaded fit.layout
    fit.trials width count fit.stride entry.zero entry.one entry.axis entry.left entry.right)
    (OwnedRowSetup.packet_unsigned n b h K s)).mono le_rfl
  rintro t mt ⟨ready,dim,bits,choices,keep,memory⟩
  refine ⟨stride ▸ base ▸ ready,(keep 3 (by decide)).trans group,dim,bits,choices,keep,?_⟩
  exact funext fun j => Fin.ext (congrFun memory j)

/-- A strict-side packet scatter entered directly from the outer symbol pair.
Only actual selected packets supply private choices or update the bank. -/
theorem packetStage_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (r : Bank w) (m : Memory w) (entry : Entry D.axis D.pair.val.1 D.pair.val.2 r)
    (group : readings r 3 = (if D.high then D.pair.val.2 else D.pair.val.1).val)
    (sel : r 36 = word w D.selector) (cross : r 37 = word w D.crossing)
    (loaded : l.Loaded n (readings pub) (readings m)) (fit : PacketRoom l w n b h K s (pub 0).val)
    (base : D.base = l.bank) (stride : D.stride = bankWidth n b h K s)
    (prepared : D.PreparedRow src m) :
    TraceRun pub mac (packetStage n b h K s) r m (rowChoices packetTrialValid D.choices)
      (packetStageCost n l.d l.blocks b h K s) (fun t mt =>
        let z := D.before m (packetTrials n l.d l.blocks)
        Keeps r t ∧ t 36 = word w z.sel ∧ t 37 = word w z.cross ∧ mt = z.mem) := by
  let z := D.before m (packetTrials n l.d l.blocks)
  let post (t : Bank w) (mt : Memory w) := Keeps r t ∧ t 36 = word w z.sel ∧ t 37 = word w z.cross ∧ mt = z.mem
  have first := preparePacketStage l D pub mac r m entry group loaded fit base stride
  have run := first.seq (Q := post) (fun u mu hi => by
    obtain ⟨ready,owner,dim,bits,card,keep,hm⟩ := hi
    subst mu
    have en : D.Entry u m := ⟨ready,owner,(keep 4 (by decide)).trans entry.axis,dim,bits,card,
      (Fin.ext (keep 36 (by decide))).trans sel,(Fin.ext (keep 37 (by decide))).trans cross⟩
    have low : selectorWidth n K h ≤ D.stride := by rw [stride]; unfold bankWidth supplyBase; omega
    have bank : D.base+(l.d*l.d)^(n+1)*2*l.blocks*D.stride ≤ 2^w := by rw [base,stride]; exact fit.bank
    apply (D.scatterRow_run pub mac src u m en prepared (stride ▸ fit.positive) low bank fit.keys).mono le_rfl
    intro t mt result
    exact ⟨keeps_setup_loop keep result.low,result.selector,result.crossing,result.memory⟩)
  simpa only [packetStage,packetStageCost,post,z,List.nil_append] using run

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
