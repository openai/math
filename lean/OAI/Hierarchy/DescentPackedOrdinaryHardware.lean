import OAI.Hierarchy.DescentPackedMatchChooserInput
import OAI.Hierarchy.DescentPackedMatchMachineSize

namespace OAI
/-! # The text and cheap instructions of the complete chooser and matcher -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentSixParty DescentPackedColony DescentColonies ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentStaticWordColumn
noncomputable section

theorem Chooser.Layout.cheap (L : Chooser.Layout) (D k b quota H G M w : ℕ) :
    CheapCode (L.program D k b quota H G M w) := by
  unfold Chooser.Layout.program
  exact @cheap_seq w _ _
    (@PackedCensus.histograms_cheap (L.census k b quota H G M false) (L.census k b quota H G M true)
      L.chart.weights.base L.marked.base H G M w)
    (@Phase.cheap _ _ (L.shelves D k b M) w H G M)

theorem Chooser.Layout.bounded (L : Chooser.Layout) (D k b quota H G M w : ℕ)
    (live : 0<H*chunks G M) : CandidateRAM.Bounded (L.program D k b quota H G M w) (L.ticks D k b quota H G M w) :=
  CandidateRAM.seq_bound (PackedCensus.histograms_storage _ _ _ _ _ _ _ _ live) (Phase.storage _ _ _ _ _ live)

variable {k D cap : ℕ}
variable (s : Shape) (chooser : Chooser.Layout) (C : Prepare.Chart k cap) (Z : DescentSortedRoster.Chart)
  (ports : Ports D) (wins : Fin (2^k)→Bank) (marked : Fin (2^k)→Fin (2*cap)→Bank)
  (romBase base nextBase seats small a K H G M unit w b quota : ℕ)

local notation "firstText" => chooser.program D k b quota H G M w
local notation "secondText" => Prepared.machine s C Z ports wins marked romBase base nextBase seats small a K H G M unit w

theorem ordinary_cheap : CheapCode ((firstText).seq secondText) := by
  refine @cheap_seq w firstText secondText (@Chooser.Layout.cheap chooser D k b quota H G M w) ?_
  unfold Prepared.machine
  refine @cheap_seq w _ _ ?_ ?_
  · exact @cheap_seq w _ _ (@Prepare.ROM.cheap w romBase k D cap a small M H G)
      (@ProtocolRAM.program_cheap w (Prepare.passes C Z base H G M D))
  · unfold Gather.ROM.machine
    refine @cheap_seq w _ _ (@Gather.ROM.cheap s small (2^k) D (2*cap) cap K H G M
      (M*s.pairs) unit w nextBase) ?_
    unfold Gather.complete Gather.all
    exact @cheap_seq w _ _ (@ProtocolRAM.program_cheap w _) (@Hierarchy.DescentPacking.PackedMatch.full_cheap w (M*s.pairs) (K*H) G M _ _)

/-- The original code bank, the two nonuniform literal tables and the dynamic
packed cursor all contribute to the hardware bound. -/
theorem ordinary_names (live : 0<H*chunks G M) (dataWidth volume : ℕ)
    (gate : ((1*2^k)+a)*M≤dataWidth/2) (cables : DescentSignedCableCodec.width D cap*M≤dataWidth/2)
    (keys : unit*M≤dataWidth/2) (pages : 2^(dataWidth/2)≤volume) (hosts : H≤volume)
    (rows : H*chunks G M≤volume) :
    names ((firstText).seq secondText) ≤ 4*chooser.ticks D k b quota H G M w+Prepared.namesPerWord k D cap K*volume := by
  rw [names_seq]
  exact Nat.add_le_add (Chooser.Layout.bounded chooser D k b quota H G M w live).size
    ((Prepared.machine_names s C Z ports wins marked romBase base nextBase seats small a K H G M unit w).trans
      (Prepared.hardware_le k D cap a K H G M unit dataWidth volume gate cables keys pages hosts rows))

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
