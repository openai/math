import OAI.Hierarchy.DescentDatedDonorOutputs
import OAI.Hierarchy.DescentRegisteredMatcherBanks
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Reading all donor operands from the completed ordinary matcher -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentPacking DescentPacking.PackedMatch DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentPackedColony ProtocolRAM
noncomputable section

private theorem below_three_additions (base a b c : ℕ) : base ≤ base+a+b+c :=
  ((Nat.le_add_right base a).trans (Nat.le_add_right _ b)).trans (Nat.le_add_right _ c)

/-- All matcher-produced shelves and the retained actor directory fit before the
following rotation boundary, independently of the contents of the working memory. -/
theorem matcher_output_room (d : DonorDate) (payload seats board : ℕ) (input : Dated.Operands)
    (w floor : ℕ) (safe : (d.schedule payload seats board).Space input w floor) :
    let a:=d.schedule payload seats board
    let b:=d.matcherOutput payload seats input (a.prepareAt input.roster floor)
    let base:=a.rotationEnd input.roster floor
    let n:=(2^(d.exponent+1)*d.hosts)*chunks d.groups (lanes payload d.amount)
    (Gather.assembly b.operands (Gather.expr b.winners b.marked b.peers d.hosts)).Fits w base ∧
      b.gate.base+b.gate.size≤base ∧
      Accessible b.peers input.actors d.hosts d.groups (lanes payload d.amount) w base ∧
      b.topology.base+b.topology.size≤base ∧ b.born.base+b.born.size≤base ∧
      n≤b.topology.size ∧ n≤b.born.size := by
  intro a b base n
  let m:=a.matcher input.roster floor
  let prep:=a.sorterAt input.roster floor
  let next:=a.matcherAt input.roster floor
  let p:=input.ports d.degree
  have seq:=a.subphase_order input floor
  have romPrep : a.prepareAt input.roster floor≤prep := by
    exact below_three_additions _ _ _ _
  have floorPrep := seq.1.trans ((a.phase_before_winners input.roster floor).trans (seq.2.1.trans romPrep))
  have nextRaw : next≤ m.raw.base := below_three_additions _ _ _ _
  have rawSrc : m.raw.base≤ m.source.base := Nat.le_add_right ..
  have srcTop : m.source.base≤ m.layout.topology.base := Nat.le_add_right ..
  have top:= (a.match_banks input floor base w (le_refl _) safe.endAddress).2.2.2
  have endBase : m.endAddr≤base := seq.2.2.2.trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have srcBase : m.source.base≤base := srcTop.trans ((Nat.le_add_right ..).trans top)
  have endRoom : m.endAddr<2^w := endBase.trans_lt safe.endAddress
  have prepAcc:=Chooser.accessible_before p input.actors safe.accessible floorPrep
  obtain ⟨acc,marked,_,_⟩ := Prepare.space (k:=d.exponent) (cap:=d.cap) p prep input.actors prepAcc
    ((nextRaw.trans (rawSrc.trans srcBase)).trans_lt safe.endAddress)
  let field:=Gather.expr b.winners b.marked b.peers d.hosts
  have low (j) : (field j).Fits w next := early_expr b.winners b.marked b.peers next acc marked j
  have packed : d.amount*(lanes payload d.amount)≤w/2 := by
    simpa only [Nat.mul_comm d.amount] using (lanes_fit payload d.amount).trans (Nat.div_le_div_right safe.embed)
  have room:=Gather.ROM.arranged d.matcher d.format.short (2^d.exponent) d.degree (2*d.cap)
    (2^(d.exponent+1)) d.hosts d.groups (lanes payload d.amount) d.amount next seats w
    safe.matchWidth packed endRoom
  have built : (Gather.assembly b.operands field).Fits w m.source.base :=
    Gather.fits b.operands field _ (room.gather field low) _
  have fresh:=acc (0 : Fin (2^d.exponent))
  have afterNext : next≤base := nextRaw.trans (rawSrc.trans srcBase)
  have floorBase : floor≤base := floorPrep.trans (((Nat.le_add_right prep (Prepare.rosterBank prep d.hosts d.degree).size).trans (le_max_right ..)).trans afterNext)
  have access:=Chooser.accessible_before b.peers (b.winners 0) fresh afterNext
  have old:=Chooser.accessible_before p input.actors safe.accessible floorBase
  have flagBase : a.flagEnd input.roster floor≤base := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have gate : b.gate.base+b.gate.size=a.flagEnd input.roster floor := rfl
  have born : b.born.base+b.born.size≤a.flagEnd input.roster floor := by
    let bank:=LayoutSum.Finish.bank d.matcher (lanes payload d.amount) b.topology m.layout.out n
    change bank.base+bank.size≤LayoutSum.Finish.stop d.matcher (lanes payload d.amount) b.topology m.layout.out n
    dsimp only [LayoutSum.Finish.stop,LayoutSum.Finish.chart,LayoutSum.plan,LayoutSum.Finish.base]
    change bank.base+bank.size≤bank.base+bank.size+_+_+2+1
    omega
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ srcBase built,gate.le.trans flagBase,
    ⟨access.ids,access.idsRoom,access.roster,access.rosterRoom,access.offsets,access.offRoom,
      access.chunks,access.chunkRoom,old.source,old.srcRoom⟩,top,born.trans flagBase,
    Gather.ROM.column_size _ _,Nat.le_pow_clog (by decide) _⟩

end
end Hierarchy.DescentSixParty.Chronology.DonorDate

end OAI
