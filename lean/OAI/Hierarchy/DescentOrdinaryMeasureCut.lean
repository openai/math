import OAI.Hierarchy.DescentScalarBookColumns
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Weakening the native input aperture of the ordinary scalar gather -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentPackedColony DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {D k K cap H G a b M w nb mb K' lo hi : ℕ}

private theorem bank_cut {B : Bank} (fit : B.Fits w lo) (h : lo≤hi) : B.Fits w hi:=
  ⟨fit.1,fit.2.1,fit.2.2.trans h⟩

private theorem ports_cut {P : Ports D} {B : Bank} (fit : Accessible P B H G M w lo) (h : lo≤hi) :
    Accessible P B H G M w hi where
  ids i := bank_cut (fit.ids i) h
  idsRoom := fit.idsRoom
  roster := bank_cut fit.roster h
  rosterRoom := fit.rosterRoom
  offsets := bank_cut fit.offsets h
  offRoom := fit.offRoom
  chunks := bank_cut fit.chunks h
  chunkRoom := fit.chunkRoom
  source := bank_cut fit.source h
  srcRoom := fit.srcRoom

private theorem table_cut {T : Tables} {x y : Expr} (fit : DescentPackedZip.Fits T x y a b M lo w)
    (h : lo≤hi) : DescentPackedZip.Fits T x y a b M hi w :=
  ⟨ProtocolRAMGeneratedWrite.fits_mono x h fit.left,ProtocolRAMGeneratedWrite.fits_mono y h fit.right,
    bank_cut fit.shift h,bank_cut fit.apply h,fit.shiftBits,fit.applyBits⟩

theorem Measured.later_cut {C : Refs D k K cap} {V : Values D k K cap H G a nb mb}
    {m : Memory w} (u : Measured C V K' M lo m) (h : lo≤hi) : Measured C V K' M hi m where
  mounted:=u.mounted
  old:=u.old
  new_:=u.new_
  fromOld i:=ports_cut (u.fromOld i) h
  fromNew x e i:=ports_cut (u.fromNew x e i) h
  dictFits i:=⟨bank_cut (u.dictFits i).1 h,(u.dictFits i).2⟩
  dictionary:=u.dictionary
  wants:=u.wants
  venues:=u.venues
  counts:=u.counts
  targetFits:=table_cut u.targetFits h
  actorFits:=table_cut u.actorFits h
  fieldFits i:=by
    obtain ⟨left,right,apply_,bs,ba⟩:=u.fieldFits i
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ h left,bank_cut right h,bank_cut apply_ h,bs,ba⟩
  emitFits:=table_cut u.emitFits h
  targets:=u.targets
  actors:=u.actors
  fields:=u.fields
  emit:=u.emit

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

end OAI
