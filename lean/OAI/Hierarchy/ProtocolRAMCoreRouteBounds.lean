import OAI.Hierarchy.ProtocolRAMCoreRouteHops
import OAI.Hierarchy.ProtocolRAMStripNativeFits

namespace OAI
/-! # Costs and address bounds for settlement hop readers -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open ProbeStage AdaptiveProbe CoreBoard ReportSockets BoughtSockets CatalogueRows
variable {z W k attempts w : ℕ} {S : PurchaseSampler}

theorem Source.payload_work (s : Source) (e : Fin (PayloadStrip.edgeCount (Stages z (2^W)))) :
    (s.payloadExpr S z W k attempts e).work≤63+8*copies k attempts := by
  let p := payloadPorts S s.catalogue s.columnBase s.remap s.sites s.superBase
    s.oldGroups s.bins s.height z W k attempts
  have cells (c) : (p.column c).work≤56+8*copies k attempts := ColumnROM.payload_work ..
  change (payloadHorizontal S z (2^W) k s.catalogue p.column e none).work≤_
  exact (payloadHorizontal_work S z (2^W) k s.catalogue _ p.column cells e none).trans (by omega)

theorem Source.tile_work (s : Source) (t : StageAt z (2^W)) :
    (s.tileExpr S z W k t).work=7 := rfl

theorem Source.center_work (s : Source) (l : Fin k×Bool) :
    (s.centerExpr S z W k l).work=7 := rfl

theorem Source.quote_work (s : Source) (t : StageAt z (2^W)) (l : Fin k×Bool) :
    (s.quoteExpr S z W k attempts t l).work≤61+8*copies k attempts := by
  unfold Source.quoteExpr
  rw [CoreLookup.field_work]
  have := ColumnROM.payload_work s.columnBase s.remap s.sites s.superBase s.oldGroups s.bins s.height
    k attempts (ColumnROM.PayloadChoice.stage t true)
  omega

structure Safe (s : Source) (S : PurchaseSampler) (z W k attempts w out : ℕ) : Prop where
  word : out<2^w
  core : s.catalogue+CoreLookup.words S z (2^W) k≤ out
  column : ∀c : ColumnROM.PayloadChoice z W,
    (ColumnROM.payloadColumn s.columnBase s.remap s.sites s.superBase s.oldGroups s.bins s.height k attempts c).Fits w out

theorem Safe.payload {s : Source} {out : ℕ} (read : Safe s S z W k attempts w out)
    (e : Fin (PayloadStrip.edgeCount (Stages z (2^W)))) : (s.payloadExpr S z W k attempts e).Fits w out := by
  unfold Source.payloadExpr payloadHorizontal
  split
  · exact ⟨core_bank_fits _ _ read.word read.core,read.column _⟩
  · exact ⟨core_bank_fits _ _ read.word read.core,trivial⟩

theorem Safe.tile {s : Source} {out : ℕ} (read : Safe s S z W k attempts w out)
    (t : StageAt z (2^W)) : (s.tileExpr S z W k t).Fits w out :=
  ⟨core_bank_fits _ _ read.word read.core,trivial⟩

theorem Safe.center {s : Source} {out : ℕ} (read : Safe s S z W k attempts w out)
    (l : Fin k×Bool) : (s.centerExpr S z W k l).Fits w out :=
  ⟨core_bank_fits _ _ read.word read.core,trivial⟩

theorem Safe.quote {s : Source} {out : ℕ} (read : Safe s S z W k attempts w out)
    (t : StageAt z (2^W)) (l : Fin k×Bool) : (s.quoteExpr S z W k attempts t l).Fits w out :=
  ⟨core_bank_fits _ _ read.word read.core,read.column _⟩

theorem safe (base col : ℕ) (v : Directory attempts) (S : PurchaseSampler) (depth K G H out : ℕ)
    (room : out<2^w) (core : base+CoreLookup.words S z (2^W) k≤ out)
    (cols : col+ColumnROM.words z (2^W) k≤ out) (cover : v.Cover S z W k depth K G H out) :
    Safe (addresses base col v.remapBase v.sitesBase v.superBase K G H) S z W k attempts w out :=
  ⟨room,core,fun c=>ColumnROM.payload_fits col v S depth K G H out c room cols cover⟩

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
