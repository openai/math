import OAI.Hierarchy.ProbeFixedPurchaseHeaderFits
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost
import OAI.Hierarchy.ProtocolRAMCalendarPostResources
import OAI.Hierarchy.TaggedWidePlacement

namespace OAI
/-! # Uniform text of the true historical purchase-header fields -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open AdaptiveProbe ProbeStage ProbeStage.Native ProbeStage.CoreBoard PurchaseFrozen BoughtSockets ReportSockets
variable {z W k letters depth : ℕ} (s : Boards z (2^W) k letters depth) (c : Mesh)
    (b : CatalogueRows.Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))

def headerWork (d k attempts : ℕ) : ℕ :=
  50+(4+ReportSockets.copies k attempts)*(selectWork ((2*rounds d+1)*(2*k)) 19+1)

theorem purchase_header_work (p a : ℕ) :
    PostResources.LinkCaps (purchaseHeader s c b G p a)
      (headerWork (2^W) k ((c.inject+c.cool)*c.outerFuel)) := by
  let jobs:=(c.inject+c.cool)*c.outerFuel
  let U:=selectWork (count z (2^W) k) 19
  let copies:=ReportSockets.copies k jobs
  have big : U+5≤50+(4+copies)*(U+1):=by rw [Nat.add_mul];omega
  have cap : headerWork (2^W) k jobs=50+(4+copies)*(U+1):=by simp only [headerWork,U,copies,count_eq]
  unfold purchaseHeader
  dsimp only
  split
  next before=>
    let i : Fin jobs:=⟨birth c p a,before⟩
    let f:=fun side=>event G.directory.remapBase (s.stratumHeader p a) (s.outer p a).market.shelf s.sampler z (2^W) k depth i side
    have field (side : Bool) : (f side).group.work≤U ∧ (f side).port.work≤U ∧ (f side).tag.work≤U :=
      event_work G.directory.remapBase (s.stratumHeader p a) depth (s.outer p a).market.shelf s.sampler i side
    have atPort (side : Bool) : (SiteROM.atPort G.directory.sitesBase G.bins G.height G.directory.superBase
        G.oldGroups copies (f side).group (f side).port (f side).tag).work≤50+(4+copies)*(U+1) := by
      obtain ⟨hg,hp,ht⟩:=field side
      have scaled:=Nat.mul_le_mul_left copies (Nat.add_le_add_right hp 1)
      simp only [SiteROM.atPort,SiteROM.siteExpr,addressExpr,Expr.work,ProtocolRAM.scale_work,Nat.one_mul]
      rw [Nat.add_mul]
      omega
    have group : (f false).group.work+5≤headerWork (2^W) k jobs:=
      ((Nat.add_le_add_right (field false).1 5).trans big).trans_eq cap.symm
    exact ⟨group,(atPort false).trans_eq cap.symm,(atPort true).trans_eq cap.symm,
      (show 1≤headerWork (2^W) k jobs by rw [cap];omega)⟩
  next =>
    have one : 1≤headerWork (2^W) k jobs:=by rw [cap];omega
    exact ⟨one,one,one,one⟩

theorem purchase_key_work (p a : ℕ) : (purchaseKey s p a).work=9 := rfl
end Hierarchy.ProtocolRAM.Calendar.StripChart

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage ProbeStage.Native StripChart
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

theorem purchase_field_work (P : v.Placement) (h width : ℕ) (a : Attempt) :
    let f:=v.nativeFormats P h width a
    let K:=headerWork (2^v.W) k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)
    PostResources.LinkCaps f.board.purchaseLink K ∧ f.board.purchaseMenu.work≤K := by
  intro f K
  let geo:=v.located (v.seed P h width) P width
  let labelled:=withPorts geo v.mesh P.catalogue P.routes
  have bound : 9≤K:=by dsimp only [K,headerWork];omega
  cases a with
  | outer p a=>
    have got:=purchase_header_work labelled v.mesh P.catalogue P.routes p a
    have menu:=(purchase_key_work labelled p a).le.trans bound
    exact ⟨⟨got.group,got.endpoint,got.opposite,(show 1≤K by omega)⟩,menu⟩
  | inner p a j t=>
    have got:=purchase_header_work labelled v.mesh P.catalogue P.routes p a
    have menu:=(purchase_key_work labelled p a).le.trans bound
    exact ⟨⟨got.group,got.endpoint,got.opposite,(show 1≤K by omega)⟩,menu⟩

theorem wide_purchase_field_work : ∃U:ℕ,∀h width a,
    let f:=v.nativeFormats (v.widePlacement h width) h width a
    PostResources.LinkCaps f.board.purchaseLink U ∧ f.board.purchaseMenu.work≤U :=
  ⟨headerWork (2^v.W) k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel),
    fun h width a=>v.purchase_field_work (v.widePlacement h width) h width a⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
