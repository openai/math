import OAI.Hierarchy.ProbeFixedBoards
import OAI.Hierarchy.ProtocolRAMCalendarStripOrigin

namespace OAI
/-! # Concrete chronological repair chart with the public stratum and native reserve operands -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart CatalogueRows
open scoped Fin.CommRing Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)

def seed := originBoards v z width P.routes.directory.keysBase

def publicHeader := v.header (v.seed P z width) P width

def privateArena := v.arena (v.seed P z width) P width

def emptyReserve := outerReserve F (v.sized (v.seed P z width) width) v.cost (v.publicHeader P z width)

/-- The padded economic-header room precedes the additional six terminal
ROMs in the original native event allocation. -/
theorem chargedHeader_le_first :
    (v.emptyReserve P z width).base+(v.emptyReserve P z width).size+
      2^(GlobalTests.bits z (CoreBoard.Stages z (2^v.W)) k) ≤ (v.privateArena P z width).first :=
  Slab.prior_le
    (chargedSlab F (v.sized (v.seed P z width) width) v.cost (v.publicHeader P z width)
      (ProtocolRAMPurchaseSampler.bits v.keepLimit))
    v.mesh z (2^v.W) k (v.sized (v.seed P z width) width).sampler.degree v.depth P.catalogue.rows

theorem emptyReserve_end_le_first :
    (v.emptyReserve P z width).base+(v.emptyReserve P z width).size≤(v.privateArena P z width).first :=
  (Nat.le_add_right ..).trans (v.chargedHeader_le_first P z width)

theorem header_scoreEnd_le_first :
    (v.publicHeader P z width).stop+2^(GlobalTests.bits z (CoreBoard.Stages z (2^v.W)) k)≤
      (v.privateArena P z width).first := by
  let E:=v.publicHeader P z width
  let P':=charges F (v.sized (v.seed P z width) width) v.cost E.stop
  have left : E.stop≤P'.payload.stop := Nat.le_add_right ..
  have right : P'.payload.stop≤P'.stop := Nat.le_add_right ..
  have same : (v.emptyReserve P z width).base=P'.stop := rfl
  have old:=v.chargedHeader_le_first P z width
  change E.stop+_≤_
  omega

/-- Recompile every reserve operand from the genuine parent output. The
stratum directory is shared with the physical purchased-endpoint loader. -/
def nativeBoards :=
  let old:=v.seed P z width
  let s:=v.mounted old P width
  withReserveSource F s v.mesh (v.privateArena P z width) P.joint.initial (v.emptyReserve P z width)

def nativeFormats := formats F v.mesh (v.privateArena P z width) P.joint.initial (v.nativeBoards P z width)

def nativeChart (r : ℕ) (banks : RouteSettlement.Banks) (source table dest : ℕ) (owners : Bank) :=
  StripChart.chart F v.mesh (v.privateArena P z width) P.joint.initial width v.keepLimit (v.nativeBoards P z width)
    v.finish (v.basePhase width) P.catalogue r banks source table dest owners

def nativeTrees := v.physicalTrees (v.seed P z width) P width

private def rowDimensions {z₀ d k₀ q₀ depth : ℕ} (s : StripChart.Boards z₀ d k₀ q₀ depth) : Attempt → ℕ × ℕ
  | .outer p a => ((s.outer p a).maxWidth, (s.outer p a).copies)
  | .inner p a j t => ((s.inner p a j t).maxWidth, (s.inner p a j t).copies)

private theorem compiled_dimensions {q₀ : ℕ} (s : StripChart.Boards z (2^v.W) k q₀ v.depth)
    (a : Attempt) (incoming : ℕ) :
    let f := build F s a incoming
    (f.batch.batch.maxWidth, f.histMass) = rowDimensions s a := by
  cases a <;> rfl

private theorem reserve_dimensions {q₀ : ℕ} (s : StripChart.Boards z (2^v.W) k q₀ v.depth)
    (c : Mesh) (A : Arena) (initial : ℕ) (empty : Bank) (a : Attempt) :
    rowDimensions (withReserveSource F s c A initial empty) a = rowDimensions s a := by
  cases a <;> rfl

theorem ordinary_dimensions (a : Attempt) :
    let f:=v.nativeFormats P z width a
    f.batch.batch.maxWidth=v.menu.maximum ∧ f.histMass=v.menu.copiesAt v.copyScale width := by
  let u:=v.mounted (v.seed P z width) P width
  let actual:=v.nativeBoards P z width
  let base:=resolvedStock v.mesh (v.privateArena P z width) P.joint.initial (build F actual) a
  have fields := reserve_dimensions v z u v.mesh (v.privateArena P z width) P.joint.initial
    (v.emptyReserve P z width) a
  have eqn := ((compiled_dimensions v z actual a base).trans fields).trans
    (compiled_dimensions v z u a base).symm
  have same := v.literal_dimensions (v.seed P z width) P width base a
  exact ⟨(congrArg Prod.fst eqn).trans same.1, (congrArg Prod.snd eqn).trans same.2⟩

theorem parent_reserve (p a j t : ℕ) :
    let outer:=v.nativeFormats P z width (.outer p a)
    ((v.nativeBoards P z width).inner p a j t).reserve.base=outer.pricedArea.output+outer.pricedArea.goods :=
  StripChart.reserve_parent F (v.mounted (v.seed P z width) P width) v.mesh
    (v.privateArena P z width) P.joint.initial (v.emptyReserve P z width) p a j t

theorem outer_reserve (p a : ℕ) : ((v.nativeBoards P z width).outer p a).reserve=v.emptyReserve P z width := rfl

theorem stratum_key (p a : ℕ) : (v.nativeBoards P z width).stratumHeader p a=P.routes.directory.keysBase := rfl

theorem common_clock (r : ℕ) (banks : RouteSettlement.Banks) (source table dest : ℕ) (owners : Bank) :
    (v.nativeChart P z width r banks source table dest owners).mesh=v.mesh := rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
