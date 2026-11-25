import OAI.Hierarchy.ProtocolRAMCalendarStripHeader
import OAI.Hierarchy.ProtocolRAMStripColumnPrograms

namespace OAI
/-! # Native address banks for the two strip programs -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard BoughtSockets
open StripDirectory CatalogueRows
open scoped Classical Fin.CommRing
variable {z W k q depth : ℕ}

def birth (c : Mesh) (p a : ℕ) := a+c.outerFuel*p

theorem birth_ordinal (c : Mesh) (p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel) :
    birth c p.val a.val=(finProdFinEquiv (p,a)).val := rfl

structure PortBanks (jobs : ℕ) where
  directory : BoughtSockets.Directory jobs
  core : ℕ
  column : ℕ
  oldGroups : ℕ
  bins : ℕ
  height : ℕ

variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
  (G : PortBanks ((c.inject+c.cool)*c.outerFuel))

def payloadPortsAt := payloadPorts s.sampler G.core G.column G.directory.remapBase
  G.directory.sitesBase G.directory.superBase G.oldGroups G.bins G.height z W k ((c.inject+c.cool)*c.outerFuel)

def boughtPortsAt (p a : ℕ) := purchasePorts b G.directory (s.outer p a).market.shelf
  s.sampler G.core G.column (s.stratumHeader p a) G.oldGroups G.bins G.height z W k depth (birth c p a)

/-- The original public width and the later archived edge label are determined
by the physical CT geometry at the same originating outer trial. -/
def withPorts : Boards z (2^W) k q depth :=
  { s with
    payloadEdge := fun _ _ => payloadEdge (payloadPortsAt s c G) b
    purchaseEdge := fun p a _ _ => purchaseEdge (boughtPortsAt s c b G p a) b }

end Hierarchy.ProtocolRAM.Calendar.StripChart

end

end OAI
