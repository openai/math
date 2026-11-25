import OAI.ThreeFlat.Diagonal.PhysicalSeedLayer

namespace OAI
/-! # Scalar seeds appearing in the compact node header -/

namespace Hierarchy.TraceSeedWriter
open ThreeFlat.Diagonal.NavigationPass

structure LayerWords (A : Archive) (axes W : ℕ) : Prop where
  first : A.seedLayer.first=0
  count : A.seedLayer.count=axes*2^axes
  kind : A.seedLayer.kind=0
  childCount : A.seedLayer.childCount=0
  children : A.seedLayer.children=0
  kernels : A.seedLayer.kernels<2^W
  incident : A.seedLayer.incident<2^W
  info : A.seedLayer.info<2^W
  extent : A.seedLayer.first+A.seedLayer.count<2^W

end Hierarchy.TraceSeedWriter

end OAI
