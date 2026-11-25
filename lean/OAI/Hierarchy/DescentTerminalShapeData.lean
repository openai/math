import Mathlib.Data.Nat.Basic

namespace OAI
/-! # Public dimensions of the three terminal phases -/

namespace Hierarchy.DescentTerminalDataPlane
structure Shape where
  exteriors : ℕ
  headBits : ℕ
  restBits : ℕ
  bitLanes : ℕ
  rawRows : ℕ
  publicRows : ℕ
  headerRows : ℕ
end Hierarchy.DescentTerminalDataPlane

namespace Hierarchy.DescentTerminalEmitter
structure Shape where
  plane : DescentTerminalDataPlane.Shape
  pool : ℕ
  rows : ℕ
  leaves : ℕ
end Hierarchy.DescentTerminalEmitter

namespace Hierarchy.DescentTerminalCompiledPrefix
structure Shape where
  nodes : ℕ
  batch : ℕ
  piece : ℕ
  sites : ℕ
  sites_pos : 0<sites
  terminal : DescentTerminalEmitter.Shape
end Hierarchy.DescentTerminalCompiledPrefix

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
def exteriorShape (template : DescentTerminalCompiledPrefix.Shape)
    (exteriors headBits tailBits lanes hiddenWords widthHeaders numSites : ℕ) (sitePos : 0 < numSites) :
    DescentTerminalCompiledPrefix.Shape :=
  {template with sites:=numSites,sites_pos:=sitePos,terminal:={template.terminal with
    plane:=⟨exteriors,headBits,tailBits,lanes,hiddenWords,exteriors*2^(headBits+tailBits),widthHeaders⟩}}
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
