import OAI.Computability.VPVNP.PairShrinkRoleMapStart
import OAI.Computability.VPVNP.PairShrinkCallFrameLive
import OAI.Computability.VPVNP.PairShrinkSiteBank

/-! # Concrete operands at the first resident map of a shrinking site -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM VertexImage Compression CompressorRecords
open ShrinkVertexImage ShrinkMapImage.Registers MapResidentInputs MapResidentRows
open scoped Fin.CommRing

variable {w p r n : ℕ}

/-- Operands left by the map reload and header, before the first motif ID is read.
The published term row and its stride accompany the five live gather inputs. -/
structure SiteMapInput (common : Fin 24 ↪ Fin r) (dfs : Fin 9 ↪ Fin r)
    (R : LeafArena.Regions) (n : ℕ) (node level term : Word w)
    (expected : Word w → Word w) (c : Config w p r) : Prop where
  node : c.reg (common 0) = node
  level : c.reg (common 11) = level
  geometry : c.reg (common 9) = (NativeFrame.frameBase R : Word w)
  histogram : c.reg (common 10) = (R.histBase : Word w)
  hidden : c.reg (common 8) = (ShrinkCallABI.hiddenBase R n : Word w)
  term : c.reg (common 16) = term
  stride : c.reg (common 17) = 10
  one : c.reg (common 22) = 1
  endWord : c.reg (dfs 6) = (n : Word w)
  memory : c.privateMem = expected

/-- The six-party programs use these five public operands at every row of this site. -/
theorem SiteMapInput.pub_eq {common : Fin 24 ↪ Fin r} {dfs : Fin 9 ↪ Fin r}
    {R : LeafArena.Regions} {node level term : Word w} {expected : Word w → Word w}
    {c : Config w p r} (h : SiteMapInput common dfs R n node level term expected c) :
    ShrinkCallABI.pub c common = ShrinkSiteBank.pub level node R n := by
  funext j
  fin_cases j
  · exact h.level
  · exact h.node
  · exact h.geometry
  · exact h.histogram
  · exact h.hidden

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  {t : ℕ} (ord : B.Entry → Fin t) (i : Fin S.steps)
  (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r)
  (dfs : Fin 9 ↪ Fin r) (R : LeafArena.Regions)

local notation "lr" => LocatedBody.commonLocator (active B ord) reg
local notation "common" => shared B ord i reg

/-- The reload and five external reads supply the exact operands in the map ABI.
The argument and hidden bits remain at their original physical addresses. -/
theorem siteMapInput_of_start
    {node level term : Word w} {before after : Config w p r} {expected : Word w → Word w}
    (apart : ∀ l, dfs 6 ≠ reg l)
    (geom : ShrinkCallFrameLive.Stored R n before.privateMem)
    (endWord : before.reg (dfs 6) = (n : Word w))
    (atNode : before.reg (lr 0) = node) (atLevel : before.reg (lr 11) = level)
    (atHidden : before.reg (lr 8) = (ShrinkCallABI.hiddenBase R n : Word w))
    (mem : before.privateMem = expected)
    (loaded : MapStart common dfs term before after) :
    SiteMapInput common dfs R n node level term expected after := by
  have frame (j : Fin 14) (h9 : j ≠ 9) (h10 : j ≠ 10) :
      after.reg (common (j.castAdd 10)) = before.reg (lr j) := by
    have h (k : Fin 14) (hne : j ≠ k) : common (j.castAdd 10) ≠ common (k.castAdd 10) :=
      (common).injective.ne ((Fin.castAddEmb 10).injective.ne hne)
    exact (loaded.outside _ (h 9 h9) (h 10 h10) (locator_header_frame B ord i reg j)).trans
      (congrArg before.reg (map_locator_shared B ord i reg j))
  have free (j : Fin 24) : dfs 6 ≠ common j := apart _
  refine ⟨(frame 0 (by decide) (by decide)).trans atNode,
    (frame 11 (by decide) (by decide)).trans atLevel, ?_, ?_,
    (frame 8 (by decide) (by decide)).trans atHidden, loaded.term, loaded.stride, loaded.one,
    (loaded.outside _ (free _) (free _)
      ⟨free _, free _, free _, free _, free _, free _, free _⟩).trans endWord,
    loaded.memory.trans mem⟩
  · rw [loaded.geometry, endWord, geom.pointer]
  · rw [loaded.histogram, endWord, geom.pointer, geom.histogram]

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
