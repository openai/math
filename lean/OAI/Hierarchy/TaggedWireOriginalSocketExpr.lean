import OAI.Hierarchy.TaggedWireRoleProgramCore
import OAI.Hierarchy.TaggedWireOriginalTableData
import OAI.Hierarchy.ProtocolRAMCatalogueRowFields
import OAI.Hierarchy.ProtocolRAMHistogram

namespace OAI
/-! # Original signed socket expressions from the public seven-column metadata -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open ProtocolRAM Calendar ProbeStage.CoreBoard
def mapSocket (f : Expr→Expr) (s : Socket) : Socket := ⟨f s.positive,f s.ordinal,f s.group,f s.slot⟩
def zipSocket (f : Expr→Expr→Expr) (a b : Socket) : Socket :=
  ⟨f a.positive b.positive,f a.ordinal b.ordinal,f a.group b.group,f a.slot b.slot⟩

def paidInputs (b : CatalogueRows.Board) (core bought : Bool→Socket) (side : Bool) : Socket :=
  zipSocket b.select (core side) (bought side)

def normalized (L : Chart) (raw : Bool→Socket) (s : Bool) : Socket :=
  zipSocket (fun x y=>sortedRead (socketSite L (raw false)) (socketSite L (raw true)) s x y) (raw false) (raw true)

def publicInput (key : Expr) : Socket := ⟨.lit 0,key,.lit 0,.lit 0⟩

/-- Core tile CT reads give the actual physical site. The finite mask of axis
types is fixed at the quoted (dimension-dependent) menu size. -/
def altInput (base sites k : ℕ) (siteWord axis : Expr) : Socket :=
  publicInput (RoleROM.expr base (sites*(2*k)) (.op .add (scale (2*k) siteWord) axis))

def exterior (base : ℕ) (h : ℕ) (p : Expr) (side : Bool) : Socket :=
  publicInput (RoleROM.expr (base+side.toNat*2^h) (2^h) (if side then .lookup ⟨0,h⟩ p else p))

def altSite (c : CatalogueRows.CoreSource) (index : Expr) (side : Bool) := (if side then c.right else c.left).atRow index

def branchSocket (kind : Expr) (n : ℕ) (yes no : Socket) := zipSocket (fun a b=>.branch .eq kind (.lit n) a b) yes no

def originalInputs (L : Chart) (metaBase old exteriorBase axisBase h W k : ℕ) (core : CatalogueRows.CoreSource)
    (paid : Bool→Socket) (side : Bool) : Socket :=
  let operand := «meta» metaBase old
  let kind := operand 0
  let id := operand 1
  let buy := mapSocket (fun e=>e.atRow id) (normalized L paid side)
  let payload := exterior exteriorBase h id side
  let directed := altSite core (operand (if side then 3 else 2)) side
  let alt := altInput axisBase (siteLast h (2^W) k+1) k directed (operand 4)
  let res := publicInput (operand (if side then 6 else 5))
  branchSocket kind 0 buy (branchSocket kind 1 payload (branchSocket kind 2 alt res))

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
end

end OAI
