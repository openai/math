import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # The two native address intervals containing the previous paid rows and assembled count table -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts
open DescentSIMDLookup ProtocolRAM
noncomputable section

structure Layout where
  base : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  blocks : ℕ
  paths : ℕ
  bits : ℕ

def layout (base H G M k paths b : ℕ) : Layout := ⟨base,H,G,M,2^k,paths,b⟩

namespace Layout
variable (L : Layout)
abbrev rows := L.hosts*chunks L.groups L.lanes
abbrev donors := L.paths*L.blocks
def pageBits := Nat.clog 2 L.rows
def span := 2^L.pageBits
def book (i : Fin L.blocks) : Bank := ⟨L.base+i.val*L.span,L.pageBits⟩
def romBase := L.base+L.blocks*L.span
def romBits := (L.bits*L.donors+L.bits)*L.lanes
def tableWords := (L.donors*2)*2^L.romBits
def outBase := L.romBase+L.tableWords
def result : Bank := ⟨L.outBase,L.pageBits⟩
def roof := L.outBase+L.span
def expr : Expr := .lookup L.result .row

theorem translate (base H G M k paths b : ℕ) :
    (layout base H G M k paths b).roof = base+(layout 0 H G M k paths b).roof := by
  simp [layout,roof,outBase,romBase,tableWords,romBits,span,pageBits,Nat.add_assoc]

end Layout
end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts

end OAI
