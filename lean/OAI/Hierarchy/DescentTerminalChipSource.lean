import OAI.Hierarchy.DescentTerminalChipValidity
import OAI.Hierarchy.DescentTerminalChipPins
import OAI.Hierarchy.DescentTerminalRestrictedScalar

namespace OAI
/-! # Authentic branch content for the fixed five-scan terminal host -/
namespace Hierarchy.DescentTerminalChipSource
open DescentKernelHistory DescentTerminalRecipeRows DescentTerminalGraphPositions
open DescentTerminalScalarTransposes DescentTerminalBinReaddress DescentTerminalDenseWindow
open DescentTerminalScalarPadded DescentTerminalChipRuntime DescentTerminalChipPins
open DescentTerminalPorts DescentTerminalCableOrder Computability.BorderVNP.Crossing
open ThreeFlat.Routing ThreeFlat.RAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section

variable {S W q : ℕ}
section GroupRows
variable (sites : Fin S→Site)
abbrev GroupRow := (i : Fin S)×(g : Fin (sites i).groups)×Fin ((sites i).chunks q g)

def localAddr (a : GroupRow (q:=q) sites) : Fin ((sites a.1).rows q) :=
  let x:=ProtocolRAMPortRanks.address ((sites a.1).chunks q) Fin.val a.2
  ⟨x.val, x.isLt.trans_le ((Nat.le_add_right ((sites a.1).portRows q) ((sites a.1).tableRows q)).trans
    (Nat.le_add_right _ 1))⟩

variable (wp : 0<W) (qp : 0<q)
def rowAddress : GroupRow (q:=q) sites ↪ Fin (Bins (W:=W) (q:=q) sites*W) where
  toFun a:=DescentTerminalBinPack.rowIndex wp (counts (q:=q) sites) ⟨a.1,localAddr sites a⟩
  inj' := by
    rintro ⟨i,z⟩ ⟨j,u⟩ eqn
    have pair : (⟨i,localAddr sites ⟨i,z⟩⟩ : (k:Fin S)×Fin ((sites k).rows q)) =
        ⟨j,localAddr sites ⟨j,u⟩⟩ := (DescentTerminalBinPack.rowIndex wp (counts (q:=q) sites)).injective eqn
    have same : i = j := congrArg Sigma.fst pair
    subst j
    have coords : (localAddr sites ⟨i,z⟩).val = (localAddr sites ⟨i,u⟩).val :=
      congrArg (fun x : (k:Fin S)×Fin ((sites k).rows q)=>x.2.val) pair
    exact congrArg (Sigma.mk i) (ProtocolRAMPortRanks.injective ((sites i).chunks q)
      Fin.val Fin.val_injective (Fin.ext coords))

def anchor (a : GroupRow (q:=q) sites) : Named sites :=
  ⟨a.1,a.2.1,⟨a.2.2.val*q,DescentTerminalCableOrder.piece_used qp a.2.2⟩⟩

def groupRow (z : Named sites) : GroupRow (q:=q) sites :=
  ⟨z.1,z.2.1,⟨z.2.2.val/q,(Nat.div_lt_iff_lt_mul qp).mpr
    (z.2.2.isLt.trans_le (by simpa [Site.chunks, Nat.mul_comm] using
      CallPool.count_le_batches_mul ((sites z.1).size z.2.1) q qp))⟩⟩

def column {A : Type} (f : GroupRow (q:=q) sites→A) (zero : A) :=
  Function.extend (rowAddress sites wp) f (fun _=>zero)

theorem column_at {A : Type} (f : GroupRow (q:=q) sites→A) (zero : A) (a : GroupRow (q:=q) sites) :
    column sites wp f zero (rowAddress sites wp a)=f a :=
  (rowAddress sites wp).injective.extend_apply ..

end GroupRows

variable {P U : Type} [Fintype P] {D p piece K₀ rawRows : ℕ} {bits : P→ℕ}
    (N : Network D P bits) (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
    (r : ∀v,Recipe U (DescentTerminalBundleRows.SiteRef (p:=p) N v)) (hp : 0<p)
    (birth : ∀v,(r v).Node ↪ ℕ) (wp : 0<W) (qp : 0<q)
local notation "L" => order N home native p external nodes ops
local notation "actual" => DescentTerminalBundleRows.site L r hp birth
local notation "K" => Bins (W:=W) (q:=q) actual
local notation "idx" => DescentTerminalScalarInput.index (q:=q) (rawRows:=rawRows) N home native external nodes ops r hp birth
local notation "fmt" => DescentTerminalScalarInput.control N home native external nodes ops r hp birth qp

def first := column actual wp (fun a=>idx (anchor actual qp a)) 0
def format := column actual wp (fun a=>fmt (anchor actual qp a)) (blank q p)
local notation "firstCol" => first (rawRows:=rawRows) N home native external nodes ops r hp birth wp qp
local notation "fmtCol" => format N home native external nodes ops r hp birth wp qp

theorem physical_row (z : Named actual) :
    DescentTerminalScalarInput.physical N home native external nodes ops r hp birth wp qp z=
      rowAddress actual wp (groupRow actual qp z) := by
  let packed : Fin (K*W) := DescentTerminalBinPack.rowIndex wp (counts (q:=q) actual)
    ⟨z.1,(Site.source qp z.2).1⟩
  calc
    _ = packed := finProdFinEquiv.apply_symm_apply packed
    _ = rowAddress actual wp (groupRow actual qp z) := rfl

theorem headers : DescentTerminalScalarInput.Headers (rawRows:=rawRows) N home native external nodes ops r hp birth
    wp qp firstCol fmtCol := by
  constructor <;> intro z <;> rw [physical_row]
  · rw [first,column_at]
    exact congrArg (fun t : ℕ =>
      DescentTerminalScalarInput.bankOffset N home native external nodes ops r hp birth z.2 rawRows +
        DescentTerminalDenseWindow.first
          (DescentTerminalScalarInput.lengths N home native external nodes ops r hp birth z.2) q
          (DescentTerminalScalarInput.base N home native external nodes ops r hp birth z.2) t / (q*p))
      (Nat.mul_div_cancel (z.2.2.val/q) qp)
  · rw [format,column_at]
    exact congrArg (DescentTerminalDenseWindow.format
      (DescentTerminalScalarInput.lengths N home native external nodes ops r hp birth z.2) (Nat.mul_pos qp hp)
      (DescentTerminalScalarInput.short N home native external nodes ops r hp birth z.2)
      (DescentTerminalScalarInput.base N home native external nodes ops r hp birth z.2))
      (Nat.mul_div_cancel (z.2.2.val/q) qp)

/-- All actual ports are addressed by their chronological group row.
The remaining physical rows use a blank format, including bins beyond
the branch's purchased endpoint. -/
def content (same : p=W*piece) (pay : RowBit rawRows (q*p)→Bool) (outer : Ports bits) : Content K₀ W q piece :=
  { first := pad firstCol 0
    format := fun i s =>
      let z := pad (m:=K₀*W) fmtCol (blank q p) i s
      (z.1.cast (by rw [same]), z.2.cast (by rw [same]))
    raw := fun t => (DescentTerminalScalarInput.raw external pay outer t).cast (by rw [same])
    gate := gates (DescentTerminalRecipeRows.control actual wp qp) }

theorem accepts_iff {w : ℕ} (same : p=W*piece) (pay : RowBit rawRows (q*p)→Bool)
    (outer : Ports bits) (wordRoom : q*p ≤ w) (m : Memory w) (base : ℕ) (z : Inputs K₀ W q piece→Bool) :
    (content N home native external nodes ops r hp birth wp qp same pay outer).accepts w z ↔
      (∀i,rowWord (planes z false) i=DescentTerminalScalarTransposes.low (same ▸ wordRoom)
        (fillSegment base (K₀*W) (DescentTerminalDenseWindowRAM.file (n:=K₀*W) base
          (pad firstCol 0) (pad fmtCol (blank q p)) (DescentTerminalScalarInput.raw external pay outer)) m (base+i.val))) ∧
      wide ∘ chunks (planes z true)=sliceOutput (bits:=w) (DescentTerminalBinFormat.address W q)
        (gates (DescentTerminalRecipeRows.control actual wp qp)) (planes z false) := by
  subst p
  constructor
  · rintro ⟨x,y⟩
    exact ⟨fun i=>(congrFun x i).trans (DescentTerminalScalarPadded.observed_at wordRoom _ _ _ m base i).symm,y⟩
  · rintro ⟨x,y⟩
    exact ⟨funext (fun i=>(x i).trans (DescentTerminalScalarPadded.observed_at wordRoom _ _ _ m base i)),y⟩

end
end Hierarchy.DescentTerminalChipSource

end OAI
