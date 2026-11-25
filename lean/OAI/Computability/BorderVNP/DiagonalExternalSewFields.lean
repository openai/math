import OAI.Computability.BorderVNP.DiagonalExternalFreePhysical
import OAI.Computability.BorderVNP.DiagonalExternalSewOrdinal
import OAI.Computability.BorderVNP.PackedCellAddressPhysical
import OAI.Computability.BorderVNP.ParseBatchRawWord

/-! # Boolean fields of the sewn and grouped terminal pack

Each possible exterior interval has three columns in the stable rectangle. Both
endpoint words name original grid sites through their retained public identifiers.
One grouped port of width `g` is used per original team and grid site. The pointer
and width bits of these parameter-only columns select two shared constant gates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FieldExport

open Crossing Packing.CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

/-- Sparse ABI parameters of the exterior fields. -/
structure Params where
  /-- One fewer than the number of teams. -/
  R : ℕ
  /-- Processors per team. -/
  processors : ℕ
  /-- Number of bits in one literal or pinned field. -/
  literal : ℕ
  /-- Width of the pair field. -/
  link : ℕ
  /-- Initial site-block width. -/
  g : ℕ
  /-- Number of initial grid sites. -/
  sites : ℕ

/-- Size of the four-slot rectangle appended after the internal cable rows. -/
def Params.slots (p : Params) := 4*(p.R+1)*p.sites

/-- Physical probe address for one candidate ordinal. -/
def Params.key (p : Params) (j : Fin p.slots) := (FourSlot.slotOrdinal (p.R+1) p.sites).symm j

/-- Parameter-only arithmetic for the actual clipped candidate. -/
def Params.record (p : Params) (j : Fin p.slots) : FourSlot.Row :=
  let x := p.key j
  FourSlot.row p.R p.processors p.literal (2*p.literal+p.R*p.link) p.link p.g
    x.1.val x.2.1.val x.2.2.1 x.2.2.2

/-- The raw public site pointer. A dead slot has a canonical zero word. -/
def Params.pointer (p : Params) (name : ℕ → ℕ → ℕ) (j : Fin p.slots) (high : Bool) :=
  let r := p.record j
  if r.live then
    if high then name r.partner r.remote else name (p.key j).1.val (p.key j).2.1.val
  else 0

/-- No unused exterior candidate contributes any cable bits. -/
def Params.width (p : Params) (j : Fin p.slots) :=
  let r := p.record j
  if r.live then r.width else 0

/-- One shared false and one shared true output, along with every input wire. -/
noncomputable def constants (σ : Type*) [Fintype σ] : Frame σ (σ ⊕ Bool) :=
  ((Frame.initial (id : σ → σ)).step (fun b : Bool => (.const b : Expr σ))).withInput

/-- Live input wire or the constant selected by the fixed public geometry bit. -/
theorem constants_eval {σ : Type*} [Fintype σ] (x : σ → Bool) :
    (constants σ).eval x = Sum.elim x id := by
  funext i
  cases i <;> simp [constants,StatementCircuit.Expr.eval]

/-- The shared constant stage has at most two Boolean gates. -/
theorem constants_size (σ : Type*) [Fintype σ] : (constants σ).size ≤ 2 := by
  unfold constants
  rw [Frame.withInput_size]
  simpa using (Frame.initial (id : σ → σ)).step_size_le (fun b : Bool => (.const b : Expr σ)) 1 (fun _ => le_rfl)

/-- Fixed most-significant-first bit projections of a word from the shared constants. -/
def constPins {σ : Type*} (w a : ℕ) (i : Fin w) : σ ⊕ Bool := .inr (a.testBit (w-1-i.val))

/-- Recover a constant word from its public pins. -/
theorem constPins_value {σ : Type*} [Fintype σ] (x : σ → Bool) (w a : ℕ) (fit : a < 2^w) :
    value ((constants σ).eval x ∘ constPins w a) = a := by
  rw [constants_eval]
  exact (ParseRecords.bigValue_testBit w a).trans (Nat.mod_eq_of_lt fit)

variable {σ : Type*} {s old n C d k w : ℕ} (F : Fields s old n C d k w σ)

/-- Append the sparse exterior columns, retain the true dynamic internal cable and
site columns, and expose exactly one compressed free block per team and site. -/
def fields (p : Params) (name : ℕ → ℕ → ℕ) :
    Fields s (old+p.slots) ((p.R+1)*p.sites) C d k w (σ ⊕ Bool) where
  sites := F.sites
  cells := F.cells
  owner v j := .inl (F.owner v j)
  auxWidth v j := .inl (F.auxWidth v j)
  ptr
    | .inl (.inl i) => Sum.elim (fun u j => .inl (F.ptr (.inl (.inl u)) j))
        (fun u => constPins d (p.pointer name u false)) (finSumFinEquiv.symm i)
    | .inl (.inr i) => Sum.elim (fun u j => .inl (F.ptr (.inl (.inr u)) j))
        (fun u => constPins d (p.pointer name u true)) (finSumFinEquiv.symm i)
    | .inr i => let a : Fin (p.R+1) × Fin p.sites := finProdFinEquiv.symm i
                constPins d (name a.1.val a.2.val)
  edgeWidth i := Sum.elim (fun u j => .inl (F.edgeWidth u j)) (fun u => constPins w (p.width u))
    (finSumFinEquiv.symm i)
  portWidth _ := constPins w p.g

end Diagonal.ExternalSew.FieldExport

end BorderVNP
end Computability
end OAI
