import OAI.Computability.BorderVNP.PackedBundleGeometryHeaders
import OAI.Computability.BorderVNP.RoutingISACellBanks

/-! # Header configuration from the actual fixed-stride cell-bank allocator

The public circuit knows the fixed physical stride before the team chooses its
group coordinate. The later native allocation writes these same base pointers to
RAM. Only each bundle's two placement words need to survive the intervening stages.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA Diagonal.ExternalSew
open VPVNP.VerifierNetwork ParseBatchSort PackedHistogram CellPacketGeometry
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {σ : Type*} [Fintype σ] {w : ℕ}

private noncomputable def configPin (banks : CellBanks.Layout) (gap : ℕ) : Config banks.cells w → Expr Unit
  | .inl (c,j) => fixed (Fin.ofNat (2^w) (banks.bank c.val+gap)) j
  | .inr _ => .input ()

/-- Public fixed-stride receive-base and reserved-gap words plus the actual validity gate. -/
noncomputable def bankConfig (banks : CellBanks.Layout) (gap : ℕ) (valid : Frame σ Unit) :
    Frame σ (Config banks.cells w) := valid.step (configPin banks gap)

/-- All the hardwired configuration words have the pointers later installed by the native loop. -/
theorem bankConfig_value (banks : CellBanks.Layout) (gap : ℕ) (valid : Frame σ Unit) (x : σ → Bool)
    (mid : ℕ → ℕ) (c : Fin banks.cells) (room : banks.bank c.val+gap < 2^w) :
    value (fun j => (bankConfig (w:=w) banks gap valid).eval x (.inl (c,j))) =
      banks.written mid banks.cells (banks.dest+2*c.val+1)+gap := by
  rw [(banks.written_at mid c.isLt).2]
  simp only [bankConfig,Frame.step_eval,configPin]
  exact (fixed_value (valid.eval x) (Fin.ofNat (2^w) (banks.bank c.val+gap))).trans (Nat.mod_eq_of_lt room)

/-- Bank allocation never changes the source profile validity bit. -/
theorem bankConfig_valid (banks : CellBanks.Layout) (gap : ℕ) (valid : Frame σ Unit) (x : σ → Bool) :
    (bankConfig (w:=w) banks gap valid).eval x (.inr ()) = valid.eval x () := by
  simp [bankConfig,configPin,StatementCircuit.Expr.eval]

/-- One constant gate per configured pointer bit and one validity wire. -/
theorem bankConfig_size (banks : CellBanks.Layout) (gap : ℕ) (valid : Frame σ Unit) :
    (bankConfig (w:=w) banks gap valid).size ≤ valid.size+banks.cells*w+1 := by
  have h (p : Config banks.cells w) : (configPin banks gap p).size ≤ 1 := by cases p <;> rfl
  simpa only [bankConfig,Config,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_unit,
    mul_one,Nat.add_assoc] using Frame.step_size_le valid (configPin banks gap) 1 h

variable {D s m n d k J A b : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
variable {N M : Network D P bits} (retain : Retains N M) (banks : CellBanks.Layout)
variable (cell : M.Site → Fin banks.cells) (aux : M.Site → ℕ) (siteID : M.Site ↪ Fin s)
variable (edgeID : M.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable (F : Fields s m n banks.cells d k w σ) {x : σ → Bool}
variable (net : Represents M cell aux siteID edgeID portID F x)
variable (code : ∀ c, (F.cells c).val = c.val)
variable (fit : ∀ c, guessedSize M cell c+siteSize M cell c aux+suppliedSize M cell c < 2^w)

include net code fit

/-- Identify the headers with the completed native allocator's physical memory in
the actual stage order. The shared circuit is independent of these later RAM images. -/
theorem SectionSpec.of_cellBanks (head origin desc gap : ℕ)
    (original : Fin J → N.Site) (live : Fin A → P) (valid : Frame σ Unit) (shape : Fin J → Shape)
    (before placed mid mem : ℕ → ℕ) (dest : ℕ) (rect : banks.cells+6*J+banks.cells ≤ 2^b)
    (keysFit : banks.cells < 2^k) (positionsFit : 2^b ≤ 2^w)
    (baseRoom : ∀ c : Fin banks.cells, banks.bank c.val+gap < 2^w)
    (width : desc < 2^w) (scanRoom : 2^Nat.clog 2 J*desc < 2^w) (copies : ∀ i, (shape i).copies < 2^w)
    (stride : ∀ i, bottomStride ((shape i).fine+(shape i).incoming) (shape i).cap < 2^w) :
    let host := fun i => retain.site (original i)
    let old := siteID ∘ host
    let l := RoutingOutputs.privateLayout head origin m banks.cells J desc gap
    let after := banks.written mid banks.cells
    let hs := fun i => geometryHeader retain siteID F (x:=x) l after banks.dest original i
      (shape i).copies (shape i).fine (shape i).incoming (shape i).cap
    let up := geometryHeaders F old desc (bankConfig banks gap valid) shape
    RoutingOutputs.Image F old (portID ∘ live) x origin before → l.Image before J placed → l.Fits w before →
    (∀ i : Fin J, mid (l.raw+2*i.val) = placed (l.raw+2*i.val) ∧ mid (l.raw+2*i.val+1) = placed (l.raw+2*i.val+1)) →
    (l.raw+2*J ≤ banks.dest ∨ banks.dest+2*banks.cells ≤ l.raw) →
    (∀ i, (hs i).siteSlot < 2^w) →
    (∀ i : Fin (2^b+2^b), mem (dest+i.val) =
      value (fun j => (geometry (source banks.cells b up)).eval x (.inl (i,j)))) →
    SectionSpec rect (cell ∘ host) hs mem dest := by
  intro host old l after hs up geom run layoutFit keep apart room result
  have preserves (i : Fin J) : after (l.raw+2*i.val) = placed (l.raw+2*i.val) ∧
      after (l.raw+2*i.val+1) = placed (l.raw+2*i.val+1) := by
    have hi := i.isLt
    exact ⟨(banks.written_outside mid banks.cells _ (by omega)).trans (keep i).1,
      (banks.written_outside mid banks.cells _ (by omega)).trans (keep i).2⟩
  exact SectionSpec.of_geometryHeaders F retain cell aux siteID edgeID portID net code fit head origin banks.dest
    desc gap original live (bankConfig banks gap valid) shape before placed after mem dest rect keysFit positionsFit
    (fun c => bankConfig_value banks gap valid x mid c (baseRoom c)) width scanRoom copies stride geom run layoutFit
    preserves room result

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
