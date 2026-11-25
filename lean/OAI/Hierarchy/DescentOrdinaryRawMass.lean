import OAI.Hierarchy.DescentIssuedDonors
import OAI.Hierarchy.DescentParentGroupSlot

namespace OAI
/-! # True surviving ordinary multiplicities in the previously emitted donor tape -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM DescentHistoryOrder DescentKernelHistory DescentStageEdgeReceipt DescentPacking
open DescentHostDegree DescentSIMDLookup DescentPackedPrivateSum DescentPackedPrivateAccumulator DescentRawCablePanel
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist} (path : Path start source)
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)
variable {H a lanesPerWord : ℕ} (vertex : source.V↪Fin H)
local notation "A" => source.placement
local notation "r" => BitDescription.scannedRows he T
local notation "N" => rawGraph he T c
local notation "fromOwner" => (originalId ((T.result he).state c).graph.Site) ∘ rawInput he T c ((r).state c)
local notation "owner" => rawOwner he T c n ((r).state c) (originalId _)
local notation "samples" => Live A (r).pick
local notation "units" => normalized A ((r).profile c)
local notation "rank" => slot A S source.valid (source.order.trans Fin.valEmbedding) vertex (Equiv.refl _) (r).pick
local notation "width" => span (S.groupCount i) k (A).cap

local notation "cellBits" => normBits (A).cap G.b G.C G.k
local notation "donorCols" => S.groupCount i*2^k*(A).cap
local notation "gain" => gainExponent 20 T.Δ
local notation "shelf" => 2^DescentHostDegree.packExponent 20 T.Δ+2
local notation "readAt" => ticket.issuedPanel vertex

def liveMass {a : ℕ} (row : Cell (2+a)) :=if samePost row then 0 else grains row

private theorem place_self {α X : Type} [Zero X] {H R : ℕ} (addr : α ↪ Fin H × Fin R)
    (value : α → X) (e : α) : place addr value (addr e).1 (addr e).2 = value e := by
  have found : ∃ t, addr t = ((addr e).1, (addr e).2) := ⟨e, rfl⟩
  rw [place, dite_eq_left found, addr.injective found.choose_spec]

private theorem liveMass_cell {a : ℕ} (pre post : Bool) (n : Cell a) :
    liveMass (cell pre post n) = (if post then 0 else n.val) := by
  simp only [liveMass, same_post, units_read]

private theorem liveMass_comparison {a : ℕ} (p : Prop) [Decidable p] (pre : Bool)
    (n : Cell a) (mass : ℕ) (represented : n.val = mass) :
    liveMass (cell pre (decide p) n) = (if p then 0 else mass) := by
  by_cases h : p <;> simp [liveMass_cell, h, represented]

private theorem liveMass_zero (a : ℕ) : liveMass (0 : Cell (2+a)) = 0 :=
  (congrArg liveMass (cell_zero a).symm).trans (liveMass_cell false false 0)

theorem OrdinaryLink.signed_units (e : samples) :
    liveMass ((readAt) (rank e).1 (rank e).2)=
      if owner ((N).src e.val)=owner ((N).dst e.val) then 0 else (N).width e.val/(A).z := by
  have fit (t : (r).pairs×Fin 2) : W.graph.width ((r).pick t)=(A).z*G.b :=
    ((r).fit t.1 t.2).trans (congrArg (·*G.b) ticket.quantum)
  have price:=normalized_width A S source.valid (r).pick ((r).profile c) fit e.val
  have reported : (GadgetNetwork.physical W.graph (r).pick (branchWidth G (fun _=>(A).z) ((r).profile c))).width e.val=(N).width e.val := by
    rcases e.val with f|⟨j,b⟩|⟨j,b⟩
    · rfl
    · rfl
    · change (A).z*_=T.z*_;rw [ticket.quantum]
  have normalized : units e.val=(N).width e.val/(A).z :=by
    rw [←reported,←price,Nat.mul_div_cancel _ (A).unitPos]
  let row (f : samples) := cell (decide (fromOwner ((N).src f.val) = fromOwner ((N).dst f.val)))
    (decide (owner ((N).src f.val) = owner ((N).dst f.val)))
    (⟨units f.val, normalized_fits A S source.valid ((r).profile c) f.val⟩ : Cell cellBits)
  refine (congrArg liveMass (place_self rank row e)).trans ?_
  exact liveMass_comparison (owner ((N).src e.val) = owner ((N).dst e.val)) _ _ _ normalized

theorem OrdinaryLink.signed_units_hole (v : Fin H) (j : Fin width)
    (hole : ¬∃e : samples,rank e=(v,j)) : liveMass ((readAt) v j)=0 := by
  change liveMass (place rank _ v j) = 0
  rw [place, dite_eq_right hole, liveMass_zero]

/-- Numeric readback uses the already published first-grain donor record,
with its original or one of ten fixed role addresses. -/
theorem OrdinaryLink.signed_report_units (e : samples) :
    let idx:=finProdFinEquiv.symm (rank e).2
    liveMass (report T.k gain shelf (ticket.measuredDonors vertex (rank e).1 idx.1) idx.2)=
      if owner ((N).src e.val)=owner ((N).dst e.val) then 0 else (N).width e.val/(A).z := by
  exact (congrArg liveMass (ticket.donor_words vertex (rank e).1 (rank e).2)).trans
    (ticket.signed_units vertex e)

end
end Hierarchy.DescentSixParty.Chronology

end OAI
