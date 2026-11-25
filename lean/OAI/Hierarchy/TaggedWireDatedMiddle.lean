import OAI.Hierarchy.TaggedWireCappedPass
import OAI.Hierarchy.TaggedWireOriginalRows
import OAI.Hierarchy.TaggedWireVirtualOperands

namespace OAI
/-! # Intermediate role widths before original commodity overflow traversals -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope AdaptiveProbe ReportSockets
open HistoryRoles.RoleProgram
open scoped Classical
variable {h d k S edges : ℕ} {sampler : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
  {place : Site h d k→Fin S} (B : Mount (S:=sampler) π place edges)
local notation "I" => Commodity (Fin (2^h)) (Stages h d) k
local notation "A" => Columns h d×Fin k
local notation "O" => Fin edges⊕(I⊕A)

/-- Reverse only the current overflow settlement, on original mixed row IDs. -/
def middleAmounts (after : O→ℕ) (spill : I→ℕ) : O→ℕ :=
  Sum.elim (fun e=>after (.inl e)-routeLoad B.ordinary spill e)
    (Sum.elim (fun i=>after (.inr (.inl i))+spill i) (fun a=>after (.inr (.inr a))))

def amountsWidth (original : O→ℕ) : Widths S :=
  B.actual.chordWidths (fun e=>original (.inl e))+
    (commodityGraph π place).chordWidths (fun i=>original (.inr (.inl i)))+
    (catalystGraph place).chordWidths (fun a=>original (.inr (.inr a)))

/-- The post-packet state in the signed composition is at the actual paid
width before this spill and the entire untrimmed stock at each commodity.
Other held goods are included regardless of the outer/inner reserve mode. -/
theorem middle_parts (T : Transfer h d k) (paid : Fin edges→ℕ) (previous : I→ℕ)
    (reserve : A→ℕ) (after : O→ℕ)
    (payments : ∀e,after (.inl e)=paid e+routeLoad B.ordinary T.spill e)
    (goods : ∀i,after (.inr (.inl i))=previous i+T.held i+T.kept i)
    (axes : ∀a,after (.inr (.inr a))=reserve a) :
    middleAmounts B after T.spill=Sum.elim paid
      (Sum.elim (fun i=>previous i+T.old i+T.active i) reserve) := by
  funext x
  rcases x with e|(i|a)
  · simp [middleAmounts,payments]
  · change after (.inr (.inl i))+T.spill i=previous i+T.old i+T.active i
    rw [goods]
    have balance:=T.balanced i
    omega
  · exact axes a

theorem middle_input (T : Transfer h d k) (paid : Fin edges→ℕ) (previous : I→ℕ)
    (reserve : A→ℕ) (after : O→ℕ)
    (payments : ∀e,after (.inl e)=paid e+routeLoad B.ordinary T.spill e)
    (goods : ∀i,after (.inr (.inl i))=previous i+T.held i+T.kept i)
    (axes : ∀a,after (.inr (.inr a))=reserve a) :
    amountsWidth B (middleAmounts B after T.spill)=input (π:=π) (place:=place)
      (B.actual.chordWidths paid+(commodityGraph π place).chordWidths previous+
        (catalystGraph place).chordWidths reserve) T := by
  rw [middle_parts B T paid previous reserve after payments goods axes]
  simp only [amountsWidth,Sum.elim_inl,Sum.elim_inr,input,chordWidths_add]
  abel

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer
end

end OAI
