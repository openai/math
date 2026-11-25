import OAI.Hierarchy.ProtocolRAMRetainedSource
import OAI.Hierarchy.ProtocolRAMTurnShelf
import OAI.Hierarchy.TaggedWireLiveVisits
import OAI.Hierarchy.ProtocolRAMTurnEdges

namespace OAI
/-! # The raw header's row and phase identify one genuine geometric visit, including reversed routes -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAMPaidTurnPlacement
open ProbeStage CoreBoard WordSeats ReportSockets AdaptiveProbe WireTelescope SettledMatrix
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAMTurnOrder ProtocolRAMTurnGeometry
open scoped Classical

/-- Undo the endpoint sort when converting a native raw forward phase into an oriented boundary. -/
def rawBoundary {K : ℕ} {E : Type} (l r : Fin K) (xs : List E) (z : Fin (xs.length+1)) :
    Fin ((oriented l r xs).length+1) :=
  ⟨forwardBoundary l r xs.length z.val,by
    by_cases before:l<r <;> simp only [forwardBoundary,oriented,before,ite_true,ite_false,List.length_reverse] <;>
      have h:=z.isLt <;> omega⟩

theorem raw_phase {K : ℕ} {E : Type} (l r : Fin K) (xs : List E) (z : Fin (xs.length+1)) :
    boundaryIndex l r xs (rawBoundary l r xs z)=z := by
  apply Fin.ext
  change forwardBoundary l r xs.length (forwardBoundary l r xs.length z.val)=z.val
  by_cases before:l<r <;> simp only [forwardBoundary,before,ite_false,ite_true];
    have h:=z.isLt; omega

variable {h W k attempts edges n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges) (pad : Chord (siteLast h (2^W) k+1))
local notation "L" => B.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "Source" => ProtocolRAMTurnGeometry.Source edges h (2^W) k
abbrev RawBoundary := (a : Source) × Fin (ProtocolRAMTurnGeometry.length a+1)

def rawItem (order : Fin n≃Source) : Fin (turns (ProtocolRAMTurnGeometry.length ∘ order)) ≃
    RawBoundary (h:=h) (W:=W) (k:=k) (edges:=edges) :=
  (encode (width (ProtocolRAMTurnGeometry.length ∘ order))).symm.trans
    (Equiv.sigmaCongrLeft (β:=fun a:Source=>Fin (ProtocolRAMTurnGeometry.length a+1)) order)

variable (fixed : Fin edges→ℕ)
/-- Raw positive fixed rows only require an authentic identity for live widths. -/
def rawLive (z : RawBoundary (h:=h) (W:=W) (k:=k) (edges:=edges))
    (keep : ProtocolRAMLiveTurnOrder.retain fixed z.1) : LiveVisit S π B pad fixed :=
  match z,keep with
  | ⟨.inl e,j⟩,pos=>.inl (⟨e,pos⟩,decide (j.val≠0))
  | ⟨.inr (.inl i),j⟩,_=>.inr (.inl ⟨i,rawBoundary ((L).goods.tail i) ((L).goods.head i) (B.ordinary i)
      (j.cast (congrArg (·+1) (length_ordinary B i).symm))⟩)
  | ⟨.inr (.inr c),j⟩,_=>.inr (.inr ⟨c,rawBoundary ((L).reserve.tail c) ((L).reserve.head c) (B.centers c)
      (j.cast (congrArg (·+1) (length_center B c).symm))⟩)

def forwardItem : LiveVisit S π B pad fixed→RawBoundary (h:=h) (W:=W) (k:=k) (edges:=edges)
  | .inl (e,b)=>⟨.inl e.val,if b then 1 else 0⟩
  | .inr (.inl ⟨i,j⟩)=>⟨.inr (.inl i),(boundaryIndex ((L).goods.tail i) ((L).goods.head i) (B.ordinary i) j).cast
      (congrArg (·+1) (length_ordinary B i))⟩
  | .inr (.inr ⟨c,j⟩)=>⟨.inr (.inr c),(boundaryIndex ((L).reserve.tail c) ((L).reserve.head c) (B.centers c) j).cast
      (congrArg (·+1) (length_center B c))⟩

theorem forward_raw (z : RawBoundary (h:=h) (W:=W) (k:=k) (edges:=edges)) (keep : ProtocolRAMLiveTurnOrder.retain fixed z.1) :
    forwardItem S π B pad fixed (rawLive S π B pad fixed z keep)=z := by
  rcases z with ⟨(e|i|c),j⟩
  · change Fin 2 at j
    fin_cases j <;> rfl
  · simp only [forwardItem,rawLive,raw_phase,Fin.cast_cast,Fin.cast_refl,id_eq]
  · simp only [forwardItem,rawLive,raw_phase,Fin.cast_cast,Fin.cast_refl,id_eq]

variable (order : Fin n ≃ ProtocolRAMTurnGeometry.Source edges h (2^W) k)
variable (col : Fin (turns (ProtocolRAMTurnGeometry.length ∘ order))→Fin 7→ℕ)
    (kept : ∀i : ProtocolRAMTurnShelf.Live col,ProtocolRAMLiveTurnOrder.retain fixed (rawItem order i.val).1)

def onRaw : ProtocolRAMTurnShelf.Live col ↪ LiveVisit S π B pad fixed where
  toFun i:=rawLive S π B pad fixed (rawItem order i.val) (kept i)
  inj' i j eq:=by apply Subtype.ext;apply (rawItem order).injective
                  simpa only [forward_raw] using congrArg (forwardItem S π B pad fixed) eq

end Hierarchy.ProtocolRAMPaidTurnPlacement

end
end OAI
