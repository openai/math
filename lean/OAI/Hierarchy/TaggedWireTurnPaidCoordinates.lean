import OAI.Hierarchy.ProtocolRAMPaidTurnPlacement
import OAI.Hierarchy.TaggedWireTurnSparseMatrix

namespace OAI
/-! # Native scatter coordinates at the canonical paid itinerary boundary -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAMPaidTurnPlacement
open ProbeStage ProbeStage.CoreBoard ProbeStage.CoreBoard.WordSeats ReportSockets
open AdaptiveProbe WireTelescope SettledMatrix ProtocolRAMTurnShelf
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical

variable {h W k attempts edges n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
  (depth : ℕ) (marked : Marks h W k attempts) (uni : Exclusive marked)
  (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges)
  (pad : Chord (siteLast h (2^W) k+1)) (fixed : Fin edges→ℕ)
  (ident : {i // 0<fixed i} ↪ Catalogue S π depth marked)

local notation "Sources" => SettledMatrix.Source edges (Commodity (Fin (2^h)) (Stages h (2^W)) k)
  (Columns h (2^W) × Fin k)
local notation "L" => B.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "num" => (SettledMatrix.Layout.ordinal (r:=edges) (I:=Commodity (Fin (2^h)) (Stages h (2^W)) k) (A:=Columns h (2^W)×Fin k)).symm
variable (order : Fin n ≃ SettledMatrix.Source edges (Commodity (Fin (2^h)) (Stages h (2^W)) k)
    (Columns h (2^W) × Fin k))
  (width : SettledMatrix.Source edges (Commodity (Fin (2^h)) (Stages h (2^W)) k)
    (Columns h (2^W) × Fin k)→ℕ) (fixedWidth : ∀e,width (.inl e)=fixed e)
local notation "rows" => ProtocolRAMTurnOrder.turns (ProtocolRAMLiveTurnOrder.length S π B pad order)
variable (col : Fin (ProtocolRAMTurnOrder.turns (ProtocolRAMLiveTurnOrder.length S π B pad order))→Fin 7→ℕ)
  (live : ∀ i,col i 4=width (ProtocolRAMLiveTurnOrder.boundaries S π B pad order i).1)

/-- Original source identity and canonical boundary index for every output RAM row. -/
def position : Fin rows ≃ TurnShelf.Positions (L).routes :=
  (ProtocolRAMLiveTurnOrder.boundaries S π B pad order).trans
    (Equiv.sigmaCongrLeft (β:=fun s : Sources=>Fin (((L).steps s).length+1)) num).symm

include live in
theorem position_width (i : Fin rows) : col i 4=(width ∘ num) (position S π B pad order i).1 := by
  have h := (Equiv.sigmaCongrLeft (β:=fun s : Sources=>Fin (((L).steps s).length+1)) num).apply_symm_apply
    (ProtocolRAMLiveTurnOrder.boundaries S π B pad order i)
  exact (live i).trans (congrArg (fun z=>width z.1) h.symm)

def honestSpine (s : Sources) :=
  (Spine.exists_of_walk ((L).paths s)).some

def atBoundary (z : ProtocolRAMLiveTurnOrder.Boundaries S π B pad) :=
  (honestSpine S π B pad z.1).visit z.2

theorem position_site
    (named : ∀i : {e // 0<fixed e},filledChord B.actual pad i.val=
      HistoryRoles.sorted S π depth marked (.inl (ident i)))
    (u : Live col) :
    (put S π depth marked uni B pad fixed ident order width fixedWidth col live u).1=
      (honestSpine S π B pad (num (position S π B pad order u.val).1)).visit
        (position S π B pad order u.val).2 := by
  let z:=semantic S π B pad fixed order width fixedWidth col live u
  have known := live_site S π depth marked B pad fixed ident named z
    (honestSpine S π B pad (sourceOf S π B pad fixed z))
  have identVisit (x : LiveVisit S π B pad fixed) :
      (honestSpine S π B pad (sourceOf S π B pad fixed x)).visit (boundaryOf S π B pad fixed x)=
        atBoundary S π B pad (ProtocolRAMLiveTurnOrder.recover S π B pad fixed x) := by
    rcases x with ⟨e,b⟩ | g | c
    · cases b <;> rfl
    · rfl
    · rfl
  have recovered : ProtocolRAMLiveTurnOrder.recover S π B pad fixed z=
      ProtocolRAMLiveTurnOrder.boundaries S π B pad order u.val := by
    apply ProtocolRAMLiveTurnOrder.recover_toVisit
  rw [identVisit,recovered] at known
  let e:=Equiv.sigmaCongrLeft (β:=fun s : Sources=>Fin (((L).steps s).length+1)) num
  have transported:=congrArg (atBoundary S π B pad)
    (e.apply_symm_apply (ProtocolRAMLiveTurnOrder.boundaries S π B pad order u.val))
  exact ((coordinate S π depth marked uni B pad fixed ident order width fixedWidth col live u).1.trans
    known.symm).trans transported.symm

end Hierarchy.ProtocolRAMPaidTurnPlacement

end
end OAI
