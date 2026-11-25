import OAI.Hierarchy.ProtocolRAMRetainedSource
import OAI.Hierarchy.ProtocolRAMTurnOrder
import OAI.Hierarchy.TaggedWireLiveVisits

namespace OAI
/-! # Positive chronological input rows as actual CT fixed, goods and reserve visits -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAMLiveTurnOrder

open ProbeStage ProbeStage.CoreBoard ProbeStage.CoreBoard.WordSeats
open AdaptiveProbe WireTelescope SettledMatrix
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical

variable {h W k attempts edges n : ℕ} (S : PurchaseSampler)
  (π : Equiv.Perm (Fin (2^h)))
  (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges)
  (pad : Chord (siteLast h (2^W) k+1)) (fixed : Fin edges → ℕ)

local notation "L" => B.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "Sources" => SettledMatrix.Source edges (Commodity (Fin (2^h)) (Stages h (2^W)) k)
  (Columns h (2^W) × Fin k)

abbrev Boundaries := (s : Sources) × Fin (((L).steps s).length+1)

def recover : LiveVisit S π B pad fixed → Boundaries S π B pad
  | .inl (e,x) => ⟨.inl e.val,if x then 1 else 0⟩
  | .inr (.inl ⟨i,j⟩) => ⟨.inr (.inl i),j⟩
  | .inr (.inr ⟨c,j⟩) => ⟨.inr (.inr c),j⟩

def toVisit (z : Boundaries S π B pad) (ok : retain fixed z.1) : LiveVisit S π B pad fixed :=
  match z,ok with
  | ⟨.inl e,j⟩,live => .inl (⟨e,live⟩,decide (j.val=1))
  | ⟨.inr (.inl i),j⟩,_ => .inr (.inl ⟨i,j⟩)
  | ⟨.inr (.inr c),j⟩,_ => .inr (.inr ⟨c,j⟩)

theorem recover_toVisit (z : Boundaries S π B pad) (ok : retain fixed z.1) :
    recover S π B pad fixed (toVisit S π B pad fixed z ok)=z := by
  rcases z with ⟨(e|i|c),j⟩
  · change (⟨.inl e,if decide (j.val=1) then 1 else 0⟩ : Boundaries S π B pad)=⟨.inl e,j⟩
    have select (k : Fin 2) : (if decide (k.val=1) then (1 : Fin 2) else 0) = k := by
      fin_cases k <;> rfl
    exact congrArg (fun k : Fin 2 => (⟨(.inl e : Sources),k⟩ : Boundaries S π B pad)) (select j)
  · rfl
  · rfl

def length (order : Fin n ≃ Sources) (i : Fin n) := ((L).steps (order i)).length

/-- In the underlying report the fixed path already goes from smaller to larger
site. The other two families may be canonically reversed by their actual ends. -/
def reverse (order : Fin n ≃ Sources) (i : Fin n) : Bool :=
  match order i with
  | .inl _ => false
  | .inr (.inl s) => decide (¬(L).goods.tail s < (L).goods.head s)
  | .inr (.inr s) => decide (¬(L).reserve.tail s < (L).reserve.head s)

def boundaries (order : Fin n ≃ Sources) :
    Fin (ProtocolRAMTurnOrder.turns (length S π B pad order)) ≃ Boundaries S π B pad :=
  (ProtocolRAMTurnOrder.visits (length S π B pad order) (reverse S π B pad order)).trans
    (Equiv.sigmaCongrLeft (β:=fun s : Sources=>Fin (((L).steps s).length+1)) order)

/-- Every positive native turn has one distinct mathematical visit. The only
extra rows in the chronological array are inactive fixed or zero-width routes. -/
def positive (order : Fin n ≃ Sources) (width : Sources → ℕ)
    (paid : ∀e,width (.inl e)=fixed e) :
    {i : Fin (ProtocolRAMTurnOrder.turns (length S π B pad order)) //
      0 < width (boundaries S π B pad order i).1} ↪ LiveVisit S π B pad fixed := by
  let perm := boundaries S π B pad order
  have ok (z : Boundaries S π B pad) (live : 0 < width z.1) : retain fixed z.1 := by
    rcases z with ⟨(e|i),j⟩
    · change 0 < fixed e
      rw [← paid e]
      exact live
    · trivial
  exact
    { toFun := fun i=>toVisit S π B pad fixed (perm i.val) (ok _ i.property)
      inj' := by
        intro i j eq
        apply Subtype.ext
        apply perm.injective
        simpa only [recover_toVisit] using congrArg (recover S π B pad fixed) eq }

end Hierarchy.ProtocolRAMLiveTurnOrder

end
end OAI
