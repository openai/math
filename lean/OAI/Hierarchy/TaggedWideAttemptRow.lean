import OAI.Hierarchy.TaggedWideCalendarLedgerCore
import OAI.Hierarchy.TaggedWideCalendarMiddle

namespace OAI
/-! # The intermediate state used by the physical signed and spill substeps -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.LedgerStep
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal TraceWords
open Tagged WideStack WideControlJoin WireTelescope WireTelescope.CalendarTape
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical
variable {F Ex Sel D H : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D] [Fintype H]
    (G : Gate)
local notation "V" => SitePins Ex Sel D G
local notation "Aug" => SitePins Ex Sel (D⊕H) G
local notation "Net" p => BitNetwork F (Fintype.card p)

/-- Both substeps read the same chronological state and the same RAM. Only
the physical local middle word is existentially summed. -/
def addMiddle : Aug→V⊕H
  | .inl x=>.inl (.inl x)
  | .inr (.inl x)=>.inl (.inr (.inl x))
  | .inr (.inr (.inl (.inl d)))=>.inl (.inr (.inr (.inl d)))
  | .inr (.inr (.inl (.inr h)))=>.inr h
  | .inr (.inr (.inr x))=>.inl (.inr (.inr (.inr x)))

def withMiddle (N : Net Aug) : Net (V⊕H) :=WideHost.onPins N (addMiddle G)

omit [Field F] in
theorem withMiddle_fee (N : Net Aug) :
    (withMiddle G N).cells+(withMiddle G N).internal=N.cells+N.internal := by
  rfl

variable (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : D→Bool)
local notation "v" => Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))
local notation "ev" h => Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim data h) (G.terminal out)))

theorem withMiddle_value (N : Net Aug) (h : H→Bool) :
    TypedWiring.value (withMiddle G N) (Sum.elim v h)=TypedWiring.value N (ev h) := by
  rw [withMiddle,WideHost.onPins_value]
  congr 1
  funext p
  rcases p with a|a|((d|m)|g) <;>rfl

variable {degree cap digits : ℕ} (capFit : cap≤2^digits) (address : Fin degree→ℕ)
local notation "mid" => Fin (degree*cap)
local notation "aug" => SitePins Ex Sel (D⊕mid) G

/-- The guard reads the preclip widths. Its digits feed the signed output
and the spill input by the same pin numbers. -/
def attemptRow (signed spill : Net aug) : Net V :=
  ChosenPackets.RowRouting.hiddenEntry (midGuard G capFit address)
    (withMiddle G signed) (withMiddle G spill)

theorem attemptRow_fee (signed spill : Net aug) :
    let row:=attemptRow G capFit address signed spill
    row.cells+row.internal≤degree*cap+degree*cap*(200*digits+65)+
      (signed.cells+signed.internal)+(spill.cells+spill.internal) := by
  intro row
  dsimp only [row,attemptRow]
  rw [ChosenPackets.RowRouting.hidden_fee,withMiddle_fee,withMiddle_fee]
  have h:=mid_cost (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) G capFit address
  omega

theorem attemptRow_value {K : ℕ} {A B C : Widths K} (op : SiteMatrix (State A) (State B) F)
    (clip : SiteMatrix (State B) (State C) F) (s : Fin K) (x : State A s) (y : State C s)
    (layout : (Σt,SiteBit B t) ↪ Fin K×mid) (site : ∀t b,(layout ⟨t,b⟩).1=t)
    (dense : ∀i : Fin G.u,(G.addr i).val=i.val) (inside : ∀q,address q<G.u)
    (strict : ∀q,(out (address q)).val<2^digits)
    (published : ∀i:mid,(s,i)∈Set.range layout ↔
      ((finProdFinEquiv : Fin degree×Fin cap≃mid).symm i).2.val<
        (out (address (finProdFinEquiv.symm i).1)).val)
    (signed spill : Net aug)
    (run : ∀z,TypedWiring.value signed (ev (middle s (siteChart layout site s) z))=op s x z)
    (settle : ∀z,TypedWiring.value spill (ev (middle s (siteChart layout site s) z))=clip s z y) :
    TypedWiring.value (attemptRow G capFit address signed spill) v=SiteMatrix.compose op clip s x y := by
  apply attempt_then_spill op clip s x y (siteChart layout site s) _ _ _ v
  · exact mid_value G capFit address out ext sel data dense inside s layout site strict published
  · intro z
    rw [withMiddle_value]
    exact run z
  · intro z
    rw [withMiddle_value]
    exact settle z

end Hierarchy.ProbeStage.CoreBoard.LedgerStep
end

end OAI
