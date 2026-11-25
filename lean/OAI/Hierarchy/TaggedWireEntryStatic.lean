import OAI.Hierarchy.TaggedWireEntryPin

namespace OAI
/-! # Public endpoint and local digit of the original matching aperture -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.EntryOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope WireTelescope.CalendarTape TaggedPrune Tagged Catalyst AdaptiveProbe HistoryRoles ReportSockets
open scoped Classical
variable {h W k w R epochs n : ℕ}
variable (S : PurchaseSampler) (p : Equiv.Perm (Row h)) (depth : ℕ) (marked : Marks h W k epochs)
local notation "Src" => HistoryRoles.Source S p.symm depth marked
local notation "τ" => exposedSite h (2^W) k w R
local notation "Pins" => RoutingPin h w (fun _ : Fin k=> Fintype.card (Columns h (2^W))*R)

def publicPort : Pins→Public S h W k epochs
  | .inl ((i,_),b)=>.inr (.inl (.inl (i,b)))
  | .inr (v,b)=>.inr (.inr (reserveLocation h (2^W) k R v,b))

def publicDigit : Pins→ℕ
  | .inl ((_,j),_)=> j.val
  | .inr (v,_)=>((reserveSeats h (2^W) k R) v).2.val

theorem digit_public (e : exposedEdges h (2^W) k w R) (b : Bool) :
    digit e=publicDigit (matchEnd p (e,b)) := by
  rcases e with ⟨i,j⟩|v <;> cases b <;> rfl

theorem named_public (unique : Exclusive marked) (rows : Fin n≃Src)
    (e : exposedEdges h (2^W) k w R) (b : Bool) :
    named S p.symm depth marked unique rows
      (rows.symm (source S p depth marked (bucket e)),MatchingEntry.side p τ e b)=
        publicPort S (matchEnd p (e,b)) := by
  let src:=source S p depth marked (bucket e)
  change physical S p.symm depth marked unique (rows (rows.symm src),
      swap S p.symm depth marked (rows (rows.symm src)) (MatchingEntry.side p τ e b))=_
  rw [rows.apply_symm_apply]
  have tail: (matchGraph p τ).tail e=siteNumber h (2^W) k (physicalEnds S p.symm depth marked src).1 := by
    rw [source_ends];rcases e with ⟨i,j⟩|v <;> rfl
  have head: (matchGraph p τ).head e=siteNumber h (2^W) k (physicalEnds S p.symm depth marked src).2 := by
    rw [source_ends];rcases e with ⟨i,j⟩|v <;> rfl
  have undo : swap S p.symm depth marked src (MatchingEntry.side p τ e b)=b := by
    unfold swap MatchingEntry.side
    rw [tail,head]
    by_cases lt:name (physicalEnds S p.symm depth marked src).1< name (physicalEnds S p.symm depth marked src).2 <;> simp [lt]
  rw [undo]
  rcases e with ⟨i,j⟩|v <;> cases b
  · rfl
  · change Sum.inr (Sum.inl (Sum.inl (p.symm (p i),true)))=_
    rw [p.symm_apply_apply];rfl
  · rfl
  · rfl

/-- The static wire number depends only on the original exterior pin.
The cap, row serialization and admitted input permutation may vary. -/
theorem static_address (unique : Exclusive marked) (rows : Fin n≃Src) (cap : Public S h W k epochs→ℕ)
    (room : ∀j b,sourceWidth S p depth marked w R (rows j)≤ cap (named S p.symm depth marked unique rows (j,b)))
    {s : Fin (siteLast h (2^W) k+1)} (orig : {i // τ i=s}) :
    let v:=(MatchingEntry.atExterior p τ s).symm orig
    let pin:=sourcePortFor S p depth marked rows v
    let position:=NamedAperture.place (fun j=> sorted S p.symm depth marked (rows j))
      (fun j=> sourceWidth S p depth marked w R (rows j)) (named S p.symm depth marked unique rows) cap room
      ⟨s,NamedAperture.atPort _ _ pin⟩
    position.1=publicPort S orig.1 ∧ position.2.val=publicDigit orig.1 := by
  intro v pin position
  obtain ⟨port,bit⟩:=place_pin S p depth marked unique rows cap room v
  have pinID : matchEnd p v.1=orig.1:=congrArg Subtype.val ((MatchingEntry.atExterior p τ s).apply_symm_apply orig)
  exact ⟨port.trans ((named_public S p depth marked unique rows v.1.1 v.1.2).trans (congrArg _ pinID)),
    bit.trans ((digit_public p v.1.1 v.1.2).trans (congrArg _ pinID))⟩

end Hierarchy.ProbeStage.CoreBoard.EntryOrder
end

end OAI
