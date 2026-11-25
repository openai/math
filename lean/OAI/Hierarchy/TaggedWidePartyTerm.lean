import OAI.Hierarchy.TaggedWideTraceBits
import OAI.Hierarchy.TaggedWirePhysicalTerm

namespace OAI
/-! # Summing the actual fixed site apertures at a retained term -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope TaggedPrune Tagged ProtocolRAMEmit
open ProtocolRAM.Calendar WireTelescope.CalendarTape
open scoped Classical BigOperators

variable {h d k w R M den : ℕ} {F : Type*} [Field F] {X : Type}
    (p : Equiv.Perm (Tagged.Row h)) (slots : Event→Slot X) (es : List Event)
    (wire : X→Widths (siteLast h d k+1)) (x₀ : X) (initial : exposedWidth p d k w R=wire x₀)
    (next : ∀e x (c : (slots e).choice x),SiteMatrix (State (wire x)) (State (wire ((slots e).next x c))) F)
    (sum : ∀e x v,(raw F (wire x)).coeff v=∑c,SiteMatrix.act (next e x c) (raw F (wire ((slots e).next x c))).coeff v)
    (report : ∀j : Path slots es x₀,Report p d k w R M den (wire (terminal slots es x₀ j)))

set_option maxHeartbeats 800000 in
/-- The true typed input to one chronological site is shared by its
consecutive operators. Its finite sum occurs only after multiplying the
entry, all protocol transitions and the final routed copy gate. -/
theorem site_apertures {N : ℕ} (j : Path slots es x₀)
    (v : ∀s,(Exposed (F:=F) (d:=d) (k:=k) (w:=w) (R:=R) p).Leg s)
    (place : PartyBit slots wire es x₀ j ↪ Fin N)
    (site : (∀e,Fin (2^(report j).widthAt e))→(Fin N→Bool)→Fin (siteLast h d k+1)→F)
    (value : ∀ (a : ∀e,Fin (2^(report j).widthAt e)) (z : SiteChoices slots wire es x₀ j)
      (s : Fin (siteLast h d k+1)),site a (placedBits slots wire es x₀ j place z) s =
      partyWeight slots wire next s es x₀ j (fun y=>(report j).finish s y ((report j).ports a s)) (z s).1 (z s).2 *
        entry p wire x₀ initial s (v s) (z s).1) :
    (∑ a : ∀e,Fin (2^(report j).widthAt e),∑ data : Fin N→Bool,
        if ∀i,data i=true → i∈Set.range place then ∏s,site a data s else 0) =
      (family p slots es wire x₀ initial next sum report).part j v := by
  refine Eq.trans ?_ (term_words p slots es wire x₀ initial next sum report j v).symm
  apply Finset.sum_congr rfl
  intro a _
  refine (sum_party_states slots wire es x₀ j place (fun data=>∏s,site a data s)).trans ?_
  let localWeight (s : Fin (siteLast h d k+1)) (z : State (wire x₀) s × PartyStates slots wire s es x₀ j) :=
    partyWeight slots wire next s es x₀ j (fun y=>(report j).finish s y ((report j).ports a s)) z.1 z.2 *
      entry p wire x₀ initial s (v s) z.1
  calc
    _ = ∑ z : SiteChoices slots wire es x₀ j, ∏s,localWeight s (z s) := by
      apply Finset.sum_congr rfl
      intro z _
      exact Finset.prod_congr rfl (fun s _=>value a z s)
    _ = ∏s,∑ z,localWeight s z := (Fintype.prod_sum localWeight).symm
    _ = _ := Finset.prod_congr rfl (fun s _=>
      (site_terms p slots es wire x₀ initial next report j s (v s) a).symm)

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm

end
end OAI
