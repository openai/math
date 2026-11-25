import OAI.Hierarchy.ProtocolRAMCatalogueActiveBill
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices
import OAI.Hierarchy.ProtocolRAMCalendarDebitCount

namespace OAI
/-! # The signed native cash ledger pays the real catalogue inside a padded board -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Classical BigOperators
variable {w z d k q goods r n : ℕ} {I E C : Type*} [Fintype I] [Fintype E] [Fintype C]

/-- Replaying the complete permanent event archive gives the earlier positive
toll on every *real* edge. Discarded padding can only raise the right-hand
sum of nonnegative charges. Exact primitive receipts are given by
`Format.installed_charge` and `FeedLayout.installed_charge`. -/
theorem installed_from_calendar (c : Mesh) (fmt : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r n) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (tree core : Attempt→Traversals)
    (feed : Boundary → CommodityColumn→Traversals) (maxBits : ℕ)
    (m : Memory w) (payload : ℕ) (ordinal : E↪Fin n) (length : Fin n→ℝ)
    (nonneg : ∀i,0≤length i) (report : Event→Charges)
    (entry : ∀ev∈events c,((eventSlices fmt feeds sink idBase role ids tree core feed maxBits ev).map
      (fun s=>s.toll m length payload)).sum≤(report ev).install) :
    let paid:=paidSlices c fmt feeds sink idBase role ids tree core feed maxBits
    (∑e,length (ordinal e)*((PaidWidths.total paid m (ordinal e):ℝ)/payload))≤
      ((events c).map (fun ev=>(report ev).install)).sum := by
  intro paid
  apply (CatalogueRows.installed_le_all ordinal payload (PaidWidths.total paid m) length nonneg).trans
  rw [show (∑e,length e*((PaidWidths.total paid m e:ℝ)/payload))=_
    from toll_from_history c fmt feeds sink idBase role ids tree core feed maxBits m length payload]
  have compare (xs : List Event) (sub : ∀ev∈xs,ev∈events c) :
      (xs.map (fun ev=>((eventSlices fmt feeds sink idBase role ids tree core feed maxBits ev).map
        (fun s=>s.toll m length payload)).sum)).sum≤(xs.map (fun ev=>(report ev).install)).sum := by
    induction xs with
    | nil => simp
    | cons e rest ih =>
      simp only [List.map_cons,List.sum_cons]
      exact add_le_add (entry e (sub e (by simp))) (ih (by exact fun ev hev=>sub ev (by simp [hev])))
  exact compare _ (by simp)

omit [Fintype I] in
/-- After combining one real opening charge for each true acquired/core edge
with its previously installed widths, the actual final cash cell pays the
pre-settlement toll net of released catalyst bits. -/
theorem prepaid_calendar (A : AccountColumns I) (mesh : Mesh) (issued : Event→WordRows)
    (fmt : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn) (sink : Sink r n)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (tree core : Attempt→Traversals)
    (feed : Boundary → CommodityColumn→Traversals) (maxBits M : ℕ)
    (m : Memory w) (ordinal : E↪Fin n) (length : Fin n→ℝ) (times : E→ℝ)
    (used : C→ℕ) (p q₀ Q Λ : ℝ) (nonneg : ∀i,0≤length i) (report : Event→Charges)
    (bill : ∀ev∈events mesh,(issued ev).bill A.payloadWidth m=(report ev).net M A.payloadWidth)
    (entry : ∀ev∈events mesh,((eventSlices fmt feeds sink idBase role ids tree core feed maxBits ev).map
      (fun s=>s.toll m length A.payloadWidth)).sum≤(report ev).install)
    (openings : (∑e,Λ*capacity p q₀ Q (times e) (length (ordinal e)))≤
      A.initialCharge+((events mesh).map (fun e=>(report e).opening)).sum)
    (released : ((events mesh).map (fun e=>(report e).releasedBits)).sum=∑j,used j) :
    let bank:=(postedRows mesh issued).account mesh A
    let x:=bank.read (.outer (mesh.inject+mesh.cool) 0) m
    let ss:=paidSlices mesh fmt feeds sink idBase role ids tree core feed maxBits
    (∑e,(length (ordinal e)*((PaidWidths.total ss m (ordinal e):ℝ)/A.payloadWidth)+
      Λ*capacity p q₀ Q (times e) (length (ordinal e))))≤
      x.paid+2*M*(∑j,(used j:ℝ))/A.payloadWidth := by
  exact prepaid_from_native A mesh issued m report M times (fun e=>length (ordinal e))
    (fun e=>PaidWidths.total (paidSlices mesh fmt feeds sink idBase role ids tree core feed maxBits) m (ordinal e)) used
    p q₀ Q Λ bill (installed_from_calendar mesh fmt feeds sink idBase role ids tree core feed maxBits m
      A.payloadWidth ordinal length nonneg report entry) openings released

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
