import OAI.Hierarchy.ProtocolRAMCalendarEventPrices
import OAI.Hierarchy.ProbeFinalRoutes

namespace OAI
/-! # The terminal signed account is the sum of every issued native payment -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open scoped BigOperators Classical
noncomputable section
variable {w : ℕ} {I : Type*}

/-- Sum of exactly the indexed words published by one physical event, read
at its terminal immutable address after the calendar. -/
def WordRows.bill (v : WordRows) (width : ℕ) (m : Memory w) : ℝ :=
  ∑i,(v.word i).value width m

theorem WordRows.bill_ports {J : Type*} [Fintype J] (field : J→ChargeWord) (width : ℕ) (m : Memory w) :
    (WordRows.ofPorts field).bill width m=∑j,(field j).value width m := by
  exact (Fintype.equivFin J).symm.sum_comp (fun i=>(field i).value width m)

theorem PriceHistory.sum_prefix (P : PriceHistory) (j width : ℕ) (m : Memory w) :
    (∑i,(P.word j i).value width m)=
      ((List.range j).map (fun t=>∑r,(P.emit t r).value width m)).sum := by
  induction j with
  | zero =>
    change (∑ i : Fin 0, (P.word 0 i).value width m) = _
    simp
  | succ j ih =>
    rw [←(P.extend j).sum_comp (fun i=>(P.word (j+1) i).value width m),Fintype.sum_sum_type,
      List.range_succ,List.map_append,List.sum_append]
    simp only [P.old_row,P.new_row,ih,List.map_singleton,List.sum_singleton]

theorem terminal_cursor (c : Mesh) : cursor c (.outer (c.inject+c.cool) 0)=(events c).length := by
  simp [cursor,position,trialBase,event_count,phaseSize,trialSize,sliceSize]

/-- The full terminal account reads the same physical address for each signed link,
opening fee, selector broadcast, catalyst credit and stock overflow as at its event.
This identity uses no assumed numerical ledger update. -/
theorem terminal_cash (M : AccountColumns I) (c : Mesh) (issued : Event→WordRows) (m : Memory w) :
    let A := (postedRows c issued).account c M
    (A.read (.outer (c.inject+c.cool) 0) m).paid =
      M.initialCharge + ((events c).map (fun e=>(issued e).bill M.payloadWidth m)).sum := by
  intro A
  rw [A.cash_words]
  apply congrArg (M.initialCharge+·)
  change (∑i,((postedRows c issued).word (cursor c (.outer (c.inject+c.cool) 0)) i).value M.payloadWidth m)=_
  rw [terminal_cursor,(postedRows c issued).sum_prefix,←positions c,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  change (scheduleRows c issued (position c e)).bill M.payloadWidth m=_
  rw [scheduleRows_current c issued he]

/-- Ordinary positive width payments and the signed cost reduction from actual
released catalyst bits form the difference represented by each row's archived
word. Activation costs are accounted separately from bit lengths. -/
structure Charges where
  install : ℝ
  opening : ℝ
  releasedBits : ℕ

def Charges.net (v : Charges) (M width : ℕ) : ℝ := v.install+v.opening-(2:ℝ)*M*v.releasedBits/width

theorem charges_sum (es : List Event) (report : Event→Charges) (M width : ℕ) :
    (es.map (fun e=>(report e).net M width)).sum=
      (es.map (fun e=>(report e).install)).sum+(es.map (fun e=>(report e).opening)).sum-
      2*M*((es.map (fun e=>(report e).releasedBits)).sum:ℕ)/width := by
  induction es with
  | nil => simp
  | cons e tail ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    rw [ih]
    unfold Charges.net
    ring

/-- Apply the terminal cash identity to the full finite schedule. The three
external receipts are for the real installed-width bank, the one-time core/probe
capacity, and the nonnegative negative-credit width histogram respectively. -/
theorem prepaid_from_native {E C : Type*} [Fintype E] [Fintype C] (acct : AccountColumns I)
    (mesh : Mesh) (issued : Event→WordRows) (mem : Memory w) (report : Event→Charges) (M : ℕ)
    (t len : E→ℝ) (installed : E→ℕ) (used : C→ℕ) (p q Q Λ : ℝ)
    (localCharge : ∀e∈events mesh,(issued e).bill acct.payloadWidth mem=(report e).net M acct.payloadWidth)
    (installedWidth : (∑e,len e*((installed e:ℝ)/acct.payloadWidth))≤
      ((events mesh).map (fun e=>(report e).install)).sum)
    (opening : (∑e,Λ*capacity p q Q (t e) (len e))≤
      acct.initialCharge+((events mesh).map (fun e=>(report e).opening)).sum)
    (true_debits : ((events mesh).map (fun e=>(report e).releasedBits)).sum=∑i,used i) :
    let A := (postedRows mesh issued).account mesh acct
    let x := A.read (.outer (mesh.inject+mesh.cool) 0) mem
    (∑e,(len e*((installed e:ℝ)/acct.payloadWidth)+Λ*capacity p q Q (t e) (len e)))≤
      x.paid+2*M*(∑i,(used i:ℝ))/acct.payloadWidth := by
  intro A x
  have cost := terminal_cash acct mesh issued mem
  have expand := List.map_congr_left (f:=fun e=>(issued e).bill acct.payloadWidth mem)
    (g:=fun e=>(report e).net M acct.payloadWidth) localCharge
  rw [expand,charges_sum,true_debits,Nat.cast_sum] at cost
  rw [Finset.sum_add_distrib]
  change _≤(A.read (.outer (mesh.inject+mesh.cool) 0) mem).paid+_
  rw [cost]
  linarith only [installedWidth,opening]

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
