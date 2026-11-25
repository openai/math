import OAI.Hierarchy.ProbeFixedOriginalPrice
import OAI.Hierarchy.ProbeFixedEventCosts
import OAI.Hierarchy.ProbeFixedFinalFeeWord
import OAI.Hierarchy.ProbePaidAddress

namespace OAI
/-! # The measured direct and mate tolls on the actual original dated bill -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory PurchaseStage StockCommit
open ThreeFlat.RAM
open scoped Classical BigOperators Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dest owners
local notation "fmt" => v.nativeFormats P z width
local notation "label" => v.directLabel P z width r banks src tab dest owners
local notation "rate" => v.paidRate P z width r banks src tab dest owners
local notation "bs" => v.nativeBoards P z width
local notation "sink" => P.catalogue.sink r banks src tab dest owners
local notation "rec" => v.receipts P z width r banks src tab dest owners

set_option maxHeartbeats 2000000 in
/-- Price bounds do not require the final installed width to fit in a word. -/
theorem direct_invoice_le (a : Attempt) (m entry : Memory W) (pre post : List Event)
    (cut : Slot C m (.attempt a) pre post entry) (len : Fin P.catalogue.rows→ℝ)
    (mask mate : Expr) (room : P.catalogue.rows≤2^W) :
    let out:=run C (events (C).mesh) m
    let f:=fmt a
    let flagged:=fun i=>v.paidSupply z a (v.occurrencePort P z width a i).val
    let direct:=fun i : Fin f.occurrences=>(label a).edge.eval out (i.val:Word W)
    (∀i,flagged i=false→mask.eval out (i.val:Word W)=0) →
    (∀e : Fin P.catalogue.rows, len e≤(((P.catalogue.geometry 5).eval out (e.val:Word W)).val:ℝ)) →
    (∀i,flagged i=true→addressPrice len (direct i).val≤v.radius ∧
      addressPrice len (mate.eval out (i.val:Word W)).val≤v.radius) →
    ∀i,addressPrice len (direct i).val+
      (if mask.eval out (i.val:Word W)=0 then 0 else addressPrice len (mate.eval out (i.val:Word W)).val)≤ rate out a i := by
  intro out f flagged direct off ordinary catalyst i
  cases type : flagged i with
  | false =>
    simp only [off i type,ite_true,add_zero]
    by_cases hi : (direct i).val<P.catalogue.rows
    · let e : Fin P.catalogue.rows := ⟨(direct i).val, hi⟩
      let physical (j : Fin P.catalogue.rows) : ℝ :=
        ((P.catalogue.geometry 5).eval out (j.val : Word W)).val
      let finalMem := run C (events v.mesh) m
      have sameOut : finalMem = out := by
        change run C (events v.mesh) m = run C (events (C).mesh) m
        exact congrArg (fun mesh => run C (events mesh) m)
          (v.common_clock P z width r banks src tab dest owners).symm
      have tariff :
          ((label a).edge.eval finalMem (i.val : Word W)).val = e.val →
          physical e = (((P.catalogue.geometry 5).eval finalMem (e.val : Word W)).val : ℝ) →
          physical e = rate finalMem a i :=
        v.direct_paid_rate P z width r banks src tab dest owners a m entry pre post cut i e
          room type physical
      rw [sameOut] at tariff
      calc
        addressPrice len (direct i).val = len e := addressPrice_fin len e
        _ ≤ physical e := ordinary e
        _ = rate out a i := tariff rfl rfl
    · have nonnegative:=v.nonsupply_price P z width a i (out ((label a).out+i.val)).val type
      change rate out a i=_ at nonnegative
      simp only [addressPrice,dite_eq_right hi,nonnegative]
      positivity
  | true =>
    have radius:=catalyst i type
    have paid := v.supply_price P z width a i (out ((label a).out+i.val)).val type
    change rate out a i = 2 * (v.radius : ℝ) at paid
    rw [paid, two_mul]
    by_cases silent : mask.eval out (i.val : Word W) = 0
    · rw [ite_eq_left silent, add_zero]
      exact radius.1.trans (le_add_of_nonneg_right (Nat.cast_nonneg v.radius))
    · rw [ite_eq_right silent]
      exact add_le_add radius.1 radius.2

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard ReportSockets PurchaseFrozen
open scoped Fin.CommRing Classical

theorem Board.extended_fee_le (b : Board) (S : PurchaseSampler) {h W k jobs depth w : ℕ}
    (π : Equiv.Perm (Fin (2^h))) (marks : Marks h W k jobs) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (size : jobs*(count h (2^W) k*paths h S.degree depth)=b.boughtRows)
    (m : Memory w) (M : ℕ) (room : b.rows<2^w) (wide : 0<w)
    (codes : ∀e,(b.core.lengthCode.eval m ((order.symm e).val:Word w)).val=coreCode S M e)
    (i : Fin b.rows) :
    extendedLength (b.ordinal S π depth marks order size) (lenCode S π depth marks M) i ≤
      (((b.geometry 5).eval m (i.val:Word w)).val:ℝ) := by
  let ord:=b.ordinal S π depth marks order size
  by_cases live : ∃e, ord e=i
  · obtain ⟨e,rfl⟩:=live
    rw [extendedLength_apply]
    cases e with
    | inl e =>
      change (coreCode S M e:ℝ)≤(((b.select b.core.lengthCode (.lit 1)).eval m ((order.symm e).val:Word w)).val:ℝ)
      rw [b.select_core _ _ _ _ room,codes]
    | inr e =>
      let j:=Fin.cast size (originalBought S π depth marks e)
      have hlen : lenCode S π depth marks M (.inr e) = 1 := rfl
      have hord : (ord (.inr e)).val = b.coreRows + j.val := rfl
      have atOne : (1 : ℕ) < 2^w := Nat.one_lt_two_pow wide.ne'
      have field : ((b.geometry 5).eval m ((b.coreRows+j.val : ℕ) : Word w)).val = 1 :=
        (congrArg Fin.val (b.select_bought m b.core.lengthCode (.lit 1) j room)).trans
          (Fin.val_cast_of_lt atOne)
      rw [hlen, hord, field]
  · change extendedLength ord _ i≤_
    rw [extendedLength,dite_eq_right live]
    positivity

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
