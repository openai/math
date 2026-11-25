import OAI.Hierarchy.ProtocolRAMCatalogue
import OAI.Hierarchy.ProbeReplacementLedger

namespace OAI
/-! # The price charged by the physical width words of one local operation -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Diagonal.MotifOuterTerms
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing

variable {w k n t d : ℕ} {F E A : Type*} [Field F] [Nonempty (Fin k)] [Fintype E] [Fintype A]
    {edge : E → Chord k} {req : A → E}

/-- Demands are occurrences; the same option may be debited several times in one packet. -/
def debited (req : A → E) (units : ℕ) (e : E) : ℕ :=
  ∑ a, if req a=e then units else 0

theorem debited_charge (req : A → E) (units : ℕ) (price : E → ℝ) :
    (∑ e, (debited req units e : ℝ)*price e) = (units:ℝ)*∑ a, price (req a) := by
  classical
  simp only [debited,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm,Finset.mul_sum]
  simp

omit [Fintype E] in
theorem histWidth_le (count : Fin n → E → ℕ) (h : Histogram (Fin n) t) (e : E) (bound : ℕ)
    (table : ∀ i,count i e≤bound) : histWidth count h e ≤ t*bound := by
  calc
    _ ≤ ∑ i, (h.val i).val*bound :=
      Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (table i)
    _ = t*bound := by rw [← Finset.sum_mul,h.2]

omit [Nonempty (Fin k)] in
/-- Downward rounding decreases each quoted demand credit. The only loss in transferring
the catalogue inequality to actual prices is the error on installed widths. -/
theorem rounded_charge (P : Probe.Packet F edge req) (h : Histogram (Fin P.terms) t)
    (physical : E → ℕ) (read : ∀ e, physical e = histWidth P.count h e) (B : ℕ)
    (maxWidth : ∀ i e,P.count i e≤B) (price quoted : E → ℝ)
    (err γ tree : ℝ) (nonneg : 0≤err) (accuracy : ∀ e, quoted e ≤ price e ∧ price e ≤ quoted e+err)
    (catalogue : (∑ e, (histWidth P.count h e:ℝ)*quoted e) + t*(tree*P.selectorBits) ≤
      t*((P.width:ℝ)*((∑ a, quoted (req a))-γ)))
    (resolution : (Fintype.card E:ℝ)*B*err ≤ P.width*γ/2) :
    (∑ e,(physical e:ℝ)*price e) + t*(tree*P.selectorBits) + t*(P.width*γ/2) ≤
      ∑ e,(debited req (t*P.width) e:ℝ)*price e := by
  have one (e : E) : (physical e:ℝ)*price e ≤
      (histWidth P.count h e:ℝ)*quoted e + ((t:ℝ)*B)*err := by
    have small : (histWidth P.count h e : ℝ) ≤ (t:ℝ)*B := by
      exact_mod_cast histWidth_le P.count h e B (fun i=>maxWidth i e)
    rw [read]
    calc
      _ ≤ (histWidth P.count h e:ℝ)*(quoted e+err) :=
        mul_le_mul_of_nonneg_left (accuracy e).2 (Nat.cast_nonneg _)
      _ ≤ _ := by rw [mul_add]; gcongr
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun e _=>one e)
  rw [Finset.sum_add_distrib] at total
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at total
  have demand : (∑ a, quoted (req a)) ≤ ∑ a, price (req a) :=
    Finset.sum_le_sum fun a _ => (accuracy (req a)).1
  have higher := mul_le_mul_of_nonneg_left demand
    (mul_nonneg (Nat.cast_nonneg t) (Nat.cast_nonneg P.width))
  have loss := mul_le_mul_of_nonneg_left resolution (Nat.cast_nonneg t)
  rw [debited_charge,Nat.cast_mul]
  linarith only [total,catalogue,higher,loss]

omit [Nonempty (Fin k)] in
/-- The data sent to the nonlinear ledger is read from physical native words.
Both charged links and consumable external catalysts use their own option prices. -/
theorem local_charge (P : Probe.Packet F edge req) (extra : ℕ) (b : Batch (P.terms+extra) d)
    (m : Memory w) (row : E → Word w) (tab : E → Fin (P.terms+extra) → Expr)
    (h : Histogram (Fin P.terms) b.copies) (active : ∀ e,b.selected m (row e))
    (letter : ∀ e,b.withinPacket m (row e)) (qFit : P.terms+extra≤2^w)
    (copiesFit : b.copies<2^w) (sumFit : (P.terms+extra)*b.copies<2^w)
    (field : ∀ e i, ((b.field i).eval m (row e)).val = ((padHistogram h extra).val i).val)
    (opts : ∀ e i, (tab e i).eval m (row e) = (padCounts P.count extra i e : Word w))
    (bound : ∀ i e, P.count i e≤b.maxWidth) (fit : b.maxWidth<2^w)
    (widthFit : b.copies*b.maxWidth<2^w) (price quoted : E → ℝ)
    (err γ tree : ℝ) (nonneg : 0≤err) (accuracy : ∀ e, quoted e ≤ price e ∧ price e ≤ quoted e+err)
    (catalogue : (∑ e, (histWidth P.count h e:ℝ)*quoted e) + b.copies*(tree*P.selectorBits) ≤
      b.copies*((P.width:ℝ)*((∑ a, quoted (req a))-γ)))
    (resolution : (Fintype.card E:ℝ)*b.maxWidth*err ≤ P.width*γ/2) :
    (∑ e, ((b.wire (tab e) |>.eval m (row e)).val:ℝ)*price e) +
      b.copies*(tree*P.selectorBits) + b.copies*(P.width*γ/2) ≤
      ∑ e,(debited req (b.copies*P.width) e:ℝ)*price e := by
  apply rounded_charge P h _ _ b.maxWidth bound price quoted err γ tree nonneg accuracy catalogue resolution
  intro e
  rw [packet_wire P extra b m (row e) e (tab e) h (active e) (letter e) qFit copiesFit sumFit
    (field e) (opts e) (fun i=>bound i e) fit,
    Fin.val_cast_of_lt ((histWidth_le P.count h e _ (fun i=>bound i e)).trans_lt widthFit)]


end Hierarchy.ProtocolRAM
end

end OAI
