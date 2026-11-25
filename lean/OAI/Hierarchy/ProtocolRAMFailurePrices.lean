import OAI.Hierarchy.ProtocolRAMStripFailureWords
import OAI.Hierarchy.ProtocolRAMStripTableTypes
import OAI.Hierarchy.ProtocolRAMGuardAdvice
import OAI.Hierarchy.ProtocolRAMFailureWords

namespace OAI
/-! # The finite price-grid advice read by each live discrepancy test -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Fin.CommRing Classical BigOperators
noncomputable section

variable {digits k w : ℕ} {E A : Type*} [Fintype E] [Nonempty E] [Fintype A] [Nonempty (Fin k)]

def StripTest.mount (s : StripTest digits) (F : Type*) [Field F] (edge : E→Chord k) (req : A→E)
    (price : (Fin digits→Fin s.radix)→E→ℝ) (m : Memory w) : Memory w :=
  menuAdvice s.table (AttemptGate.discrepancyWord F edge req price s.precision) m

theorem StripTest.score (s : StripTest digits) (F : Type*) [Field F] (edge : E→Chord k) (req : A→E)
    (price : (Fin digits→Fin s.radix)→E→ℝ) (old : Memory w) (i : Fin s.rows)
    (v : Fin digits→Fin s.radix) (room : s.radix^digits≤2^w) (cap : s.radix^digits≤ s.table.size)
    (live : s.live.eval (s.mount F edge req price old) (i.val:Word w)≠0)
    (xs : ∀j,(s.quoted j).eval (s.mount F edge req price old) (i.val:Word w)=((v j).val:Word w))
    (valueFit : AttemptGate.discrepancyWord F edge req price s.precision v<2^w) :
    s.failure.value (s.mount F edge req price old) i=
      ⌊(s.precision:ℝ)*Probe.discrepancy F edge req (price v)⌋₊ := by
  have entry := menu_lookup_word s.table (AttemptGate.discrepancyWord F edge req price s.precision)
    old (i.val:Word w) s.quoted v room cap xs
  simp only [FailureWords.value,FailureWords.effective,failure,Expr.eval,
    ThreeFlat.RAM.DescriptorExpr.Comparison.test,Nat.cast_zero,beq_iff_eq,
    ite_eq_right live]
  exact (congrArg Fin.val entry).trans (Fin.val_cast_of_lt valueFit)

theorem StripTest.dead (s : StripTest digits) (m : Memory w) (i : Fin s.rows)
    (inactive : s.live.eval m (i.val:Word w)=0) : s.failure.value m i=0 := by
  simp [FailureWords.value,FailureWords.effective,failure,Expr.eval,
    ThreeFlat.RAM.DescriptorExpr.Comparison.test,inactive]

/-- Missing the global repair threshold gives the small-discrepancy alternative
with its explicit fifth tolerance unit, including dormant rows of score zero. -/
theorem FailureWords.quiet {_w n : ℕ} (actual : Fin n→ℝ) (raw : Fin n→ℕ) {Q : ℕ} {ε : ℝ}
    (positive : 0<Q) (approx : ∀ i, |(raw i:ℝ)/Q-actual i|≤ε)
    (quiet : ¬ ⌈4*ε*n*Q⌉₊≤∑i,raw i) :
    (∑i,actual i)≤5*ε*n := by
  have hq : (0:ℝ)<Q := by exact_mod_cast positive
  have below : (∑ i,(raw i:ℝ))<4*ε*n*Q := by
    rw [←Nat.cast_sum]
    exact Nat.lt_ceil.mp (lt_of_not_ge quiet)
  have total : (∑ i,(raw i:ℝ)/Q)≤4*ε*n := by
    rw [←Finset.sum_div,div_le_iff₀ hq]
    exact below.le
  have s := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    show actual i≤(raw i:ℝ)/Q+ε by linarith only [(abs_le.mp (approx i)).1])
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at s
  linarith

end
end Hierarchy.ProtocolRAM

end OAI
