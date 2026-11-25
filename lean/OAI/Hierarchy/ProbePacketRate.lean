import OAI.Hierarchy.ProbeIntegerBatch
import OAI.Hierarchy.ProbeBatchReplacement

namespace OAI
/-! # Exact integer perturbation bounds for a finite repair catalogue -/

namespace Hierarchy.AdaptiveProbe
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical
noncomputable section

variable {F A E : Type*} [Field F] [Fintype A] [Fintype E] {s : ℕ} [Nonempty (Fin s)]
    {edge : E → Chord s} {req : A → E}

/-- A native catalogue can store this integer bound once per packet. For every
actual histogram, the installed and spent bit widths together move any one
ordinary inventory address by at most `rate / K` normalized units. -/
def packetRate (P : Probe.Packet F edge req) : ℕ :=
  (Finset.univ.sup fun z : Fin P.terms × E => P.count z.1 z.2) + Fintype.card A

omit [Nonempty (Fin s)] in
theorem packet_rate (P : Probe.Packet F edge req) (K w J : ℕ) (hb : 0<P.width)
    (capped : J ≤ copied K P.width w) (h : Histogram (Fin P.terms) J) (e : E) :
    K*(histWidth P.count h e + ∑ a, if req a=e then J*P.width else 0) ≤ w*packetRate P := by
  classical
  let B := Finset.univ.sup fun z : Fin P.terms × E => P.count z.1 z.2
  have paid : K*J*P.width ≤ w := by
    have bound := (Nat.mul_le_mul_right (K*P.width) capped).trans (Nat.div_mul_le_self w (K*P.width))
    simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using bound
  have copies : K*J ≤ w := (Nat.le_mul_of_pos_right (K*J) hb).trans paid
  have hist : histWidth P.count h e ≤ J*B := calc
    _ ≤ ∑ i, (h.1 i).val*B := Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _
      (Finset.le_sup (f:=fun z : Fin P.terms × E => P.count z.1 z.2) (Finset.mem_univ (i,e)))
    _ = J*B := by rw [← Finset.sum_mul,h.2]
  have demand : (∑ a, if req a=e then J*P.width else 0) ≤ Fintype.card A*(J*P.width) := by
    calc
      _ ≤ ∑ _ : A, J*P.width := Finset.sum_le_sum fun a _ => by split <;> omega
      _ = _ := by simp
  calc
    _ ≤ K*(J*B+Fintype.card A*(J*P.width)) := Nat.mul_le_mul_left _ (Nat.add_le_add hist demand)
    _ = K*J*B+(K*J*P.width)*Fintype.card A := by ring
    _ ≤ w*B+w*Fintype.card A := Nat.add_le_add (Nat.mul_le_mul_right _ copies) (Nat.mul_le_mul_right _ paid)
    _ = w*packetRate P := by simp [packetRate,B,Nat.mul_add]

omit [Nonempty (Fin s)] in
/-- The static layout needs the maximum of the finitely many packet rates,
independently of the selector histogram or the number of input records. -/
theorem rate_le_catalogue {J : Type*} [Fintype J] (A : J → Type*) [∀ j,Fintype (A j)]
    (req : ∀j,A j→E) (P : ∀ j,Probe.Packet F edge (req j)) (j : J) :
    packetRate (P j) ≤ Finset.univ.sup (fun u => packetRate (P u)) := Finset.le_sup (f:=fun u=>packetRate (P u)) (Finset.mem_univ j)

end
end Hierarchy.AdaptiveProbe

end OAI
