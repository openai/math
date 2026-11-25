import OAI.ThreeFlat.Diagonal.PortGridKernel
import OAI.ThreeFlat.Diagonal.FixedMotifTile
import OAI.ThreeFlat.Diagonal.MotifHistogram

namespace OAI
/-! # One finite list of normalized refresh tile tables

The dyadic refresh expander is fixed before choosing the trace width. Each
of its finitely many demand shapes has its own original tile scale. Taking
a common multiple yields a single scale for the bounded grid search.
-/

namespace ThreeFlat.Diagonal.PortMotifGrid

open LinearAlgebra.SpectralBooks SiteTensor ChordGraph Computability.VPVNP.MotifGrid MotifOuterTerms
open scoped Classical BigOperators

variable {E S : Type} [Fintype E] [Fintype S] {K : Type} [Field K] {m : ℕ} [Nonempty (Fin m)]
variable (D : PortGraph (Fin m) E) (P : PortGraph (Fin m) S)
  {p : E → ℝ} {q : S → ℝ} {H R : ℝ} (G : StrictGrids p q H R)
  (hp : ∀ e, 0<p e) (hq : ∀ e, 0<q e)
  (comparison : ∀ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin m) K → _ → Prop),
    distanceEnergy p (fun e => rawWireDistance φ 1 (D.tail e) (D.head e)) ≤
      H * distanceEnergy q (fun e => rawWireDistance φ 1 (P.tail e) (P.head e)))

include hp hq comparison in
private theorem base_tile {t : ℕ} (ht : 0<t) (z : G.demands) {η : ℝ} (hη : 0<η) :
    ∃ b : ℕ, 0<b ∧ ∃ T : FixedMotifTile D P (fun e => b * G.demandWidths t z e) K,
      (T.bits : ℝ) ≤ η*b ∧ ∀ s, widthNorm q (fun e => (T.output s e : ℝ)) ≤ (b*(t*G.denominator):ℕ)*R := by
  obtain ⟨b,s,hb,hs,l,hl,n,hn,M,hM⟩ := exists_grid_kernel D P G hp (fun e => (hq e).le) comparison ht z hη 0
  let T : FixedMotifTile D P (fun e => b * G.demandWidths t z e) K :=
    { Alphabet := Fin l, bits := s, encode := Fin.castLEEmb hl,
      output := fun a e => ∑ j, n a j * G.supplyWidths t j e, entry := M, identity := hM }
  refine ⟨b,hb,T,hs,?_⟩
  intro a
  let hist : Histogram G.supplies b := ⟨fun j => ⟨n a j, Nat.lt_succ_of_le (by
    rw [← hn a]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))⟩,hn a⟩
  have nn := histogram_norm (G.supplyWidths t) q hq (G.supplyWidths_norm_le t) hist
  change widthNorm q (fun e => ((∑ j, n a j * G.supplyWidths t j e : ℕ):ℝ)) ≤ _
  simpa only [hist,histWidth,Nat.cast_mul,mul_assoc] using nn

include hp hq comparison in
/-- Uniform base multiplicity, selector fraction and normalized supply
radius for all of the expander's candidate demand profiles. -/
theorem common_grid {t : ℕ} (ht : 0<t) {η : ℝ} (hη : 0<η) :
    ∃ b : ℕ, 0<b ∧ ∀ z : G.demands, ∃ T : FixedMotifTile D P (fun e => b * G.demandWidths t z e) K,
      (T.bits : ℝ) ≤ η*b ∧ ∀ s, widthNorm q (fun e => (T.output s e : ℝ)) ≤ (b*(t*G.denominator):ℕ)*R := by
  choose b pos T fee rad using fun z => base_tile D P G hp hq comparison ht z hη
  let B := ∏ z, b z
  refine ⟨B, Finset.prod_pos (fun z _ => pos z), ?_⟩
  intro z
  obtain ⟨r, hr⟩ : b z ∣ B := Finset.dvd_prod_of_mem b (Finset.mem_univ z)
  have widths : (fun e => B * G.demandWidths t z e) = (fun e => (b z * G.demandWidths t z e) * r) := by
    funext e; rw [hr]; ac_rfl
  rw [widths]
  refine ⟨(T z).atScale r, ?_, ?_⟩
  · change ((r*(T z).bits:ℕ):ℝ) ≤ _
    rw [Nat.cast_mul,hr,Nat.cast_mul]
    calc
      _ ≤ (r:ℝ)*(η*b z) := mul_le_mul_of_nonneg_left (fee z) (Nat.cast_nonneg _)
      _ = _ := by ring
  · intro s
    have h := (T z).repeat_output_norm r q hq (rad z) s
    rw [hr]
    simpa only [Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using h

end ThreeFlat.Diagonal.PortMotifGrid

end OAI
