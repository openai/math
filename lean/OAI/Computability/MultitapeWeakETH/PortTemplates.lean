import OAI.Computability.MultitapeWeakETH.Price
import OAI.Computability.VPVNP.IteratedCompression
import OAI.Computability.VPVNP.WireCATZero

/-! # Port supplies the fixed wire-compression templates in characteristic zero -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP VPVNP.SpectralGeometry VPVNP.WireGeometry VPVNP.WireTensor Finset
open scoped BigOperators Classical
noncomputable section

/-- Add parallel copies of a perfect matching to attain dyadic degree.
Positivity of each existing arc, and hence connectivity, is preserved. -/
private theorem dyadic_extension {o D : ℕ} (ho : 0 < o) (G : RegularArcGraph (Fin (2^o)) D)
    (paths : ∀ i j, Relation.ReflTransGen (fun u v => 0 < G.multiplicity u v) i j) :
    ∃ H : RegularArcGraph (Fin (2^o)) (2^D), (arcSupportGraph H.multiplicity).Connected ∧
      ∀ i j, G.multiplicity i j ≤ H.multiplicity i j := by
  let extra := 2^D-D
  let M (u v : Fin (2^o)) := G.multiplicity u v + if u.rev = v then extra else 0
  have symm (u v) : M u v = M v u := by
    have iff : u.rev = v ↔ v.rev = u := ⟨fun eq => eq ▸ Fin.rev_rev _,fun eq => eq ▸ Fin.rev_rev _⟩
    simp only [M,iff,G.multiplicity_symmetric u v]
  have rows (u) : ∑ v, M u v = 2^D := by
    simp only [M,sum_add_distrib,G.degree,sum_ite_eq,mem_univ,ite_true,extra]
    have := Nat.lt_two_pow_self (n:=D)
    omega
  have loopless (u : Fin (2^o)) : M u u = 0 := by
    have ne : u.rev ≠ u := by
      intro eq
      have val := congrArg Fin.val eq
      simp only [Fin.val_rev] at val
      have bound := u.isLt
      obtain ⟨o,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ho.ne'
      have even : 2^o.succ = 2^o*2 := pow_succ ..
      omega
    simp [M,ne]
  have mono (u v) : G.multiplicity u v ≤ M u v := Nat.le_add_right ..
  obtain ⟨H,eq,connected⟩ := exists_connected_regularArcGraph M symm rows loopless (fun u v =>
    Relation.ReflTransGen.mono (fun i j h => h.trans_le (mono i j)) u v (paths u v))
  exact ⟨H,connected,fun i j => eq ▸ mono i j⟩

/-- The manuscript's complete-geodesic Port hypothesis gives the dyadic
expander premise used by the verified VPVNP compression algorithm. -/
theorem wireExpanders_of_port (port : PortZero) : HasWireExpanders (AlgebraicClosure ℚ) := by
  obtain ⟨D,γ,Dpos,γpos,graphs⟩ := port
  refine ⟨D,γ*(2:ℝ)^D/D,by positivity,?_⟩
  intro minimum
  obtain ⟨o,large,G,paths,bound⟩ := graphs (max minimum 2)
  have two : 2 ≤ 2^o := (le_max_right ..).trans large
  have ho : 0 < o := Nat.pos_of_ne_zero (fun h => by simp [h] at two)
  obtain ⟨H,conn,mono⟩ := dyadic_extension ho G paths
  refine ⟨o,(le_max_left ..).trans large,H,conn,?_⟩
  intro J _ F
  let _ := F.wirePseudoMetric
  intro place
  rcases subsingleton_or_nontrivial J with sub | nontriv
  · have eq (i j) : dist (place i) (place j) = 0 := by rw [Subsingleton.elim (place i) (place j),dist_self]
    simp [walkEnergy,eq]
  obtain ⟨X,_,_,embed,he,realizable,fractions,_,_⟩ :=
    exists_geodesic_completion_of_wire_transport F (fun _ _ _ S => S.fractionTransport)
  let energy (M : Matrix (Fin (2^o)) (Fin (2^o)) ℕ) := ∑ i, ∑ j, (M i j:ℝ)*dist (place i) (place j)^2
  have old := bound X fractions realizable (embed ∘ place)
  have sum := G.sum_cost (fun i j => dist (place i) (place j)^2)
  rw [Fintype.sum_prod_type] at sum
  simp only [Function.comp_apply,he] at old
  change (D:ℝ)*(∑ i, ∑ j, dist (place i) (place j)^2) ≤
    γ*(2:ℝ)^o*(∑ u, ∑ port : Fin D, dist (place u) (place (G.reverse (u,port)).1)^2) at old
  rw [sum] at old
  have bigger : energy G.multiplicity ≤ energy H.multiplicity := by
    apply sum_le_sum; intro i _
    apply sum_le_sum; intro j _
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (mono i j)) (sq_nonneg _)
  have old' := old.trans (mul_le_mul_of_nonneg_left bigger (by positivity))
  have heq : walkEnergy (normalizeArcs H.multiplicity (2^D)) place = energy H.multiplicity/(2:ℝ)^D := by
    simp only [walkEnergy,normalizeArcs,energy,Nat.cast_pow,Nat.cast_ofNat,sum_div,div_mul_eq_mul_div]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    rw [dist_comm]
  rw [heq,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  have dp : (0:ℝ) < D := Nat.cast_pos.mpr Dpos
  field_simp
  nlinarith only [old']

/-- The finite template and the field assignment are fixed before seeing
the input formula, its sparsification parameters or its length. -/
theorem templates_of_port (port : PortZero) :
    ∃ (S : Compression.BlockSchedule (AlgebraicClosure ℚ)) (B : S.Templates),
      0 < S.laneBits ∧ 2 ≤ B.growthConstant ∧ ∃ f : B.Entry → AlgebraicClosure ℚ, B.IsSolution f := by
  obtain ⟨S,B,lanes,growth,solution,_⟩ := Compression.exists_iterated_compression.{0,0} (wireExpanders_of_port port)
  exact ⟨S,B,lanes,growth,solution⟩

end
end OAI.Computability.MultitapeWeakETH
