import OAI.ThreeFlat.Diagonal.TraceCircuitPad
import OAI.ThreeFlat.Diagonal.TraceLocalNetwork
import OAI.ThreeFlat.Diagonal.TraceCircuitArray

namespace OAI
/-! # Rectangular array of scalar-weighted local circuits with shared input wires -/

namespace ThreeFlat.Diagonal.TracePacketArray

open TraceCircuit

variable {F ι σ : Type*} [Fintype ι] [Fintype σ] [CommRing F] {t b p : ℕ}

noncomputable def one (f : ι → TraceCompose.Packet σ) (g : ι → Bool → F) : BitNetwork F (Fintype.card σ) :=
  let e := (Fintype.equivFin ι).symm
  localNetwork (f ∘ e) (Fintype.equivFin σ) (g ∘ e)

@[simp] theorem one_eval (f : ι → TraceCompose.Packet σ) (g : ι → Bool → F) (pin : Fin (Fintype.card σ) → Bool) :
    (one f g).eval pin = ∏ i, g i ((f i).2.eval (pin ∘ Fintype.equivFin σ)) := by
  unfold one
  rw [localNetwork_eval]
  exact (Fintype.equivFin ι).symm.prod_comp (fun i : ι => g i ((f i).2.eval (pin ∘ Fintype.equivFin σ)))

theorem one_count (f : ι → TraceCompose.Packet σ) (g : ι → Bool → F) :
    (one f g).cells = (one f g).internal + Fintype.card ι := rfl

theorem one_internal (f : ι → TraceCompose.Packet σ) (g : ι → Bool → F) :
    (one f g).internal = ∑ i, (f i).1 := by
  unfold one localNetwork outputBatch
  change (TraceCompose.gather (f ∘ (Fintype.equivFin ι).symm)).size = _
  rw [TraceCompose.gather_size]
  exact (Fintype.equivFin ι).symm.sum_comp (fun i : ι => (f i).1)

noncomputable def gates (f : Fin t → ι → TraceCompose.Packet σ) (g : ι → Bool → F) : ℕ :=
  Finset.univ.sup fun v => (one (f v) g).internal

theorem gates_le (f : Fin t → ι → TraceCompose.Packet σ) (g : ι → Bool → F) (m : ℕ)
    (h : ∀ v i, (f v i).1 ≤ m) : gates f g ≤ Fintype.card ι*m := by
  apply Finset.sup_le; intro v _
  rw [one_internal]
  exact (Finset.sum_le_sum (fun i _ => h v i)).trans (by simp)

noncomputable def sites (f : Fin t → ι → TraceCompose.Packet σ) (g : ι → Bool → F)
    (v : Fin t) : Fin (gates f g+Fintype.card ι) → Cell F (gates f g) (Fintype.card σ) :=
  let hn : (one (f v) g).internal ≤ gates f g :=
    Finset.le_sup (f:=fun u => (one (f u) g).internal) (Finset.mem_univ v)
  paddedCells (one (f v) g) hn (by rw [one_count]; omega)

noncomputable def network (f : Fin t → ι → TraceCompose.Packet σ) (g : ι → Bool → F)
    (addr : Fin t → σ → BitSource b p) : BitNetwork F p :=
  assemble (sites f g) (fun v j => addr v ((Fintype.equivFin σ).symm j))

theorem eval (f : Fin t → ι → TraceCompose.Packet σ) (g : ι → Bool → F)
    (addr : Fin t → σ → BitSource b p) (pin : Fin p → Bool) :
    (network f g addr).eval pin = ∑ hidden, ∏ v, ∏ i,
      g i ((f v i).2.eval (fun j => (addr v j).read hidden pin)) := by
  classical
  rw [network,assemble_eval]
  apply Finset.sum_congr rfl; intro hidden _
  apply Finset.prod_congr rfl; intro v _
  let x := fun j => (addr v ((Fintype.equivFin σ).symm j)).read hidden pin
  have hn : (one (f v) g).internal ≤ gates f g :=
    Finset.le_sup (f:=fun i => (one (f i) g).internal) (Finset.mem_univ v)
  have hc : (one (f v) g).cells+(gates f g-(one (f v) g).internal) ≤ gates f g+Fintype.card ι := by
    rw [one_count]; omega
  exact (paddedCells_sum (one (f v) g) hn hc x).trans (by rw [one_eval]; simp [x,Function.comp_def])

@[simp] theorem cells (f : Fin t → ι → TraceCompose.Packet σ) (g : ι → Bool → F)
    (addr : Fin t → σ → BitSource b p) : (network f g addr).cells = t*(gates f g+Fintype.card ι) := rfl

/-- A supplied arithmetic capacity avoids taking the maximum over
exponentially many row numbers in a uniform implementation. -/
noncomputable def boundedSites (f : Fin t → ι → TraceCompose.Packet σ) (g : ι → Bool → F) (m : ℕ)
    (bound : ∀ v i, (f v i).1 ≤ m) (v : Fin t) :
    Fin (Fintype.card ι*m+Fintype.card ι) → Cell F (Fintype.card ι*m) (Fintype.card σ) :=
  let hn : (one (f v) g).internal ≤ Fintype.card ι*m :=
    (Finset.le_sup (s:=Finset.univ) (f:=fun v => (one (f v) g).internal) (Finset.mem_univ v)).trans
      (gates_le f g m bound)
  paddedCells (one (f v) g) hn (by rw [one_count]; omega)

noncomputable def boundedNetwork (f : Fin t → ι → TraceCompose.Packet σ) (g : ι → Bool → F) (m : ℕ)
    (bound : ∀ v i, (f v i).1 ≤ m) (addr : Fin t → σ → BitSource b p) : BitNetwork F p :=
  assemble (boundedSites f g m bound) (fun v j => addr v ((Fintype.equivFin σ).symm j))

theorem bounded_eval (f : Fin t → ι → TraceCompose.Packet σ) (g : ι → Bool → F) (m : ℕ)
    (bound : ∀ v i, (f v i).1 ≤ m) (addr : Fin t → σ → BitSource b p) (pin : Fin p → Bool) :
    (boundedNetwork f g m bound addr).eval pin = (network f g addr).eval pin := by
  classical
  rw [boundedNetwork,assemble_eval,eval]
  apply Finset.sum_congr rfl; intro hidden _
  apply Finset.prod_congr rfl; intro v _
  rw [boundedSites,paddedCells_sum,one_eval]
  simp [Function.comp_def]

end ThreeFlat.Diagonal.TracePacketArray

end OAI
