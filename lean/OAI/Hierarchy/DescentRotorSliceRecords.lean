import OAI.Hierarchy.DescentGoodBaseMatrix
import OAI.Hierarchy.ProtocolStackContraction

namespace OAI
/-! # Scalar lookup records for all powered slices of a selected reset -/

namespace Hierarchy.DescentRotor.BaseCircuit
open LinearAlgebra.SpectralBooks ThreeFlat
open RouteUnits Expander NonlinearExpanders DescentBaseProfile
open scoped BigOperators Classical
noncomputable section
variable {E K : Type*} [Fintype E] [Field K] {n h C w u : ℕ} {G : Graph n h}
    {hw : 0<w} {src dst : E → Fin (2^n)} {pay : ℝ}

abbrev Hidden (P : BaseCircuit K G C w u hw src dst pay) :=
  Fin P.layers → Arc G.arcs → Fin u → Fin (2^(C*w))

abbrev Slice (P : BaseCircuit K G C w u hw src dst pay) := Fin P.layers × Fin (2^n) × Fin u

/-- The concrete scalar request submitted by the chosen powered atom. Every
argument comes from one actual wire value, filled source or destination
row, fixed host incidence, replica digit or permutation selector. -/
def address (P : BaseCircuit K G C w u hw src dst pay) (x y : E → Fin u → Bool) (z : Hidden P)
    (s : Slice P) : Fin (Fintype.card (Entry G.arcs C w)) :=
  let r := s.1
  let v := s.2.1
  let k := s.2.2
  key G.arcs C w (P.rotation r,⟨v,
    fillRows 0 (fun e=>(P.choose e,e.1)) (packetWord (packetAddress src dst hw) x) (r,v) k,
    fillRows 0 (fun e=>(P.choose e,e.2.1)) (packetWord (packetAddress src dst hw) y) (r,v) k,
    fun p=>z r p.val.1 k⟩)

private theorem slice_sum {J V U A : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [Fintype U] [Fintype A] (entry : J → V → U → A → K) :
    (∑ z : J → A, ∏ s : J × V × U, entry s.1 s.2.1 s.2.2 (z s.1)) =
      ∏ r, ∑ a, ∏ v, ∏ k, entry r v k a := by
  let factor (r : J) (a : A) := ∏ v, ∏ k, entry r v k a
  calc
    _ = ∑ z : J → A, ∏ r, factor r (z r) := by simp only [Fintype.prod_prod_type,factor]
    _ = _ := (Fintype.prod_sum factor).symm

/-- Sum over the actual hidden wires of all selected degree-three layers. The
terms are products of calls to the single, globally fixed rotor scalar ROM. -/
theorem lookup_contraction (P : BaseCircuit K G C w u hw src dst pay) (x y : E → Fin u → Bool) :
    (∑ z : Hidden P,∏ s : Slice P,rom G.arcs C w (fixedTable P.menu) (P.address x y z s)) =
    if ∀ e,x e=y e then 1 else 0 := by
  let left (r : Fin P.layers) (v : Fin (2^n)) :=
    fillRows 0 (fun e => (P.choose e,e.1)) (packetWord (packetAddress src dst hw) x) (r,v)
  let right (r : Fin P.layers) (v : Fin (2^n)) :=
    fillRows 0 (fun e => (P.choose e,e.2.1)) (packetWord (packetAddress src dst hw) y) (r,v)
  let entry (r : Fin P.layers) (v : Fin (2^n)) (k : Fin u) (a : Arc G.arcs → Fin u → Fin (2^(C*w))) :=
    P.tables r v (left r v k) (right r v k) (fun p => a p.val.1 k)
  have point (z : Hidden P) (s : Slice P) :
      rom G.arcs C w (fixedTable P.menu) (P.address x y z s) = entry s.1 s.2.1 s.2.2 (z s.1) := by
    obtain ⟨r,v,k⟩ := s
    let a (p : (supplyGraph G.arcs).Port v) := z r p.val.1 k
    exact (rom_read G.arcs C w (fixedTable P.menu) (P.rotation r) v (left r v k) (right r v k) a).trans
      (congrFun (congrFun (congrFun (congrFun (P.selected r).symm v) (left r v k)) (right r v k)) a)
  have packed (r : Fin P.layers) : attachedLayer (P.tables r) u (left r) (right r) =
      ∑ a, ∏ v, ∏ k, entry r v k a := by
    refine (attachedLayer_eq (P.tables r) u (left r) (right r)).trans ?_
    unfold PortGraph.contraction
    apply Finset.sum_congr (congrArg
      (@Finset.univ (Arc G.arcs → Fin u → Fin (2^(C*w)))) (Subsingleton.elim _ _))
    intro a _
    rfl
  calc
    _ = ∑ z : Hidden P, ∏ s : Slice P, entry s.1 s.2.1 s.2.2 (z s.1) :=
      Finset.sum_congr rfl fun z _ => Finset.prod_congr rfl fun s _ => point z s
    _ = ∏ r, ∑ a, ∏ v, ∏ k, entry r v k a := slice_sum entry
    _ = ∏ r, attachedLayer (P.tables r) u (left r) (right r) :=
      Finset.prod_congr rfl fun r _ => (packed r).symm
    _ = _ := P.realizes x y

/-- The controller may return only the frequency bits of its scalar requests.
Every contribution of all allowed field entries, including zero, survives
taking these histogram counts and powers of two. -/
theorem lookup_histogram (P : BaseCircuit K G C w u hw src dst pay) (x y : E → Fin u → Bool)
    (digits : ℕ) (fit : Fintype.card (Slice P)<2^digits) :
    (∑ z : Hidden P, ∏ i : Fin (Fintype.card (Entry G.arcs C w)), ∏ j : Fin digits,
      if (Finset.univ.filter (fun s : Slice P=>P.address x y z s=i)).card.testBit j.val then
        (rom G.arcs C w (fixedTable P.menu) i)^(2^j.val) else 1) =
      if ∀e,x e=y e then 1 else 0 := by
  rw [←P.lookup_contraction x y]
  apply Finset.sum_congr rfl
  intro z _
  convert (ProtocolStackContraction.table_histogram_bits
    (P.address x y z) (rom G.arcs C w (fixedTable P.menu)) digits fit).symm using 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  exact congrArg (fun fs : Finset (Slice P) => if fs.card.testBit j.val then
    (rom G.arcs C w (fixedTable P.menu) i)^(2^j.val) else 1)
    (@Finset.filter_congr_decidable _ Finset.univ (fun s => P.address x y z s=i)
      (fun _ => inferInstance) (fun _ => Classical.propDecidable _))

end
end Hierarchy.DescentRotor.BaseCircuit

end OAI
