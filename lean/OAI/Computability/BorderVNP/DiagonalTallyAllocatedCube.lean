import OAI.Computability.BorderVNP.DiagonalTallyReportAllocation
import OAI.Computability.BorderVNP.DiagonalTallyPacketResult
import OAI.Computability.BorderVNP.DiagonalTallyCubeSuffixRead

/-! # Using the ordered global reservations for the native lookup and cube suffix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyAllocation

open VPVNP.BurstRAM RoutingISA BorderVNP.Cube BorderVNP.Cube.Tally DiagonalTallyPacketEmit

/-- Concrete selected-ID producer frame. The previously generated physical triples and
fixed recipes are read in place, while the two generated output arrays use the fresh arena. -/
def AfterTasks.packetFrame (a : AfterTasks) (count triples recipes zeroAddr oneAddr vertices : ℕ) : Frame :=
  ⟨count,triples,recipes,a.lookupRefs,a.lookupRows,zeroAddr,oneAddr,a.bound.cubeWidth,vertices⟩

/-- The generated lookup data and result words fit and have the ordering needed by the actual
lookup instructions. They also end below all persistent packed cell metadata. -/
theorem AfterTasks.lookup_separated (a : AfterTasks) {count : ℕ} (hv : count ≤ a.bound.vertices) :
    a.lookupRows+2*count ≤ a.lookupRefs ∧ a.lookupRefs+count*a.bound.cubeWidth ≤ a.ids ∧
    a.ids+count<a.packed ∧ a.packed<a.refs ∧ a.refs<a.descriptors ∧ a.descriptors<a.fresh := by
  have mul := Nat.mul_le_mul_right a.bound.cubeWidth hv
  simp only [lookupRows,lookupRefs,ids,packed,refs,descriptors,fresh]
  omega

/-- Every actual row and reference produced by the compiled cube lookup is within
the allocated finite table. The argument uses the real selected vertices and the
physical packet-relative addresses encoded by their recipes. -/
theorem AfterTasks.packetFits {w n b h K s : ℕ} (a : AfterTasks) (count triples recipes zeroAddr oneAddr dir : ℕ)
    (m : ℕ → ℕ) (vs : Fin count → Visit n b h K s) (countBound : count ≤ a.bound.vertices)
    (frameBelow : dir+85 ≤ a.start) (tripleBelow : triples+3*a.bound.vertices ≤ a.start)
    (recipeBelow : recipes+Fintype.card (Selector n K h)*Fintype.card (Vertex (n+1))*a.bound.cubeWidth ≤ a.start)
    (slices : Fintype.card (Selector n K h)*Fintype.card (Vertex (n+1))<2^w) (room : a.fresh<2^w)
    (hr : (a.packetFrame count triples recipes zeroAddr oneAddr (Fintype.card (Vertex (n+1)))).recipeAt m n b h K s)
    (ht : ∀ i, (vs i).tripleAt m (triples+3*i.val))
    (old : ∀ i, ∀ r∈recipe (vs i).selector (vs i).vertex b s, r.address (vs i).base zeroAddr oneAddr<a.start) :
    (a.packetFrame count triples recipes zeroAddr oneAddr (Fintype.card (Vertex (n+1)))).Fits m w dir := by
  let V := Fintype.card (Vertex (n+1))
  let S := Fintype.card (Selector n K h)
  let f := a.packetFrame count triples recipes zeroAddr oneAddr V
  change f.Fits m w dir
  obtain ⟨sep,out,idEnd,packEnd,refEnd,descEnd⟩ := a.lookup_separated countBound
  have rowBound (i : Fin count) : m (triples+3*i.val+1)*V+m (triples+3*i.val+2)<S*V := by
    obtain ⟨_,hu,hv⟩ := ht i
    rw [hu,hv]
    have su := (selectorOrder n K h (vs i).selector).isLt
    have vv := (vertexOrder _ (vs i).vertex).isLt
    change _<S at su
    change _<V at vv
    have prod := Nat.mul_le_mul_right V (Nat.succ_le_of_lt su)
    rw [Nat.succ_mul] at prod
    omega
  refine ⟨frameBelow,?_,?_,sep,?_,?_,?_⟩
  · change triples+3*count ≤ a.start
    omega
  · intro i hi j hj
    let row := m (triples+3*i+1)*V+m (triples+3*i+2)
    have hrow : row<S*V := rowBound ⟨i,hi⟩
    have mul := Nat.mul_le_mul_right a.bound.cubeWidth (Nat.succ_le_of_lt hrow)
    rw [Nat.succ_mul] at mul
    change j<a.bound.cubeWidth at hj
    change recipes+row*a.bound.cubeWidth+j<a.start
    change recipes+S*V*a.bound.cubeWidth ≤ a.start at recipeBelow
    omega
  · change a.lookupRefs+count*a.bound.cubeWidth<2^w
    omega
  · intro k hk
    change k<count*f.width at hk
    have pos : 0<f.width := by
      by_contra! bad
      have eq : f.width=0 := by omega
      simp [eq] at hk
    let i : Fin count := ⟨k/f.width,(Nat.div_lt_iff_lt_mul pos).mpr hk⟩
    have j := Nat.mod_lt k pos
    have decomp : i.val*f.width+k%f.width=k := Nat.div_add_mod' _ _
    rw [← decomp,(vs i).generatedRef f m i.val hr (ht i) j]
    apply lt_trans (old i _ (List.getElem_mem ..))
    change a.lookupRows<2^w
    omega
  · intro i hi
    exact (rowBound ⟨i,hi⟩).trans slices

/-- Concrete cube suffix shares the descriptor base with the true earlier cell operands. -/
def AfterTasks.suffixFrame (a : AfterTasks) (prior count zeroAddr parameters : ℕ) :
    DiagonalTallyCubeSuffix.Frame := ⟨prior,count,a.descriptors,a.ids,zeroAddr,parameters⟩

/-- The real suffix has space for every emitted row and cannot touch the selected ID bank. -/
theorem AfterTasks.suffix_room (a : AfterTasks) {prior count : ℕ}
    (hp : prior ≤ a.bound.cells*a.bound.gadgets+a.bound.uses) (hc : count ≤ a.bound.vertices)
    (zeroAddr parameters : ℕ) :
    let f := a.suffixFrame prior count zeroAddr parameters
    f.start+5*count<a.fresh ∧ f.ids+count<f.start := by
  intro f
  obtain ⟨_,_,ids,p,r,_⟩ := a.lookup_separated hc
  change a.descriptors+5*prior+5*count<a.fresh ∧ a.ids+count<a.descriptors+5*prior
  rw [AfterTasks.fresh,Bounds.operands]
  omega

end DiagonalTallyAllocation

end BorderVNP
end Computability
end OAI
