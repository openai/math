import OAI.Computability.MultitapeWeakETH.TerminalWords
import OAI.Computability.MultitapeWeakETH.GridProgram

/-! # Gathering the two ends of the terminal wires from a shared assignment -/

namespace OAI.Computability.MultitapeWeakETH.TerminalWords

open IntegerMultiplication Code VPVNP Compression PairSimulation TerminalGatherGeometry
open private take_sum from OAI.Computability.VPVNP.PairTerminalPrefix
open private payload_bit from OAI.Computability.VPVNP.PairTerminalGatherGeometry
noncomputable section

abbrev Fields := List Tally × Bits.Word

/-- Widths are stored in outgoing arc order. The exclusive prefix sum
is the location of the first bit. -/
def slice (q : Fields × Tally) : Bits.Word :=
  let widths := q.1.1
  let start := (cutLists (q.2,widths)).1.flatten
  let len := Iter.pick [] (widths,q.2)
  (cutLists (len,(cutLists (start,q.1.2)).2)).1

theorem slice_poly : Poly slice := by
  have ws : Easy (fun q : Fields × Tally => q.1.1) := Easy.fst.compose Easy.fst
  have start := (easy_cut (Easy.snd.pair ws)).fstCompose.compose Easy.flatten
  have bit : Easy (fun q : Fields × Tally => q.1.2) := Easy.fst.compose Easy.snd
  have rest := (easy_cut (start.pair bit)).sndCompose
  have len := (ws.pair Easy.snd).compose (Iter.facile [])
  exact (easy_cut (len.pair rest)).fstCompose.poly

def widths {a g : ℕ} (X : State a g) := List.ofFn (fun i => tally (TerminalPrefix.width X i))

theorem slice_widths {a g : ℕ} (X : State a g) (i : Fin (TerminalPrefix.arcCount X))
    (bits : Bits.Word) :
    slice ((widths X,bits),tally i.val) =
      (bits.drop (EndpointBits.offset (TerminalPrefix.width X) i)).take (TerminalPrefix.width X i) := by
  have start : ((widths X).take i.val).flatten.length = EndpointBits.offset (TerminalPrefix.width X) i := by
    rw [List.length_flatten,List.map_take]
    simp only [widths,List.map_ofFn,Function.comp_def,tally_length,take_sum]
  simp [slice,widths,cutLists,Iter.entry,tally_length] at *
  exact congrArg (fun n => (bits.drop n).take _) start

theorem slice_field {a g : ℕ} (X : State a g) (v : X.network.Site) (b : Bool) (j : Fin (2^a))
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool) :
    slice ((widths X,List.ofFn f),tally (number X (arc X v b j)).val) =
      List.ofFn (NodeArguments.fieldBits X v (half X f v) b j) := by
  let e := number X (arc X v b j)
  let w := TerminalPrefix.width X
  have eq : w e = X.halfWidth v b j := slot_width X v b j
  have fit := EndpointBits.arc_fits w e
  rw [slice_widths]
  change ((List.ofFn f).drop (EndpointBits.offset w e)).take (w e) = _
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn]
    exact (Nat.min_eq_left (by omega : w e ≤ (∑ i,w i)-EndpointBits.offset w e)).trans eq
  · intro k _ hk
    have h : k < X.halfWidth v b j := by simpa only [List.length_ofFn] using hk
    let idx := FinalBits.index w e (Fin.cast eq.symm ⟨k,h⟩)
    have loc : EndpointBits.offset w e + k = idx.val := (FinalBits.index_val w e (Fin.cast eq.symm ⟨k,h⟩)).symm
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    have addr : (⟨EndpointBits.offset w e+k,by omega⟩ : Fin (∑ i,w i)) = idx := Fin.ext loc
    rw [addr]
    cases b with
    | false => exact (payload_bit X f (v,j) ⟨k,h⟩).symm
    | true => exact (payload_bit X f (X.slots.actualGraph.target.symm (v,j)) ⟨k,h⟩).symm

/-- A vertex's fields are given by a list of outgoing ordinals followed by
the inverse images of its incoming ordinals. Both ends use the same bits. -/
def gather (q : Fields × List Tally) : Bits.Word := (q.2.map (fun i => slice (q.1,i))).flatten

theorem gather_poly : Poly gather :=
  (Poly.push ([],[]) [] slice_poly).compose Easy.flatten.poly

def edges {a g : ℕ} (X : State a g) (v : X.network.Site) (b : Bool) :=
  List.ofFn (fun j => tally (number X (arc X v b j)).val)

theorem gather_eq {a g : ℕ} (X : State a g) (v : X.network.Site)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool) :
    gather ((widths X,List.ofFn f),edges X v false ++ edges X v true) =
      NodeArguments.packed X v (half X f v) := by
  simp [gather,edges,List.map_ofFn,Function.comp_def,slice_field,NodeArguments.packed,NodeArguments.fields]

end
end OAI.Computability.MultitapeWeakETH.TerminalWords
