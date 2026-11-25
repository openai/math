import OAI.Computability.BorderVNP.ParseBatchPrewire

/-! # Reading the three public fields of a processor

The coordinates are the physical bit offsets in the prewired Boolean input.
Exterior partners are enumerated in the local order that skips the current team.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open TeamContraction ParseBatch

variable {R r t d link inner n : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
  (team : Fin (R+1)) (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (j : Fin r)

private theorem lookup (i : Fin (Prewire.publicWidth G)) :
    some (Prewire.publicBits G team pin ext (j,i)) =
      (((G.program ++ List.ofFn (G.literal team j)) ++
        List.ofFn (fun off : Fin (R*link) =>
          let kb := finProdFinEquiv.symm off
          ext (Layout.blockOf team (team.succAbove kb.1) (team.ne_succAbove kb.1), j, kb.2))) ++
        List.ofFn (fun a : Fin (G.program.length+t) => liveBit team pin (finProdFinEquiv (j,a)).val))[i.val]? := by
  let fields := G.processorFields team pin ext 0 0 0
  have hi : i.val < (fields.row j).length := by
    rw [fields.row_length j]
    simpa [Prewire.publicWidth, Wiring.pinLayout, RoutingISA.Pins.Layout.stride,
      RoutingISA.Pins.Layout.offset, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using i.isLt
  change some ((fields.row j)[i.val]'hi) = _
  rw [← List.getElem?_eq_getElem hi]
  apply congrArg (fun l : List Bool => l[i.val]?)
  change (((G.program ++ List.ofFn (G.literal team j)) ++
    (Layout.exteriorRows team j (assignments ext (fun _ (_ : Edge) => false))).flatten) ++ _) = _
  rw [Layout.flatten_exteriorRows team j _ pin]
  rfl

/-- The first field reads a bit of the processor's program followed by its literal tail. -/
theorem publicBits_literal (a : Fin (G.program.length+t)) :
    Prewire.publicBits G team pin ext (j, ⟨a.val, by
      unfold Prewire.publicWidth
      have := a.isLt
      omega⟩) =
      (G.program ++ List.ofFn (G.literal team j))[a.val]'(by simp) := by
  apply Option.some.inj
  rw [lookup]
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_ofFn]; omega),
    List.getElem?_append_left (by simp), List.getElem?_eq_getElem (by simp)]

private theorem exterior_lt (k : Fin R) (b : Fin link) : k.val*link+b.val < R*link := by
  simpa [finProdFinEquiv_apply_val, Nat.add_comm, Nat.mul_comm] using (finProdFinEquiv (k,b)).isLt

/-- A partner field reads the common exterior wire of the two teams at the same
processor and the same within-link bit. -/
theorem publicBits_exterior (k : Fin R) (b : Fin link) :
    Prewire.publicBits G team pin ext (j, ⟨G.program.length+t+(k.val*link+b.val), by
      unfold Prewire.publicWidth
      have := exterior_lt k b
      omega⟩) =
      ext (Layout.blockOf team (team.succAbove k) (team.ne_succAbove k), j, b) := by
  have hk := exterior_lt k b
  have pos : (finProdFinEquiv (k,b)).val = k.val*link+b.val := by
    simp only [finProdFinEquiv_apply_val]
    ac_rfl
  apply Option.some.inj
  rw [lookup, List.getElem?_append_left (by simp only [List.length_append, List.length_ofFn]; omega),
    List.getElem?_append_right (by simp only [List.length_append, List.length_ofFn]; omega)]
  simp only [List.length_append, List.length_ofFn, Nat.add_sub_cancel_left]
  rw [← pos, List.getElem?_eq_getElem (by
    simp only [List.length_ofFn]
    exact (finProdFinEquiv (k,b)).isLt), List.getElem_ofFn]
  simp only [Fin.eta, Equiv.symm_apply_apply]

/-- The final field reads the flat live-pin coordinate for this processor. -/
theorem publicBits_pin (a : Fin (G.program.length+t)) :
    Prewire.publicBits G team pin ext (j, ⟨G.program.length+t+R*link+a.val, by
      unfold Prewire.publicWidth
      have := a.isLt
      omega⟩) =
      liveBit team pin (finProdFinEquiv (j,a)).val := by
  apply Option.some.inj
  rw [lookup, List.getElem?_append_right (by simp only [List.length_append, List.length_ofFn]; omega)]
  simp only [List.length_append, List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn]

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
