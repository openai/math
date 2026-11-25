import OAI.Computability.BorderVNP.LabelIndexImage

/-! # The per-cell demands and the initial scaled means of the native chooser -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA.LabelTrial

/-- Writing beyond all heads and allocated nodes preserves their lists. -/
private theorem lists_above {l m a i d j k} (v : View l m a l.cells i d j k)
    (al : Allocated l) (hi : i ≤ l.cableCount) {addr : ℕ} (ha : l.data ≤ addr) (value c : ℕ)
    (hc : c < l.cells) :
    let mem := Function.update a.mem addr value
    Linked mem l.nodes (2*i) (mem (l.heads+c)) (incidents (cableAt l m) c i) := by
  have nn := al.nodes
  have hh := al.heads
  dsimp only
  rw [Function.update_of_ne (by omega)]
  apply (v.lists c hc).copy le_rfl
  intro x _ hx
  apply Function.update_of_ne
  omega

/-- Each delivery's width is added exactly once to its cell and the total. -/
theorem View.delivery {l m a i} (v : View l m a l.cells l.cableCount i 0 0)
    (al : Allocated l) (ep : Endpoints l m) (hi : i < l.deliveryCount) :
    View l m (Phase.delivery.step l i a) l.cells l.cableCount (i+1) 0 0 := by
  let d := deliveryAt l m i
  have he := v.input.delivery al hi
  have dest : a.mem (l.deliveries+i*7+4) = d.1 := congrArg Prod.fst he
  have width : a.mem (l.deliveries+i*7+6) = d.2 := congrArg Prod.snd he
  have hc : d.1 < l.cells := ep.deliveries i hi
  have hh := al.heads
  have hn := al.nodes
  simp only [Phase.step,dest,width]
  constructor
  · intro x hx
    exact (Function.update_of_ne (show x ≠ l.data+d.1 by omega) ..).trans (v.input x hx)
  · exact fun c hc' => lists_above v al le_rfl (Nat.le_add_right ..) _ c hc'
  · intro c hc'
    simp only [sumWidth,show deliveryAt l m i = d from rfl]
    by_cases eq : d.1 = c
    · simp [eq,v.data c hc']
    · rw [ite_eq_right eq,Nat.add_zero,Function.update_of_ne (by omega)]
      exact v.data c hc'
  · exact v.cableTotal
  · simp only [sumWidth,Function.comp_apply,v.dataTotal]
    rfl
  · simp
  · simp

/-- Filling the next cable mean bin writes the original total as its numerator.
All cell demands and previously filled bins survive. -/
theorem View.cableBin {l m a i} (v : View l m a l.cells l.cableCount l.deliveryCount i 0)
    (al : Allocated l) : View l m (Phase.cableBins.step l i a)
      l.cells l.cableCount l.deliveryCount (i+1) 0 := by
  have hh := al.heads
  have hn := al.nodes
  have hd := al.data
  constructor
  · intro x hx
    exact (Function.update_of_ne (show x ≠ l.cableMean+i by omega) ..).trans (v.input x hx)
  · exact fun c hc => lists_above v al le_rfl (by omega) _ c hc
  · intro c hc
    exact (Function.update_of_ne (show l.data+c ≠ l.cableMean+i by omega) ..).trans (v.data c hc)
  · exact v.cableTotal
  · exact v.dataTotal
  · intro k hk
    by_cases eq : k = i
    · simp [eq,Phase.step]
    · exact (Function.update_of_ne (show l.cableMean+k ≠ l.cableMean+i by omega) ..).trans (v.pairs k (by omega))
  · simp

/-- Every data mean initially has numerator `Z * total` when scaled by `Z²`. -/
theorem View.dataBin {l m a i} (v : View l m a l.cells l.cableCount l.deliveryCount (l.labels*l.labels) i)
    (al : Allocated l) : View l m (Phase.dataBins.step l i a)
      l.cells l.cableCount l.deliveryCount (l.labels*l.labels) (i+1) := by
  have hh := al.heads
  have hn := al.nodes
  have hd := al.data
  have hb := al.cableMean
  constructor
  · intro x hx
    exact (Function.update_of_ne (show x ≠ l.dataMean+i by omega) ..).trans (v.input x hx)
  · exact fun c hc => lists_above v al le_rfl (by omega) _ c hc
  · intro c hc
    exact (Function.update_of_ne (show l.data+c ≠ l.dataMean+i by omega) ..).trans (v.data c hc)
  · exact v.cableTotal
  · exact v.dataTotal
  · intro k hk
    exact (Function.update_of_ne (show l.cableMean+k ≠ l.dataMean+i by omega) ..).trans (v.pairs k hk)
  · intro k hk
    by_cases eq : k = i
    · simp [eq,Phase.step]
    · exact (Function.update_of_ne (show l.dataMean+k ≠ l.dataMean+i by omega) ..).trans (v.bins k (by omega))

/-- Propagate an indexed invariant through an arbitrary prefix of a directory pass. -/
theorem Phase.prefix_view (p : Phase) (l : Layout) (a : Acc) (V : ℕ → Acc → Prop)
    (init : V 0 a) (step : ∀ i < p.count l, ∀ b, V i b → V (i+1) (p.step l i b))
    {j : ℕ} (hj : j ≤ p.count l) : V j (p.prefix l a j) := by
  induction j with
  | zero => exact init
  | succ j ih => exact step j hj _ (ih (Nat.le_of_succ_le hj))

/-- All list, width and scaled mean words in the final natural image match the
original cable and data rows, including tables with no cells or rows. -/
theorem image_view (l : Layout) (m : ℕ → ℕ) (al : Allocated l) (ep : Endpoints l m) :
    View l m (image l m) l.cells l.cableCount l.deliveryCount (l.labels*l.labels) l.labels := by
  let a : Acc := ⟨m,0,0⟩
  have v0 := Phase.clear.prefix_view l a (fun i b => View l m b i 0 0 0 0) (View.empty l m)
    (fun _ hi _ v => v.clear al hi) le_rfl
  have v1 := Phase.cable.prefix_view l _ (fun i b => View l m b l.cells i 0 0 0) v0
    (fun _ hi _ v => v.cable al ep hi) le_rfl
  have v2 := Phase.delivery.prefix_view l _ (fun i b => View l m b l.cells l.cableCount i 0 0) v1
    (fun _ hi _ v => v.delivery al ep hi) le_rfl
  have v3 := Phase.cableBins.prefix_view l _ (fun i b => View l m b l.cells l.cableCount l.deliveryCount i 0)
    v2 (fun _ _ _ v => v.cableBin al) le_rfl
  exact Phase.dataBins.prefix_view l _ (fun i b => View l m b l.cells l.cableCount l.deliveryCount (l.labels*l.labels) i)
    v3 (fun _ _ _ v => v.dataBin al) le_rfl

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
