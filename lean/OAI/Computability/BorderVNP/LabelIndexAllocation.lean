import OAI.Computability.BorderVNP.LabelIndexVolumes

/-! # Physical label-index initialization from disjoint arrays and total width bounds -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA VPVNP.BurstRAM

/-- Widening a prefix and its nonnegative weights can only increase its volume. -/
theorem sumWidth_le {f g : ℕ → ℕ} {i j : ℕ} (hij : i ≤ j) (h : ∀ k < j, f k ≤ g k) :
    sumWidth f i ≤ sumWidth g j := by
  induction j generalizing i with
  | zero =>
    have eq : i = 0 := by omega
    simp [eq,sumWidth]
  | succ j ih =>
    by_cases eq : i = j+1
    · subst i
      exact Nat.add_le_add (ih le_rfl (fun k hk => h k (by omega))) (h j (by omega))
    · exact (ih (by omega) (fun k hk => h k (by omega))).trans (Nat.le_add_right ..)

/-- Physical word bounds on the allocated directory and the two aggregate input volumes. -/
structure Fits (l : Layout) (w : ℕ) (m : ℕ → ℕ) : Prop where
  /-- Address of the end of the final allocated array. -/
  addresses : l.dataMean+l.labels ≤ 2^w
  /-- Sum of cable widths including any absorbed row. -/
  cableWidth : sumWidth (Cable.width ∘ cableAt l m) l.cableCount < 2^w
  /-- Sum of all delivery widths. -/
  dataWidth : sumWidth (Prod.snd ∘ deliveryAt l m) l.deliveryCount < 2^w
  /-- Largest scaled initial demand. -/
  dataScaled : sumWidth (Prod.snd ∘ deliveryAt l m) l.deliveryCount*l.labels < 2^w

/-- The declared array allocations and input volumes bound every intermediate
address, subtotal and scaled mean, without any execution-dependent assumption. -/
theorem room_of_fits (l : Layout) (m : ℕ → ℕ) (w : ℕ) (al : Allocated l)
    (ep : Endpoints l m) (fit : Fits l w m) : room l w m := by
  let a : Acc := ⟨m,0,0⟩
  have v0 (i : ℕ) (hi : i ≤ l.cells) := Phase.clear.prefix_view l a (fun j b => View l m b j 0 0 0 0)
    (View.empty l m) (fun _ hj _ v => v.clear al hj) hi
  have v1 (i : ℕ) (hi : i ≤ l.cableCount) := Phase.cable.prefix_view l _
    (fun j b => View l m b l.cells j 0 0 0) (v0 _ le_rfl) (fun _ hj _ v => v.cable al ep hj) hi
  have v2 (i : ℕ) (hi : i ≤ l.deliveryCount) := Phase.delivery.prefix_view l _
    (fun j b => View l m b l.cells l.cableCount j 0 0) (v1 _ le_rfl)
    (fun _ hj _ v => v.delivery al ep hj) hi
  have v3 := Phase.cableBins.prefix_view l _ (fun i b => View l m b l.cells l.cableCount l.deliveryCount i 0)
    (v2 _ le_rfl) (fun _ _ _ v => v.cableBin al) le_rfl
  have v4 (i : ℕ) (hi : i ≤ l.labels) := Phase.dataBins.prefix_view l _
    (fun j b => View l m b l.cells l.cableCount l.deliveryCount (l.labels*l.labels) j)
    v3 (fun _ _ _ v => v.dataBin al) hi
  obtain ⟨ac,ad,ah,an,aData,ab⟩ := al
  have endBound := fit.addresses
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi
    exact ⟨by omega,by omega⟩
  · intro i hi
    let e := cableAt l m i
    have v := v1 i hi.le
    have same := v.input.cable ⟨ac,ad,ah,an,aData,ab⟩ hi
    have hs := congrArg Cable.src same
    have hd := congrArg Cable.dst same
    have hw := congrArg Cable.width same
    have ends := ep.cables i hi
    change e.src < l.cells ∧ e.dst < l.cells at ends
    let b := Phase.cable.prefix l (Phase.clear.prefix l a l.cells) i
    change b.mem (l.cables+i*3) = e.src at hs
    change b.mem (l.cables+i*3+1) = e.dst at hd
    change b.mem (l.cables+i*3+2) = e.width at hw
    have low := sumWidth_le (f := liveWidth ∘ cableAt l m) (g := Cable.width ∘ cableAt l m)
      (i := i) le_rfl (fun _ _ => by simp only [Function.comp_apply,liveWidth]; split <;> omega)
    have high := (sumWidth_le (f := Cable.width ∘ cableAt l m) hi (fun _ _ => le_rfl)).trans_lt fit.cableWidth
    change sumWidth (Cable.width ∘ cableAt l m) i+e.width < 2^w at high
    refine ⟨by omega,?_,?_,by omega,by omega,?_⟩
    · rw [hs]; omega
    · rw [hd]; omega
    · rw [v.cableTotal,hw]; omega
  · intro i hi
    let d := deliveryAt l m i
    have v := v2 i hi.le
    have same := v.input.delivery ⟨ac,ad,ah,an,aData,ab⟩ hi
    have hd := congrArg Prod.fst same
    have hw := congrArg Prod.snd same
    let b := Phase.delivery.prefix l (Phase.cable.prefix l (Phase.clear.prefix l a l.cells) l.cableCount) i
    change b.mem (l.deliveries+i*7+4) = d.1 at hd
    change b.mem (l.deliveries+i*7+6) = d.2 at hw
    have hc : d.1 < l.cells := ep.deliveries i hi
    have low := sumWidth_le (f := fun j => if (deliveryAt l m j).1 = d.1 then (deliveryAt l m j).2 else 0)
      (g := Prod.snd ∘ deliveryAt l m) (i := i) le_rfl (fun _ _ => by simp only [Function.comp_apply]; split <;> omega)
    have high := (sumWidth_le (f := Prod.snd ∘ deliveryAt l m) hi (fun _ _ => le_rfl)).trans_lt fit.dataWidth
    change sumWidth (Prod.snd ∘ deliveryAt l m) i+d.2 < 2^w at high
    refine ⟨by omega,?_,?_,?_⟩
    · rw [hd]; omega
    · rw [hd,hw,v.data _ hc]; omega
    · rw [hw,v.dataTotal]; exact high
  · intro i hi
    change l.cableMean+i < 2^w
    omega
  · intro i hi
    have v := v4 i hi.le
    exact ⟨by omega,v.dataTotal ▸ fit.dataScaled⟩

/-- From the actual frame and input rows, the physical program produces both
oriented linked lists, aggregate cell demands, and scaled initial moments with
a linear native tick bound. -/
theorem initializeDirectory {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) :
    let l := layout (pub 0).val (readings m)
    (pub 0).val+56 < 2^w → l.labels*l.labels < 2^w → Allocated l → Endpoints l (readings m) →
    Fits l w (readings m) →
    BoundedRun pub macros program s m
      (setup.slots + (Phase.clear.ticks l + (Phase.cable.ticks l + (Phase.delivery.ticks l +
        (Phase.cableBins.ticks l + Phase.dataBins.ticks l)))))
      (fun z => let a : Acc := ⟨z.mem,z.reg 18,z.reg 19⟩
        View l (readings m) a l.cells l.cableCount l.deliveryCount (l.labels*l.labels) l.labels) := by
  intro l hf hz al ep fit
  apply (program_runs pub macros s m hf hz (room_of_fits l _ w al ep fit)).mono le_rfl
  intro z h
  have eq : Acc.mk z.mem (z.reg 18) (z.reg 19) = image l (readings m) := by
    rw [h.2.2.2,h.2.1,h.2.2.1]
  rw [eq]
  exact image_view l _ al ep

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
