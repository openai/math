import OAI.Computability.BorderVNP.CubeHostScatterPhysicalEnds
import OAI.Computability.BorderVNP.CubeRouteCommonOwners

/-! # Recovering the host's source columns from the native interval and pair-directory images -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA RoutingISA.Evaluator RoutingISA.CubeArena RoutingISA.LocalRow VPVNP.BurstRAM Physical Physical.Owned Tally
open private array_word from OAI.Computability.BorderVNP.CubeRouteCommonOwners

variable {ar : CubeArena.Layout} {il : NativeIntervals.Layout} {w frame controls R broadcast : ℕ}
variable {axis : Fin (ar.n+1)} {before dir orig after mem : ℕ → ℕ}

/-- Geometry of the genuine processed cable and chooser arrays. Every cable row is
stored below the secondary header, and its labels and ordinal belong to the public arena. -/
structure CableColumns (ar : CubeArena.Layout) (frame : ℕ) (il : NativeIntervals.Layout) (before : ℕ → ℕ) : Prop where
  labels : il.labels = ar.publicBase
  ordinals : il.ordinals = ar.ordinalBase
  cables : frame+112 ≤ il.cables ∧ il.cables+3*il.count ≤ ar.header.header
  count : il.count ≤ ar.cables
  endpoints : ∀ i < il.count, il.src before i < ar.cells ∧ il.dst before i < ar.cells

/-- Actual pre-transmission directory construction and the returned interval image
supply all host columns, including unused rows and diagonal or antipodal label pairs.
Only memory words outside the evaluator's mutating arrays are transported. -/
theorem residentRows_of_columns (l : Layout) (space : CableColumns ar frame il before)
    (fit : NativeIntervals.Layout.Fits il w before) (interval : il.Image before il.count dir)
    (low : ∀ x < ar.publicBase, dir x = orig x)
    (entry : NativeEntry ar frame controls axis R (powerHeaderImage ar broadcast dir) orig after)
    (primary : frame+112 ≤ ar.header.header)
    (transfer : ∀ x, x < ar.records → (x < ar.header.header+13 ∨ ar.publicBase ≤ x) →
      x ≠ frame+13 → x ≠ frame+46 → mem x = after x)
    (shape : l.count = il.count ∧ l.alphabet = il.alphabet ∧ l.cables = il.cables ∧ l.labels = il.labels ∧
      l.ordinals = il.ordinals ∧ l.pairs = ar.pairDirectory)
    (banks : l.blocks = ar.header.blocks ∧ l.bc = ar.h*ar.b ∧ l.bankWidth = bankWidth ar.n ar.b ar.h ar.K ar.s ∧
      l.selectorWidth = selectorWidth ar.n ar.K ar.h) :
    ResidentRows l il before dir mem ar.n ar.header.d ar.header.blocks ar.b ar.h ar.K ar.s := by
  obtain ⟨num,alpha,cables,labels,ordinals,pairs⟩ := shape
  obtain ⟨scheduled,result,written⟩ := entry.image
  obtain ⟨hdr,labHi,group,owners,pairEnd,hostEnd,_,_⟩ := ar.writer_order
  have groupLow : ar.publicBase ≤ ar.groupWeights := (Nat.le_add_right ..).trans labHi
  have power : ar.powerBase ≤ ar.groupWeights := (Nat.le_add_right ..).trans ar.group_order.2.2.2.2.2.2.2.1
  have above (x : ℕ) (lo : ar.publicBase ≤ x) (hi : x < ar.records) : mem x = after x :=
    transfer x hi (.inr lo) (by omega) (by omega)
  have selected (x : ℕ) (lo : ar.publicBase ≤ x) (hi : x < ar.powerBase) : mem x = dir x :=
    (above x lo (by omega)).trans ((scheduled_before ar result written.pairRows ⟨rfl,rfl,rfl,rfl,rfl⟩ (by omega)).trans
      (array_word ar dir broadcast lo hi))
  have cable (r : Fin il.count) (off : ℕ) (lim : off < 3)
      (word : il.cables+3*r.val+off ∈ [il.cables+3*r.val,il.cables+3*r.val+1,il.cables+3*r.val+2,
        il.labels+il.src before r.val,il.labels+il.dst before r.val]) :
      mem (il.cables+3*r.val+off) = before (il.cables+3*r.val+off) := by
    have bounds := space.cables
    have valid := r.isLt
    have preserve := fit.input r.val valid _ word
    exact (transfer _ (by omega) (.inl (by omega)) (by omega) (by omega)).trans
      ((entry.low _ (by omega)).trans ((low _ (by omega)).symm.trans (interval.outside _ preserve.1 preserve.2)))
  have endpoints (r : Fin il.count) : l.cell mem r.val false = il.src before r.val ∧
      l.cell mem r.val true = il.dst before r.val ∧ l.width mem r.val = il.width before r.val := by
    simp only [Layout.cell,Layout.width,NativeIntervals.Layout.src,NativeIntervals.Layout.dst,NativeIntervals.Layout.width,
      cables,Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
    exact ⟨cable r 0 (by decide) (by simp),cable r 1 (by decide) (by simp),cable r 2 (by decide) (by simp)⟩
  have labelHi := (arena_label_arrays ar).2.1
  have ordinalLo := ar.group_order.2.2.2.2.2.1
  have ordinalEnd : ar.ordinalBase+ar.cables = ar.powerBase := rfl
  refine ⟨num,alpha,endpoints,?_,?_,?_,banks⟩
  · intro r side
    rw [labels]
    have valid := space.endpoints r.val r.isLt
    have cell : l.cell mem r.val side < ar.cells := by cases side <;> first
      | exact (endpoints r).1 ▸ valid.1
      | exact (endpoints r).2.1 ▸ valid.2
    have atLabel : il.labels+l.cell mem r.val side ∈
        [il.cables+3*r.val,il.cables+3*r.val+1,il.cables+3*r.val+2,il.labels+il.src before r.val,il.labels+il.dst before r.val] := by
      cases side
      · simp [(endpoints r).1]
      · simp [(endpoints r).2.1]
    have preserve := fit.input r.val r.isLt _ atLabel
    exact (selected _ (space.labels ▸ Nat.le_add_right ..) (by rw [space.labels]; omega)).trans (interval.outside _ preserve.1 preserve.2)
  · intro r
    rw [ordinals]
    have bound := r.isLt.trans_le space.count
    exact selected _ (space.ordinals ▸ ordinalLo.trans (Nat.le_add_right ..)) (by rw [space.ordinals]; omega)
  · have result := Padding.tripleWords_of_image (n := ar.n) written.pairRows rfl
    intro u v
    let x := ar.pairDirectory+3*(HostAddress.code u*ar.header.d^(ar.n+1)+HostAddress.code v)
    have pos : ar.publicBase ≤ x := by dsimp only [x]; omega
    have upper : x+2 < ar.records := by
      have key := (finProdFinEquiv (finFunctionFinEquiv u,finFunctionFinEquiv v)).isLt
      change HostAddress.code v+ar.header.d^(ar.n+1)*HostAddress.code u < ar.header.d^(ar.n+1)*ar.header.d^(ar.n+1) at key
      have small : HostAddress.code u*ar.header.d^(ar.n+1)+HostAddress.code v < ar.alphabet^2 := by
        simpa only [CubeArena.Layout.alphabet,pow_two,Nat.add_comm,Nat.mul_comm] using key
      dsimp only [x]; omega
    rw [pairs]
    exact ⟨(above x pos (by omega)).trans (result u v).1,(above _ (by omega) (by omega)).trans (result u v).2.1,
      (above _ (by omega) upper).trans (result u v).2.2⟩

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
