import OAI.Hierarchy.DescentResetWindowFields
import OAI.Hierarchy.DescentNextSignedRAM

namespace OAI
/-! # Size of the eight words on a physical candidate reset window -/
noncomputable section
namespace Hierarchy.DescentResetWindowFields
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase DescentNextSignedWindow
open DescentNextSignedWindow.Native
open scoped Classical
variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J]
  [Fintype V] [DecidableEq V] [Fintype E] {d k i : ℕ} {bits : P→ℕ}
  {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
local notation "B" => Stage.source A native
local notation "fit" => Stage.measured A native S ready
variable (C : Blocks (Stage.source A native) E) (marked : E→Prop)

omit [Fintype E] in
include ready in
theorem count_room (h : Stage.Host J V k) (x : Local C h) : C.count x.val≤A.cap := by
  let atSlot:=fun j : Fin (C.count x.val)=>(B).position fit h (Incidence.candidate C h x j)
  have inj : Function.Injective atSlot := by
    intro a b eqn
    have both:=((B).position fit h).injective eqn
    have same : (Sigma.mk x.val a : Σe,Fin (C.count e))=⟨x.val,b⟩:=
      C.order.injective (congrArg Subtype.val both)
    exact heq_iff_eq.mp (Sigma.mk.inj same).2
  simpa using Fintype.card_le_of_injective atSlot inj

private theorem field_bound {D cap : ℕ} (r : Record D cap)
    (position : r.position < cap) (source : r.atSource < cap)
    (shared : r.shared < cap) (mass : r.count ≤ cap) (j : Fin 8) :
    fields (some r) j ≤ max (D+1) (cap+1) := by
  have sign := Bool.toNat_le r.side
  have live := Bool.toNat_le r.marked
  have peer := r.neighbor.isLt
  have degree := Nat.le_max_left (D+1) (cap+1)
  have room := Nat.le_max_right (D+1) (cap+1)
  fin_cases j
  · change 1 ≤ _
    omega
  · change r.side.toNat ≤ _
    omega
  · change r.neighbor.val ≤ _
    omega
  · change r.marked.toNat ≤ _
    omega
  · change r.position ≤ _
    omega
  · change r.shared ≤ _
    omega
  · change r.atSource ≤ _
    omega
  · change r.count ≤ _
    omega

omit [Fintype E] in
theorem record_fields_le (h : Stage.Host J V k) (u : Roster.Face A native C h) (neighbor : Fin A.degree) (j : Fin 8) :
    fields (some (record A native S ready C marked h u neighbor)) j ≤ max (A.degree+1) (A.cap+1) := by
  let e:=u.val.1
  let first : Fin (C.count e):=⟨0,u.property.1⟩
  let rec₀:=record A native S ready C marked h u neighbor
  let root := C.src e
  let src : Local C root := ⟨e,u.property.1,Or.inl rfl⟩
  have inParallel : C.order ⟨e,first⟩∈(B).parallel root (C.dst e) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl ⟨C.atSource e first,C.atTarget e first⟩⟩
  apply field_bound rec₀
  · exact ((B).position fit h (Incidence.candidate C h (Roster.resident A native C h u) first)).isLt
  · exact ((B).position fit root (Incidence.candidate C root src first)).isLt
  · exact (B).serial_lt fit root (C.dst e) _ inParallel
  · exact count_room A native S ready C h (Roster.resident A native C h u)

end Hierarchy.DescentResetWindowFields
end

end OAI
