import OAI.Hierarchy.DescentIssuedNodeOrder
import OAI.Hierarchy.DescentGroupStage

namespace OAI
/-! # Physical key-major matching source ordinals before any branch profiles -/

namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentStageEdgeReceipt DescentHostDirectory
open scoped Classical
noncomputable section
variable {Q J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {H G k : ℕ}

def heap (z : ℕ×ℕ) := 2^z.1-1+z.2

private theorem limits {k : ℕ} {z : ℕ×ℕ} (legal : z∈codes k) : z.1≤k ∧ z.2<2^z.1 := by
  induction k with
  | zero => obtain rfl : z=(0,0) := Finset.mem_singleton.mp legal;decide
  | succ k ih =>
    rcases Finset.mem_union.mp legal with old|fresh
    · obtain ⟨d,h⟩ := ih old;exact ⟨d.trans (Nat.le_succ _),h⟩
    · obtain ⟨x,small,rfl⟩ := Finset.mem_image.mp fresh
      exact ⟨le_rfl,Finset.mem_range.mp small⟩

theorem heap_fits {z : ℕ×ℕ} (legal : z∈codes k) : heap z<2^(k+1) := by
  obtain ⟨small,at_⟩ := limits legal
  have bound := Nat.pow_le_pow_right (by decide : 0<2) small
  have positive := Nat.two_pow_pos z.1
  unfold heap
  rw [pow_succ]
  omega

private theorem heap_strict {a b : ℕ×ℕ} (inc : a.1<b.1) (first : a.2<2^a.1) : heap a<heap b := by
  have growth := Nat.pow_le_pow_right (by decide : 0<2) inc
  rw [pow_succ] at growth
  have pos := Nat.two_pow_pos a.1
  unfold heap
  omega

theorem heap_inj {a b : ℕ×ℕ} (ha : a∈codes k) (hb : b∈codes k) (eqn : heap a=heap b) : a=b := by
  obtain ⟨_,h⟩ := limits ha
  obtain ⟨_,h'⟩ := limits hb
  have de : a.1=b.1 := by
    rcases lt_trichotomy a.1 b.1 with lt|eqn'|gt
    · exact False.elim ((ne_of_lt (heap_strict lt h)) eqn)
    · exact eqn'
    · exact False.elim ((ne_of_lt (heap_strict gt h')) eqn.symm)
  exact Prod.ext de (by simpa only [heap,de,Nat.add_right_inj] using eqn)

/-- The physical source coordinates appear in the order of the key-major
scans, the old host word row, and the packed group lane. -/
def chartOf (k : ℕ) (address : Q↪(J×V)×(ℕ×ℕ)) (legal : ∀q,thickKey (address q)∈keys k 1)
    (groupName : J↪Fin G) (vertexName : V↪Fin H) : Q↪Fin (2^(k+1)*H*G) := by
  let law (q : Q) : (address q).2∈codes k := (Finset.mem_product.mp (Finset.mem_product.mp (legal q)).2).1
  let key (q : Q) : Fin (2^(k+1)) := ⟨heap (address q).2,heap_fits (law q)⟩
  exact ⟨fun q=>finProdFinEquiv (finProdFinEquiv (key q,vertexName (address q).1.2),groupName (address q).1.1),by
    intro x y eqn
    have rest := finProdFinEquiv.injective eqn
    have head := finProdFinEquiv.injective (congrArg Prod.fst rest)
    apply address.injective
    exact Prod.ext (Prod.ext (groupName.injective (congrArg Prod.snd rest)) (vertexName.injective (congrArg Prod.snd head)))
      (heap_inj (law x) (law y) (congrArg Fin.val (congrArg Prod.fst head)))⟩

omit [DecidableEq J] [DecidableEq V] in
theorem chartOf_val (k : ℕ) (address : Q↪(J×V)×(ℕ×ℕ)) (legal : ∀q,thickKey (address q)∈keys k 1)
    (groupName : J↪Fin G) (vertexName : V↪Fin H) (q : Q) :
    (chartOf k address legal groupName vertexName q).val=(heap (address q).2*H+(vertexName (address q).1.2).val)*G+
      (groupName (address q).1.1).val := by
  change (groupName (address q).1.1).val+G*((vertexName (address q).1.2).val+H*heap (address q).2)=_
  ring

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {Gadget : PoweredGadget F} {price ε : ℝ}

def sourceChart (he : 0≤ε) (A : GroupStage W Gadget price ε J V k) (groupName : J↪Fin G) (vertexName : V↪Fin H) :
    ScanColonies he A.stage ↪ Fin (2^(k+1)*H*G) :=
  chartOf k (nativeAddress he A.stage) (nativeAddress_legal he A.stage) groupName vertexName

theorem sourceChart_val (he : 0≤ε) (A : GroupStage W Gadget price ε J V k) (groupName : J↪Fin G) (vertexName : V↪Fin H)
    (q : ScanColonies he A.stage) :
    let z:=nativeAddress he A.stage q
    (sourceChart he A groupName vertexName q).val=((2^z.2.1-1+z.2.2)*H+(vertexName z.1.2).val)*G+(groupName z.1.1).val :=
  chartOf_val k (nativeAddress he A.stage) (nativeAddress_legal he A.stage) groupName vertexName q

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
