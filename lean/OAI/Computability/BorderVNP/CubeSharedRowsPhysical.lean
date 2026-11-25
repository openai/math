import OAI.Computability.BorderVNP.CubeSharedRowsLoad
import OAI.Computability.BorderVNP.CubeISAOwnedPacketCount
import OAI.Computability.BorderVNP.CubeISALengthImage
import OAI.Computability.BorderVNP.CubeTeamNativeBudget
import OAI.Computability.BorderVNP.CubeGroupLoad

/-! # The shared seven-word records of a passing physical cube declaration

A strict symbol pair reserves its entire selector prefix and the bits crossing
the chosen cut. The two endpoint views belong to the teams found by the joint
weight scan. Each group charges the incident lists, its arriving data, and one
millionth of its raw padded wire load.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.SharedRows

open Physical RoutingISA.CubeLengths VPVNP.MotifBase

variable {n d blocks K h : ℕ}

/-- The physical selector prefix followed by the checked crossing bits of a distinct pair. -/
def reserved (blocks K h : ℕ) (D : LengthDeclaration n d) (p : Symbols d) : ℕ :=
  rowSelectorBits n d blocks K h D.1 (Sym2.mk p.val.1 p.val.2) + D.2 (Sym2.mk p.val.1 p.val.2) D.1

/-- Every shared list is charged once to each of its two incident groups. -/
def incident (blocks K h : ℕ) (D : LengthDeclaration n d) (s : Fin d) : ℕ :=
  ∑ p : Symbols d, if s = p.val.1 ∨ s = p.val.2 then reserved blocks K h D p else 0

/-- Total width of data descriptors arriving at one symbol group. -/
def dataAt {A : Type*} [Fintype A] (recv : A → Label (n+1) d) (width : A → ℕ)
    (i : Fin (n+1)) (s : Fin d) : ℕ :=
  ∑ a, if recv a i = s then width a else 0

/-- The actual Section 8.2 joint group weights in native fixed-point units. -/
def groupWords {A : Type*} [Fintype A] (recv : A → Label (n+1) d) (width : A → ℕ)
    (blocks K h b : ℕ) (D : LengthDeclaration n d) (j : ℕ) : ℕ :=
  if hj : j < d then TeamNative.scaledWeight (incident blocks K h D ⟨j,hj⟩)
    (dataAt recv width D.1 ⟨j,hj⟩) (groupRaw (blocks*(h*b)) D.1 ⟨j,hj⟩) else 0

/-- Dividing the stored weight by the common scale gives the paper's rational charge. -/
theorem groupWords_weight {A : Type*} [Fintype A] (recv : A → Label (n+1) d) (width : A → ℕ)
    (blocks K h b : ℕ) (D : LengthDeclaration n d) (j : Fin d) :
    TeamNative.unscale (groupWords recv width blocks K h b D j.val) =
      incident blocks K h D j + dataAt recv width D.1 j + (groupRaw (blocks*(h*b)) D.1 j : ℚ)/1000000 := by
  simpa only [groupWords,dite_eq_left j.isLt] using TeamNative.unscale_scaledWeight
    (incident blocks K h D j) (dataAt recv width D.1 j) (groupRaw (blocks*(h*b)) D.1 j)

/-- Both endpoints, including two groups assigned to the same team, incur the width charge. -/
theorem sum_incident (blocks K h : ℕ) (D : LengthDeclaration n d) :
    (∑ s, incident blocks K h D s) = 2 * ∑ p, reserved blocks K h D p := by
  simp only [incident,Finset.sum_comm (γ := Fin d),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have he : p.val.1 ≠ p.val.2 := p.property.ne
  have split (s : Fin d) :
      (if s = p.val.1 ∨ s = p.val.2 then reserved blocks K h D p else 0) =
      (if s = p.val.1 then reserved blocks K h D p else 0) +
      (if s = p.val.2 then reserved blocks K h D p else 0) := by
    by_cases a : s = p.val.1
    · subst s; simp [he]
    · simp [a]
  simp [split,Finset.sum_add_distrib,two_mul]

/-- Every data descriptor is charged to the unique group of its destination label. -/
theorem sum_dataAt {A : Type*} [Fintype A] (recv : A → Label (n+1) d) (width : A → ℕ)
    (i : Fin (n+1)) : (∑ s, dataAt recv width i s) = ∑ a, width a := by
  simp only [dataAt,Finset.sum_comm (γ := Fin d)]
  simp

/-- The shared writer's actual declaration inputs, including the closed selector prefix. -/
structure DeclarationFields (l : Layout) (mem : ℕ → ℕ) (blocks K h : ℕ) (D : LengthDeclaration n d) : Prop where
  /-- The shared group count equals the symbol alphabet size. -/
  groups : l.groups = d
  /-- All physical directions occur in each declared row. -/
  axes : l.axes = n+1
  /-- The grouping uses the declared coordinate word. -/
  axis : l.axis = D.1.val
  /-- The square array holds the declared unordered-pair widths. -/
  stored : StoredRows mem l.lengths D.2
  /-- Fixed-length selector prefix of each strict row. -/
  selectors : l.selectors =
    2*blocks*(d.choose 2)^n * VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h

/-- A physical row reserves exactly the packet selectors followed by the real cut bits. -/
theorem DeclarationFields.width {l : Layout} {mem : ℕ → ℕ} {D : LengthDeclaration n d}
    (f : DeclarationFields l mem blocks K h D) (p : Symbols d) :
    l.selectors + l.crossWidth mem p.val.1 p.val.2 = reserved blocks K h D p := by
  have hs := f.stored p.val.1 p.val.2 D.1
  rw [entryOrder_val,ite_eq_left p.property.le] at hs
  rw [← Nat.add_assoc] at hs
  rw [Layout.crossWidth,f.axes,f.axis,f.groups,hs,f.selectors,reserved,Owned.strict_rowSelectorBits]

/-- All seven output words of an actual strict pair: tag, both greedy owners, the
physical length, source word, and both ordered destination buffers. -/
theorem Layout.Image.physicalRow {l : Layout} {orig before mem : ℕ → ℕ} {D : LengthDeclaration n d}
    (image : l.Image before (l.dataCount+l.groups.choose 2) mem)
    (fields : DeclarationFields l before blocks K h D)
    (team : TeamNative.Layout) (ws : ℕ → ℕ) (tables : TeamNative.Tables team ws orig team.groups before)
    (teamGroups : team.groups = d) (teamOwners : l.owners = team.owners) (p : Symbols d) (j : Fin 7) :
    mem (l.address (l.rowIndex p.val.1 p.val.2)+j.val) =
      ![0,(TeamNative.owner team.r ws p.val.1).val,(TeamNative.owner team.r ws p.val.2).val,
        reserved blocks K h D p,0,l.view p.val.1 p.val.2,l.view p.val.2 p.val.1] j := by
  have hdst : p.val.2.val < l.groups := fields.groups ▸ p.val.2.isLt
  rw [image.rows _ hdst _ p.property (l.index_lt p.property hdst),Layout.row,
    fields.width p,teamOwners,tables.owners _ (teamGroups ▸ p.val.1.isLt),
    tables.owners _ (teamGroups ▸ p.val.2.isLt)]

/-- On a passing broadcast the shared width uses the actual subtotal of the
selected packets and singletons at the least minimizing coordinate. -/
theorem reserved_passing (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) (pass : passesLengths b s select D) (p : Symbols d) :
    reserved blocks K h D p = rowSelectorBits n d blocks K h (chosen b s select) (Sym2.mk p.val.1 p.val.2) +
      subtotals itemRow (crossCount b s select) (chosen b s select) (Sym2.mk p.val.1 p.val.2) (chosen b s select) := by
  rw [(passesLengths_iff ..).mp pass]
  rfl

/-- Read the public crossing words using the grouping coordinate of the selected path. -/
def decoded (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (raw : Broadcast n d (declarationCap n d blocks b h s)) : LengthDeclaration n d :=
  (chosen b s select,fun r i => readCode _ (raw.2 r i))

/-- The broadcast check forces the coordinate and every declared physical row. -/
theorem decoded_passes (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (raw : Broadcast n d (declarationCap n d blocks b h s)) (hp : passesBroadcast b s select raw) :
    readCode _ raw.1 = (decoded b s select raw).1.val ∧ passesLengths b s select (decoded b s select raw) := by
  obtain ⟨i,hi,passes⟩ := hp
  have eq : i = chosen b s select := congrArg Prod.fst ((passesLengths_iff ..).mp passes)
  subst i
  exact ⟨hi,passes⟩

/-- Reading the output of the shared pass on a passing broadcast gives the owners
chosen from the physical joint weights and the selector-plus-crossing payload of
the selected path. Both endpoint addresses use the ordered symbol-pair banks. -/
theorem Layout.Image.passingBroadcast {l : Layout} {orig before mem : ℕ → ℕ}
    (image : l.Image before (l.dataCount+l.groups.choose 2) mem)
    {A : Type*} [Fintype A] (recv : A → Label (n+1) d) (width : A → ℕ)
    (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (raw : Broadcast n d (declarationCap n d blocks b h s)) (hp : passesBroadcast b s select raw)
    (fields : DeclarationFields l before blocks K h (decoded b s select raw))
    (team : TeamNative.Layout) (tables : TeamNative.Tables team
      (groupWords recv width blocks K h b (decoded b s select raw)) orig team.groups before)
    (teamGroups : team.groups = d) (teamOwners : l.owners = team.owners) (p : Symbols d) (j : Fin 7) :
    let ws := groupWords recv width blocks K h b (decoded b s select raw)
    let i := chosen b s select
    let r := Sym2.mk p.val.1 p.val.2
    mem (l.address (l.rowIndex p.val.1 p.val.2)+j.val) =
      ![0,(TeamNative.owner team.r ws p.val.1).val,(TeamNative.owner team.r ws p.val.2).val,
        rowSelectorBits n d blocks K h i r + subtotals itemRow (crossCount b s select) i r i,
        0,l.view p.val.1 p.val.2,l.view p.val.2 p.val.1] j := by
  rw [image.physicalRow fields team _ tables teamGroups teamOwners p j]
  rw [reserved_passing b s select _ (decoded_passes b s select raw hp).2]


end Cube.SharedRows

end BorderVNP
end Computability
end OAI
