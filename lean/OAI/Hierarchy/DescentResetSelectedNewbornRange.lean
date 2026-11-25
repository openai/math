import OAI.Hierarchy.DescentResetSelectedRange

namespace OAI
/-! # The exact newborn source contributing each installed range field -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentRetainedRangeDigits DescentBundleHistory DescentResetPublicOperandBook
open DescentResetOperandSetup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "cfg" => publicOperands z roots menu.payload
local notation "C" => a.successor.setup
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
variable (Y : Fin (a.successor.setup.retained.outputs*a.successor.setup.placement.shapes)→Fin a.successor.setup.placement.oldHosts→
    Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.retained.bits)
variable (j : Fin a.successor.setup.retained.outputs) (block : Fin a.successor.setup.placement.blocks)
variable (host : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
variable (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (arg : Fin (publicOperands z roots menu.payload).args) (node : Fin (publicOperands z roots menu.payload).nodes)
local notation "idx" => (finProdFinEquiv (arg,node) : Fin (cfg).mouths)
local notation "private_" f:arg => (cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
  node.val arg.val (DescentRetainedRangeDigits.page f).succ ((cfg).reg x)
variable (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → ((publicOperands z roots menu.payload).reg x 1).val=0)
    (physical : ∀hv : host.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
      ((publicOperands z roots menu.payload).reg x 3).val=(a.successor.setup.placement.shape (name ⟨host.val,hv⟩)).val)
    (free : ∀hv : host.val<U,menu.keep (a.successor.setup.placement.shape (name ⟨host.val,hv⟩))=false)
local notation "observed" f:arg => menu.spanValue name Y j block host g x idx (DescentRetainedRangeDigits.page f) blank physical

include free in
theorem selected_private_range (active : 0<private_ (2:Fin 3)) (f : Fin 3) :
    observed f=(private_ f : Cell (C).fieldBits) := by
  have absent : (cfg).mixed z.board node.val arg.val x=none := by
    cases eqn : (cfg).mixed z.board node.val arg.val x with
    | none=>rfl
    | some item=>
      have dead:=(cfg).mixed_excludes_private z.board node.val arg.val (cfg).split x item eqn (page (2:Fin 3)).succ
      exact False.elim ((Nat.ne_of_gt active) dead)
  apply Fin.ext
  rw [menu.spanValue_newborn name Y j block host g x idx (page f) blank physical free]
  simp only [Config.column,Equiv.symm_apply_apply,absent,Fin.val_zero,Nat.add_zero]

include free in
theorem selected_public_range (port original count : ℕ) (marked : Bool)
    (arrived : (cfg).mixed z.board node.val arg.val x=some (port,original,count,marked)) (f : Fin 3) :
    observed f=(value ⟨0,1,count⟩ f:Cell (C).fieldBits) := by
  have dead:=(cfg).mixed_excludes_private z.board node.val arg.val (cfg).split x _ arrived (page f).succ
  apply Fin.ext
  rw [menu.spanValue_newborn name Y j block host g x idx (page f) blank physical free]
  simp only [Equiv.symm_apply_apply,dead,Nat.cast_zero,Fin.val_zero,Nat.zero_add,Config.column,arrived]
  fin_cases f <;> rfl

include free in
/-- At every fallback argument, or a public rotor argument past the private spine,
the range digit is read directly from its genuine mixed lookup. This also
covers the last partially populated word and every following padding word. -/
theorem selected_surface_word (f : Fin 3) (missing : private_ f=0) :
    (observed f).val=((cfg).column z.board (C).fieldBits (some (page f)) idx x).val := by
  rw [menu.spanValue_newborn name Y j block host g x idx (page f) blank physical free]
  simp only [Equiv.symm_apply_apply,missing,Nat.cast_zero,Fin.val_zero,Nat.zero_add]


include free in
theorem selected_missing_range (absent : (cfg).mixed z.board node.val arg.val x=none)
    (f : Fin 3) (missing : private_ f=0) : observed f=0 :=by
  apply Fin.ext
  rw [menu.spanValue_newborn name Y j block host g x idx (page f) blank physical free]
  simp only [Equiv.symm_apply_apply,Config.column,absent,missing,Nat.cast_zero,Fin.val_zero,Nat.add_zero]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

namespace Hierarchy.DescentRetainedRangeDigits
open DescentBundleHistory DescentKernelHistory
noncomputable section
variable {p : ℕ} {U V : Type} {w : V→ℕ} {r : BitRecipe U V w}
theorem atSlot_count_pos (s : Shape p r) (u : r.Node) (j : Fin (occurrences s u).length) :
    0<atSlot s u j.val 2 := by
  let c:=(occurrences s u)[j.val]
  have mem : c∈occurrences s u:=List.getElem_mem j.isLt
  obtain ⟨row,_,inside⟩:=List.mem_flatMap.mp mem
  obtain ⟨desc,_,inCopies⟩:=List.mem_flatMap.mp inside
  obtain ⟨positive,same⟩:=List.mem_replicate.mp inCopies
  have bound : 0<c.count:=by rw [same];exact Nat.pos_of_ne_zero positive
  simp only [atSlot,List.getElem?_eq_getElem j.isLt,Option.elim_some]
  exact bound
end
end Hierarchy.DescentRetainedRangeDigits

end OAI
