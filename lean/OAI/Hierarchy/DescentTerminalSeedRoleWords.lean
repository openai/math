import OAI.Hierarchy.DescentTerminalRoleBirthWords
import OAI.Hierarchy.DescentSliceFields
import OAI.Hierarchy.DescentPackedSeedLegs

namespace OAI
/-! # Primitive seed panel from the original vertex header and fixed aligned stack width -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentKernelHistory DescentBundleHistory DescentSixParty DescentPackedSeed DescentInitialHost
open DescentSeedRoot DescentEpochTagKeys Computability.BorderVNP.Crossing Catalyst
open scoped Classical BigOperators
noncomputable section
variable {F:Type} [Field F] {k n copies s p:ℕ} (X : Approximation F k n) (c : (initialGroup X copies s).Choice)
    (j : Fin copies) (v : Vertex X) (hp:0<p) (divides:p∣s)

/-- At every seed vertex the slice field depends only on the measured local leg count and the public stack width. -/
theorem seed_slices (u : (initialRecipe X copies s c ⟨j,v⟩).Node) :
    (initialShape X copies s c ⟨j,v⟩ hp divides).sliceFields u=List.replicate (legArity X v) (List.replicate (s/p) (⟨0,1,1⟩:SliceCode)) := by
  let sh := initialShape X copies s c ⟨j,v⟩ hp divides
  change sh.sliceFields u = _
  unfold Shape.sliceFields
  have one (i) : (List.ofFn (fun g=>(sh.chunk u i g).code))=List.replicate (s/p) (⟨0,1,1⟩:SliceCode) := by
    calc
      _ = List.ofFn (fun _ : Fin (sh.groups u i)=>(⟨0,1,1⟩:SliceCode)) := by
        apply congrArg List.ofFn;funext g
        have part:=operand_window X c hp divides j v u i g
        change SliceCode.mk _ _ _=_
        rw [part.1,part.2.1,part.2.2.1]
      _ = _ := by rw [List.ofFn_const,initial_groups X copies s c ⟨j,v⟩ hp divides u i]
  simp_rw [one]
  rw [List.ofFn_const]
  exact congrArg (fun count : ℕ => List.replicate count (List.replicate (s/p) (⟨0,1,1⟩ : SliceCode)))
    (recipe_arity X c j v u)

theorem seed_printed {P:Type} {colors A grains R:ℕ} (dict:Codec P colors) (role:P)
    (u : (initialRecipe X copies s c ⟨j,v⟩).Node)
    (valid:DescentBundleTagKeys.Fits dict A grains p R (role,(initialShape X copies s c ⟨j,v⟩ hp divides).sliceFields u)) :
    Printed dict (fields (rawWords (n:=colors) (p:=p) (R:=R)
      (birth (A:=A) (G:=grains) dict role (List.replicate (legArity X v) (List.replicate (s/p) (⟨0,1,1⟩:SliceCode))))))
      role ((initialShape X copies s c ⟨j,v⟩ hp divides).sliceFields u) := by
  rw [←seed_slices X c j v hp divides u];exact birth_printed dict _ _ valid

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
