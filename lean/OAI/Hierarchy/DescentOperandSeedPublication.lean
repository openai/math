import OAI.Hierarchy.DescentSeedOperandStamp
import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentOperandSeedState
import OAI.Hierarchy.DescentPackedSeedCopyOrdinal

namespace OAI
/-! # Cables and stamped exterior references on the same installed native seed image -/
namespace Hierarchy.DescentOperandStateBanks.Seed
open DescentPackedSeed DescentSeedRoot DescentInitialHost DescentKernelHistory DescentBundleHistory DescentColonies DescentSIMDLookup
open Computability.BorderVNP.Crossing DescentSixParty ThreeFlat Routing Catalyst Diagonal
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F J : Type} [_root_.Field F] [Fintype J] [DecidableEq J] {k n groups d R s w M b : ℕ}
    (X : Approximation F k n) (c : (initialGroup X R s).Choice) (name : J≃Fin groups)
    (digits : Fin R≃J×Block d)


omit [Fintype J] [DecidableEq J] in
theorem stamp_read (wide : 2<2^w) (base : ℕ) (m : Memory w)
    (room : stampStart X base+CopyOrdinal.words d groups M<2^w)
    (hm : 0<M) (word : b*M≤w) (fits : R≤2^b)
    (j : Fin R) (v : Vertex X) (u : (initialRecipe X R s c ⟨j,v⟩).Node)
    (i : Fin ((initialRecipe X R s c ⟨j,v⟩).arity u)) (g : ℕ) (f : Field) :
    let next:=stampImage X name digits base M b m
    let group:=(seedPos X c digits ⟨j,v⟩).1
    let block:=seedBlock X c digits ⟨j,v⟩
    let ticket:=digit b (lane (name group) hm).val
      (next (stampStart X base+(row _ _ _ (position block (name group) hm)).val)).val
    let ordinal:=Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i
    let leg₀:=leg X v (Fin.cast (recipe_arity X c j v u) i)
    withStamp (field X base v ordinal g next) (ticket:Computability.VPVNP.BurstRAM.Word w) f =
      ((originalAt X v leg₀ j.val g).fields ⟨0,1,1⟩ f : Computability.VPVNP.BurstRAM.Word w) := by
  intro next grp blk ticket ordinal leg₀
  obtain ⟨_,_,read,localFrame⟩:=CopyOrdinal.issued (M:=M) (b:=b) name digits (stampStart X base) (image X base m) room
  have actual : ticket=j.val := CopyOrdinal.seed_digits name digits X c (stampStart X base) next hm word fits read j v
  have keep (z : ℕ) (low : z<stampStart X base) : next z=image X base m z := localFrame z (.inl low)
  have baseFits:= (order X (v,ordinal)).isLt
  have peer : (Signed.address X (v,ordinal,0)).val < Signed.size X :=
    (Signed.address X (v,ordinal,0)).isLt
  have serial : (Signed.address X (v,ordinal,1)).val < Signed.size X :=
    (Signed.address X (v,ordinal,1)).isLt
  have table : field X base v ordinal g next=field X base v ordinal g (image X base m) := by
    unfold field
    rw [keep (base+Signed.size X+(order X (v,ordinal)).val) (by unfold stampStart;omega),
      keep (base+(Signed.address X (v,ordinal,0)).val) (by unfold stampStart;omega),
      keep (base+(Signed.address X (v,ordinal,1)).val) (by unfold stampStart;omega)]
  rw [actual,table]
  exact stamped X c wide base m j v u i g f

end
end Hierarchy.DescentOperandStateBanks.Seed

end OAI
