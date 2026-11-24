import OAI.Computability.VPVNP.PairShrinkRoleExact
import OAI.Computability.VPVNP.PairShrinkRoleChildTyped
import OAI.Computability.VPVNP.PairShrinkRoleHiddenTyped
import OAI.Computability.VPVNP.PairTreeNodeReaders

/-!
# Choice suffixes of shrinking visits

A successful visit consumes two adjacent fields: the independent arguments
of the placed children, followed by the owned absorbed words. Its deterministic
map scan decides acceptance on the resulting scratch and consumes no suffix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM DFS Compression CompressorRecords NetworkKernel
open LocalHistory NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess
open scoped Fin.CommRing

variable {w endAddr a g : ℕ} {α β : Type*}

private def Accepts (read : Reader w endAddr α) (node : Word w) (saved : Scratch w endAddr)
    (bs rest : List Bool) : Prop := ∃ out, read node saved bs = some (out,rest)

private theorem accepts_bind (first : Reader w endAddr α) (next : α → Reader w endAddr β)
    (node : Word w) (saved : Scratch w endAddr) (bs rest : List Bool) :
    Accepts (bind first next) node saved bs rest ↔ ∃ a tail,
      first node saved bs = some (a,tail) ∧ Accepts (next a.value) node a.updated tail rest := by
  cases ha : first node saved bs with
  | none => simp [Accepts, bind, ha]
  | some pair =>
    obtain ⟨a,tail⟩ := pair
    cases hb : next a.value node a.updated tail with
    | none => simp [Accepts, bind, ha, hb]
    | some pair => obtain ⟨b,remain⟩ := pair; simp [Accepts, bind, ha, hb]

private theorem accepts_maps (js : List (ResidentMapLoop.Exact.Action w endAddr))
    (node : Word w) (saved : Scratch w endAddr) (bs rest : List Bool) :
    Accepts (ResidentMapLoop.Exact.mapReader js) node saved bs rest ↔
      bs = rest ∧ (ResidentMapLoop.Exact.scan node js saved).isSome := by
  cases h : ResidentMapLoop.Exact.scan node js saved with
  | none => simp [Accepts, ResidentMapLoop.Exact.mapReader, h]
  | some pair => obtain ⟨es,out⟩ := pair; simp [Accepts, ResidentMapLoop.Exact.mapReader, h]

variable {X : State a g} (A : Arena) (T : IncidenceDirectory w) (m : Memory w)
  (older cap : ℕ) (desc : Word w → ChildArguments.Descriptor w X)
  (args : List (Child X) → Args w) (seed : List (Child X) → List Row)
  (maps : List (Child X) → List Row → List (ResidentMapLoop.Exact.Action w endAddr))
  (loadChild : Setup w endAddr) (loadHidden : List (Child X) → Setup w endAddr)
  (loadMaps : List (Child X) → List Row → Setup w endAddr)

/-- Exact acceptance, factoring out the deterministic setup stages. The old
and hidden results determine the actual starting scratch for the map checks. -/
theorem visitReader_suffix_iff (node : Word w) (saved : Scratch w endAddr) (bs rest : List Bool) :
    (∃ out, visitReader A T m older cap desc args seed maps loadChild loadHidden loadMaps
      node saved bs = some (out,rest)) ↔ ∃ old tail h,
      ChildArguments.reader A T m older cap desc node (loadChild.updated node saved) bs =
        some (old,tail) ∧
      hiddenReader (args old.value) m (seed old.value) node
        ((loadHidden old.value).updated node old.updated) tail = some (h,rest) ∧
      (ResidentMapLoop.Exact.scan node (maps old.value h.value)
        ((loadMaps old.value h.value).updated node h.updated)).isSome := by
  change Accepts _ _ _ _ _ ↔ _
  simp only [visitReader, accepts_bind, accepts_maps, Setup.reader, Option.some.injEq,
    Prod.mk.injEq, and_assoc]
  constructor
  · rintro ⟨_,_,rfl,rfl,old,tail,ho,_,_,rfl,rfl,h,_,hh,_,_,rfl,rfl,rfl,good⟩
    exact ⟨old,tail,h,ho,hh,good⟩
  · rintro ⟨old,tail,h,ho,hh,good⟩
    exact ⟨_,_,rfl,rfl,old,tail,ho,_,_,rfl,rfl,h,rest,hh,_,_,rfl,rfl,rfl,good⟩

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
