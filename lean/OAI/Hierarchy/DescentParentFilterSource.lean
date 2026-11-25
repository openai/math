import OAI.Hierarchy.DescentPackedParentFilterRAM
import OAI.Hierarchy.DescentOrdinaryParallelSide

namespace OAI
/-! # Literal donor-walk labels for the two-sided parent classifier -/
namespace Hierarchy.DescentParallelBase.ParentFilter
open DescentSIMDLookup DescentHaloWalkRAM DescentPacking.PackedMatch.Local DescentHostDirectory
open scoped Classical
noncomputable section
variable {Z : Type} [Fintype Z] [DecidableEq Z] {H D k g slots K L : ℕ}
local notation "P" => breadth D
local notation "Q" => 2^(k+1)*slots

def printed (D k g slots : ℕ) (positive : 0<slots) (w : Walk) (hub : Bool) : Endpoint (breadth D) (2^(k+1)*slots) where
  path:=ActorPath.index D w
  low:=⟨(SiteDecode.trim k g slots hub (w.2.2.1*slots+w.2.2.2))%(2^(k+1)*slots),Nat.mod_lt _ (Nat.mul_pos (Nat.two_pow_pos _) positive)⟩

def venue (name : Z→Fin H) (hub : Z→Bool) (x : Key Z) (legal : x∈keys k slots) : Fin H×Fin Q:=
  (name x.1,⟨SiteDecode.localNumber k slots (mergeHub hub k g x),by
    rw [←SiteDecode.trim_key k g slots hub x legal];exact SiteDecode.trim_lt k g slots hub x legal⟩)

omit [DecidableEq Z] in
theorem printed_at (next : Z→Fin D→Option Z) (name : Z→Fin H) (R : Fin H→Fin D→Option (Fin H))
    (real : ∀z i y,next z i=some y→R (name z) i=some (name y)) (root : Z) (w : Walk) (x : Key Z) (hit : walked next root w x)
    (hub : Z→Bool) (legal : x∈keys k slots) (pos : 0<slots) :
    let read:=printed D k g slots pos w (hub x.1)
    Gather.reaching R (name root) read.path=some (venue (g:=g) name hub x legal).1 ∧ read.low=(venue (g:=g) name hub x legal).2 :=by
  intro read;refine ⟨ActorPath.emitted next name R real root w x hit,?_⟩
  have low : w.2.2.1*slots+w.2.2.2=SiteDecode.localNumber k slots x:=by
    have got:=hit.2;rw [show w.2.2.1=heap x.2.1 from congrArg Prod.fst got,show w.2.2.2=x.2.2 from congrArg Prod.snd got]
    simp [SiteDecode.localNumber,packedNumber,heap,nodeNumber]
  apply Fin.ext;change (SiteDecode.trim k g slots (hub x.1) (w.2.2.1*slots+w.2.2.2))%Q=SiteDecode.localNumber k slots (mergeHub hub k g x)
  rw [low,Nat.mod_eq_of_lt (SiteDecode.trim_lt k g slots hub x legal),SiteDecode.trim_key k g slots hub x legal]

/-- Only the two actual relative walk words, their destination hub bits and
the compact previous chronology enter this local record. -/
def programmed (pos : 0<slots) (w : Walk×Walk) (hubS hubT upper : Bool) (key : Fin K) (mass : Fin (L+1)) : Source P Q K L :=
  ⟨printed D k g slots pos w.1 hubS,printed D k g slots pos w.2 hubT,upper,key,mass⟩

omit [DecidableEq Z] in
theorem programmed_actual (next : Z→Fin D→Option Z) (name : Z→Fin H) (R : Fin H→Fin D→Option (Fin H))
    (real : ∀z i y,next z i=some y→R (name z) i=some (name y)) (root : Z) (w : Walk×Walk) (x y : Key Z) (truth : ParentIncidence.Actual next root w x y)
    (hub : Z→Bool) (xok : x∈keys k slots) (yok : y∈keys k slots) (pos : 0<slots) (upper : Bool) (key : Fin K) (mass : Fin (L+1)) :
    Witness R (name root) (programmed (k:=k) (g:=g) pos w (hub x.1) (hub y.1) upper key mass)
      (venue (g:=g) name hub x xok) (venue (g:=g) name hub y yok) :=by
  have s:=printed_at (g:=g) next name R real root w.1 x truth.src hub xok pos
  have t:=printed_at (g:=g) next name R real root w.2 y truth.dst hub yok pos
  exact ⟨s.1,t.1,s.2,t.2⟩

end
end Hierarchy.DescentParallelBase.ParentFilter

end OAI
