import OAI.Hierarchy.DescentDatedBookedMouth
import OAI.Hierarchy.DescentOrdinaryPageMarks

namespace OAI
/-! # All seven ordinary operand papers read the same stamped origin, including the newborn mouth -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryOriginMask DescentOrdinaryAtomFieldRAM DescentOrdinaryMouthReturn DescentOrdinaryBorn
open DescentSIMDLookup DescentOperandVectorArena DescentHaloWalkRAM DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

namespace HeaderWords
def stamp {D k K c H G a nb mb} (V : ScalarOperand.Values D k K c H G a nb mb)
    (bits nodes : ℕ) (j : Fin nodes) (h : Fin H) (g : Fin G) : ℕ :=
  ((encode bits nodes).symm (selection (DescentPackedActorMask.nodes (breadth D*2^k) K c) nodes bits (marked V h g)) j).val

theorem stamp_reindex {D k K c H G b n q c' H' G' b' : ℕ}
    (cap : c=c') (host : H=H') (groups : G=G') (bits : b=b')
    (x : ScalarOperand.Values D k K c H G b n q) (a nodes : ℕ) (j : Fin nodes) (h : Fin H') (g : Fin G') :
    stamp (reindex cap host groups bits x) a nodes j h g=stamp x a nodes j (h.cast host.symm) (g.cast groups.symm) :=by
  cases cap;cases host;cases groups;cases bits;rfl
end HeaderWords

variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (floor : ℕ) (A : v.ArgumentEntry) (mat : A.Match v floor)
local notation "bn₀" => v.bornBook
local notation "rc₀" => v.resolver
local notation "vx₀" => v.vector
local notation "rect₀" => References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity ((rc₀).size+2)
local notation "dir₀" => A.directory v floor mat

theorem original_mouth_stamp {w nb mb} (pg : Fin (vx₀).pageCount)
    (rows : rect₀ nb mb) (home : (bn₀).hosts=(vx₀).hosts) (group : (bn₀).groups=(vx₀).groups*(vx₀).radix)
    (word : (bn₀).bits=(rc₀).size+2) (m : Memory w)
    (pitch : 0<(vx₀).lanes*(vx₀).radix)
    (pages : ∀p q,ScalarOperand.Measured ((dir₀).refs p q) (rows p q) (rc₀).nodes ((vx₀).lanes*(vx₀).radix) (v.vectorStart floor) m)
    (arg : Fin (bn₀).args) (q : Fin (vx₀).lows) (node : Fin (rc₀).nodes) (bits : ℕ)
    (h : Fin (bn₀).hosts) (k : Fin (bn₀).groups) :
    HeaderWords.stamp (v.headerMouthRows floor A mat rows home group word arg q) bits (rc₀).nodes node h k=
      HeaderWords.stamp (rows pg q) bits (rc₀).nodes node (h.cast home) (k.cast group) :=by
  let other:=v.headerMouthPage floor A mat arg
  have same:=(dir₀).marked_pages pitch other pg q (rows other q) (rows pg q) (pages other q) (pages pg q)
  change HeaderWords.stamp (HeaderWords.reindex mat.newCap.symm home.symm group.symm word.symm (rows other q)) _ _ _ _ _=_
  rw [HeaderWords.stamp_reindex]
  have atRow := congrFun (congrFun same (h.cast home)) (k.cast group)
  unfold HeaderWords.stamp
  exact congrArg (fun mask => ((encode bits (rc₀).nodes).symm
    (selection _ (rc₀).nodes bits mask) node).val) atRow

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
