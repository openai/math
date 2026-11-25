import OAI.Hierarchy.DescentReachedOriginTransport
import OAI.Hierarchy.DescentDatedRegisteredHeaders

namespace OAI
/-! Reading a newborn role field from the original W page and its measured chip. -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentSIMDLookup DescentScalarBookReshape DescentOrdinaryRasterReturn
open DescentSixParty.Chronology.PhysicalOrdinary
noncomputable section

def Values.withBirth {D k K cap H J a nb mb : ℕ}
    (v : Values D k K cap H J a nb mb)
    (f : Fin (2^k)→Fin cap→Fin 6→Fin H→Fin J→Cell a) :
    Values D k K cap H J a nb mb := {v with born:=f}

variable {D k K c H Q J r a nb mb D' k' K' c' Q' J' r' a' H' : ℕ}
variable (degree:D'=D) (depth:k'=k) (oldNodes:K'=K) (capacity:c'=c)
    (lo:Q'=Q) (gs:J'=J) (rad:r'=r) (field:a'=a) (wide:H≤H')
variable {C₀ H₀ G₀ a₀ : ℕ} (cB:C₀=c') (hB:H₀=H') (gB:G₀=J'*r') (aB:a₀=a')

/-- The chip lookup uses the old block, outgoing seat, original donor, and old group. -/
def Values.pulledBirth
    (f:Fin (2^k')→Fin C₀→Fin 6→Fin H₀→Fin G₀→Cell a₀)
    (b:Fin (2^k)) (s:Fin c) (t:Fin 6) (h:Fin H) (g:Fin (J*r)) : Cell a :=
  (f (b.cast (congrArg (2^·) depth.symm)) (s.cast (cB.trans capacity).symm) t
    ((h.castLE wide).cast hB.symm)
    (g.cast (gB.trans (congrArg₂ Nat.mul gs rad)).symm)).cast
      (congrArg (2^·) (aB.trans field))

theorem Values.native_birth_read
    (small:Fin Q→Values D k K c H (J*r) a nb mb)
    (large:Fin Q'→Values D' k' K' c' H' (J'*r') a' nb mb)
    (resident:∀l,Values.Prefix wide (Values.originTransport degree depth oldNodes capacity lo gs rad field small l)
      (large l))
    (f:Fin (2^k')→Fin C₀→Fin 6→Fin H₀→Fin G₀→Cell a₀)
    (N:ℕ) (u:Fin N) (b:Fin r) (h:Fin (H*Q)) (g:Fin J) :
    (take u (DescentScalarBookReshape.book (fun l x y=>((HeaderWords.reindex cB.symm hB.symm gB.symm aB.symm (large l)).withBirth f).book
      N x (y.cast gB.symm)) (b.cast rad.symm)
      ((widen wide (h.cast (congrArg (H*·) lo.symm))).cast (congrArg (·*Q') hB.symm))
      (g.cast gs.symm))).val =
    (take u (DescentScalarBookReshape.book (fun l x y=>((small l).withBirth
      (Values.pulledBirth depth capacity gs rad field wide cB hB gB aB f)).book N x y) b h g)).val :=by
  subst D'; subst k'; subst K'; subst c'; subst Q'; subst J'; subst r'; subst a'
  subst C₀; subst H₀; subst G₀; subst a₀
  let prior := fun l=>(small l).withBirth (fun b s t h g=>f b s t (h.castLE wide) g)
  let next := fun l=>(large l).withBirth f
  have projected (l) : Values.Prefix wide (prior l) (next l) :=
    ⟨(resident l).walks,(resident l).old,fun _ _ _ _ _=>rfl,(resident l).wanted,
      (resident l).venues,(resident l).counts⟩
  exact congrArg (fun word=>(take u word).val) (Values.Prefix.returned projected N b h g)

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

end OAI
