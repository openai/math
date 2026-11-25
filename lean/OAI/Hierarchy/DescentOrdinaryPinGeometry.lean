import OAI.Hierarchy.DescentPinCohorts

namespace OAI
/-! # The exterior binary chart of an ordinary physical radix step -/

namespace Hierarchy.DescentSixParty.PinCohorts
open DescentCompiler DescentGL DescentColonies DescentExterior
noncomputable section

variable {F P : Type} [Field F] {d k tail : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
  {W Y : MarkedWorld F d P bits} {i z D wire hist z' D' wire' hist' : ℕ}
  {r : Reached W G q ε S k i z D wire hist} {next : Reached Y G q ε S k (i+1) z' D' wire' hist'}

/-- Split off the remixed old block. The new host is determined by the old
host and block according to the physical chart supplied by this step. -/
def ordinaryGeometry (base : S.baseGroups=2^tail) (radix : S.radix=2^k) (age : i<S.length)
    (L : Layout k) {K : Type} (chart : next.V ↪ K) (label : r.V → Block k → K)
    (groups : ∀pin, ((next.placement.pos (Y.graph.attach pin)).1,next.placement.block (Y.graph.attach pin)) =
      S.groupDigits age radix (r.placement.pos (W.graph.attach pin)).1)
    (hosts : ∀pin, chart (host next pin) = label (host r pin) (r.placement.block (W.graph.attach pin))) :
    Step r next base radix := by
  let parts:=splitRows (S.groupWidth k tail i) k
  let trim:=castBits (S.group_cut (k:=k) (tail:=tail) age)
  refine ⟨parts.trans (trim.prodCongr L),?_,?_⟩
  · intro pin
    apply (address _).injective
    apply Fin.ext
    change (address _ (trim (parts (active r base radix pin)).1)).val=
      (address _ (active next base radix pin)).val
    rw [cast_address]
    rw [(active_parts r base radix pin).1]
    simp only [active,Equiv.apply_symm_apply]
    rw [groups pin]
    exact (group_address base radix age _).symm
  · intro a b old same
    change L (parts (active r base radix a)).2=L (parts (active r base radix b)).2 at same
    have oldBlock:=congrArg (address k) (L.injective same)
    rw [(active_parts r base radix a).2,(active_parts r base radix b).2] at oldBlock
    apply chart.injective
    rw [hosts a,hosts b,old,oldBlock]

end
end Hierarchy.DescentSixParty.PinCohorts

end OAI
