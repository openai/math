import OAI.Hierarchy.DescentDatedStageVenue

namespace OAI
/-! # Earlier native venue rows survive later dated writes -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentPackedColony DescentColonies DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] {u : ℕ} {bits : P→ℕ} {W : MarkedWorld F u P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D wire s H w : ℕ}
    (r : Reached W G q ε S k age z D wire s) (wide : Fintype.card r.V≤H)
    (i : Dated.Operands) (M countBits floor : ℕ) (rs : Fin H→Fin D→Option (Fin H))
local notation "g" => S.groupCount age

theorem stageVenue_below (m n : Memory w) (old : stageVenue r wide i M countBits floor rs m)
    (signed : ∀(x:Block k) (j:Fin (2*r.placement.cap)),
      (i.wire x.val j.val).base+H*chunks g M≤floor)
    (same : ∀a,a<floor→n a=m a) : stageVenue r wide i M countBits floor rs n :=by
  rcases old with ⟨ca,roster,actors,wires,hubs,slots,hub,atomFits,atoms⟩
  have slab {T : Bank} {a rows : ℕ} (live : a<rows) (end_ : T.base+rows≤floor) :
      n (T.base+a)=m (T.base+a):=same _ ((Nat.add_lt_add_left live T.base).trans_le end_)
  have bank {T : Bank} {a rows : ℕ} (live : a<rows) (size : rows≤T.size) (fit : T.Fits w floor) :
      n (T.base+a)=m (T.base+a):=slab live ((Nat.add_le_add_left size _).trans fit.2.2)
  refine ⟨ca,?_,?_,?_,hubs,slots,?_,atomFits,?_⟩
  · constructor
    · intro p j;exact (bank (row H g M p).isLt (ca.idsRoom j) (ca.ids j)).trans (roster.ids p j)
    · intro v j
      have ends:=Nat.mul_le_mul_right D v.isLt
      rw [Nat.succ_mul] at ends
      have live:=j.isLt
      exact (bank (show v.val*D+j.val<H*D by omega) ca.rosterRoom ca.roster).trans (roster.roster v j)
    · intro v;exact (bank v.isLt ca.offRoom ca.offsets).trans (roster.offsets v)
    · intro p;exact (bank (row H g M p).isLt ca.chunkRoom ca.chunks).trans (roster.chunks p)
  · intro p;exact (bank (row H g M p).isLt ca.srcRoom ca.source).trans (actors p)
  · intro x j p;exact (slab (row H g M p).isLt (signed x j)).trans (wires x j p)
  · intro h;exact (bank h.isLt slots hubs).trans (hub h)
  · intro x p
    exact (ProtocolRAM.eval_below _ _ m n (atomFits _) same).trans (atoms x p)

end
end Hierarchy.DescentSixParty

end OAI
