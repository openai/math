import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Native row expressions and the data they read for a stem candidate -/
namespace Hierarchy.DescentResetStemIncidence
open DescentPackedColony (target)
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
noncomputable section
variable {K H pitch w : ℕ}

/-- The physical actor can use its scan index for `here`, or an existing
identifier lookup if the actor rows have another order. -/
structure Ports (K : ℕ) where
  here : Expr
  near : Fin 3→Expr
  src : Fin K→Expr
  dst : Fin K→Expr
  oldHub : Fin K→Expr

structure Scene (K H pitch : ℕ) where
  here : Fin H→Fin pitch
  near : Fin pitch→Fin 3→Option (Fin pitch)
  ends : Fin K→Fin H→Option (Fin pitch×Fin pitch)
  oldHub : Fin K→Fin H→Bool

structure Reads (p : Ports K) (s : Scene K H pitch) (m : Memory w) : Prop where
  here : ∀r : Fin H,(p.here.eval m (r.val:Word w))=((s.here r).val:Word w)
  near : ∀r : Fin H,∀i,(p.near i).eval m (r.val:Word w)=(target (s.near (s.here r) i):Word w)
  src : ∀j,∀r : Fin H,(p.src j).eval m (r.val:Word w)=(target ((s.ends j r).map Prod.fst):Word w)
  dst : ∀j,∀r : Fin H,(p.dst j).eval m (r.val:Word w)=(target ((s.ends j r).map Prod.snd):Word w)
  oldHub : ∀j,∀r : Fin H,(p.oldHub j).eval m (r.val:Word w)=((s.oldHub j r).toNat:Word w)

structure Ports.All (p : Ports K) (P : Expr→Prop) : Prop where
  here : P p.here
  near : ∀i,P (p.near i)
  src : ∀i,P (p.src i)
  dst : ∀i,P (p.dst i)
  hub : ∀j,P (p.oldHub j)

end
end Hierarchy.DescentResetStemIncidence

end OAI
