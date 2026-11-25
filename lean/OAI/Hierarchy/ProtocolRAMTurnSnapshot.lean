import OAI.Hierarchy.ProtocolRAMTurnLiveRead

namespace OAI
/-! # Total numeric bank semantics for a history with arbitrary dormant entries -/

namespace Hierarchy.ProtocolRAMTurnSnapshot
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProtocolRAMTurnItinerary
open scoped Fin.CommRing
variable {W N : ℕ}

/-- Numerical contents have a value even on unoccupied words. No object of a
potentially empty type of physical ports is selected to interpret such a word. -/
def values (b : Banks) (m : Memory W) : Values where
  oldSource i := (b.oldSource.read m (i:Word W)).val
  oldTarget i := (b.oldTarget.read m (i:Word W)).val
  edge i := (b.edge.read m (i:Word W)).val
  tailSite i := (b.tailSite.read m (i:Word W)).val
  tailRole i := (b.tailRole.read m (i:Word W)).val
  headRole i := (b.headRole.read m (i:Word W)).val
  starts i := (b.starts.read m ((4*i:ℕ):Word W)).val

theorem adjacent (b : Banks) (m : Memory W) (t : Turn) : b.Adjacent (values b m) m t := by
  constructor
  · intro _; exact (Fin.cast_val_eq_self _).symm
  · intro _; exact (Fin.cast_val_eq_self _).symm
  · intro _ _; exact (Fin.cast_val_eq_self _).symm
  · intro _ _; exact (Fin.cast_val_eq_self _).symm
  · intro _ _; exact (Fin.cast_val_eq_self _).symm
  · intro _ _; exact (Fin.cast_val_eq_self _).symm
  · intro _ _; exact (Fin.cast_val_eq_self _).symm
  · intro _ _; exact Fin.isLt _

def turn (p : Chart) (m : Memory W) (i : Fin N) : Turn :=
  let x : Word W := i.val
  ⟨(p.item.eval m x).val,(p.origin.eval m x).val,(p.length.eval m x).val,(p.position.eval m x).val,
    decide (p.reverse.eval m x ≠ 0),(p.width.eval m x).val,(p.site.eval m x).val,(p.seat.eval m x).val⟩

theorem row (p : Chart) (m : Memory W) (i : Fin N) (one : 1 < 2^W)
    (binary : p.reverse.eval m (i.val:Word W)=0 ∨ p.reverse.eval m (i.val:Word W)=1) :
    p.Row m (i.val:Word W) (turn p m i) := by
  constructor
  · exact (Fin.cast_val_eq_self _).symm
  · exact (Fin.cast_val_eq_self _).symm
  · exact (Fin.cast_val_eq_self _).symm
  · exact (Fin.cast_val_eq_self _).symm
  · have nz : (1:Word W)≠0 := by
      intro hh
      have n:=congrArg Fin.val hh
      change ((1:ℕ):Word W).val=0 at n
      rw [Fin.val_cast_of_lt one] at n
      omega
    rcases binary with h|h <;> simp [turn,h,nz]
  · exact (Fin.cast_val_eq_self _).symm
  · exact (Fin.cast_val_eq_self _).symm
  · exact (Fin.cast_val_eq_self _).symm

/-- This issues the genuine seven-field scan on the committed memory. Its two
numeric prerequisites concern only the immutable route length and computed
direction flag. All port authentication is deferred to the positive records. -/
theorem observed (base : ℕ) (p : Chart) (b : Banks) (m : Memory W)
    (one : 1 < 2^W) (fit : ∀ f,(field p b f).Fits W base) (room : base+7*N < 2^W)
    (within : ∀i : Fin N,p.position.eval m (i.val:Word W) ≤ p.length.eval m (i.val:Word W))
    (binary : ∀i : Fin N,p.reverse.eval m (i.val:Word W)=0 ∨ p.reverse.eval m (i.val:Word W)=1) :
    let r := fun i : Fin N => turn p m i
    let v := values b m
    ∃ out,(program W base N p b).Exec m out (ticks base N p b) ∧
      (∀ (i : Fin N) (f : Fin 7), f=4 ∨ (r i).field v 4≠0 →
        out (base+f.val*N+i.val)=((r i).field v f:Word W)) ∧
      ∀ a,a<base ∨ base+7*N≤a → out a=m a := by
  intro r v
  apply observed_live base p b r v m one fit room (fun i=>within i)
  · intro i
    exact width_at p m _ _ (Fin.cast_val_eq_self _).symm (not_lt_of_ge (within i))
  · intro i _
    exact ⟨row p m i one (binary i),adjacent b m _,Fin.isLt _,Fin.isLt _⟩

end Hierarchy.ProtocolRAMTurnSnapshot

end OAI
