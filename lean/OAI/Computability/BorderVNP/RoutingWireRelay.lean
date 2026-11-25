import OAI.Computability.BorderVNP.RoutingWireReads
import OAI.Computability.BorderVNP.TransmissionAcross

/-! # The native relay test on the two physical message positions

Each routed data bit occurs once on each side of its relay. Reading the two
computed addresses in the relay's own RAM gives exactly the pair compared by
the global message check. Both words are genuine Boolean values.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
  {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}

/-- Reading a routed address at the relay gives the appropriate physical message
variable, even though the leg is indexed by its logical endpoint. -/
theorem TransferBank.read_relay_hop (hw : 0 < w) {v : Fin (R+1)}
    (A : TransferBank G pin ext L.width w L.header v) {u : Fin (R+1)}
    (p : Hop L.three L.width u v) :
    readings A.mem (routedAddress (readings A.pub) (readings A.mem) u v p.1 (p.2.val / ((R+1)-2))) =
      ((L.exteriorEquiv ext).hop u v p).toNat := by
  have hd := hop_ne_relay p
  obtain ⟨f0,f1,_,f3,f4,f5,_⟩ := A.schedule.frame
  have neq : v.val ≠ u.val := fun he => hd (Fin.ext he.symm)
  simp only [routedAddress,f0,f1,f3,f4,Wiring.transferFrame,ite_eq_right neq]
  exact G.read_message_leg L v u hd.symm pin ext A.ibase A.hbase A.starbase A.mem
    A.physical hw p (blockOf_swap ..) (readings A.pub) A.schedule.table f5

/-- Equality of the two initialized physical words at the checked quotient is
equivalent to equality of the two legs of this bit in the abstract routing message. -/
theorem TransferBank.relay_hop_iff (hw : 0 < w) {v : Fin (R+1)}
    (A : TransferBank G pin ext L.width w L.header v) {u : Fin (R+1)}
    (p : Hop L.three L.width u v) :
    RelayWordAgrees (readings A.pub) (readings A.mem) u v p.1 (p.2.val / ((R+1)-2)) ↔
      (L.exteriorEquiv ext).hop u v p =
        (L.exteriorEquiv ext).hop p.1 v (otherHop L.three L.width p) := by
  let p' := otherHop L.three L.width p
  have hr := A.read_relay_hop hw p'
  change readings A.mem (routedAddress (readings A.pub) (readings A.mem) p.1 v u (p.2.val/((R+1)-2))) = _ at hr
  rw [RelayWordAgrees,A.read_relay_hop hw p,hr]
  have inj : Function.Injective Bool.toNat := by decide
  exact ⟨fun h => inj h.1,fun h => ⟨congrArg Bool.toNat h,Bool.toNat_lt _⟩⟩

/-- On all relays together, the individual native tests impose precisely the
relay clause of the global physical-assignment check. -/
theorem transfer_relays_iff (hw : 0 < w) (A : ∀ v, TransferBank G pin ext L.width w L.header v) :
    (∀ (u v : Fin (R+1)) (p : Hop L.three L.width u v),
      RelayWordAgrees (readings (A v).pub) (readings (A v).mem) u v p.1 (p.2.val / ((R+1)-2))) ↔
      ∀ (u v : Fin (R+1)) (p : Hop L.three L.width u v),
        (L.exteriorEquiv ext).hop u v p = (L.exteriorEquiv ext).hop p.1 v (otherHop L.three L.width p) := by
  exact forall_congr' fun u => forall_congr' fun v => forall_congr' fun p => (A v).relay_hop_iff hw p

end TeamContraction

end BorderVNP
end Computability
end OAI
