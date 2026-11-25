import OAI.Computability.BorderVNP.TransmissionExteriorWire
import OAI.Computability.BorderVNP.TransmissionSafe
import OAI.Computability.BorderVNP.RoutingISARelayModel

/-! # Cross-team consistency of native endpoint reads

The sender, relay and recipient may have different scratch states. The processor input
images share the same exterior variables, and the built scheduling tables assign both
ends of each physical block the same position.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission

variable {R r t d link inner n w header : ℕ} {Edge : Type}
variable {G : Wiring R r t d link inner n Edge} {pin : Fin d → Bool}
variable {ext : Exterior R r link → Bool} {width : Fin (R+1) → Fin (R+1) → ℕ}

/-- The actual routing frame for one team in the common physical wiring. -/
def Wiring.transferFrame (G : Wiring R r t d link inner n Edge) (team : Fin (R+1))
    (header dst : ℕ) : BroadcastFrame :=
  ⟨team, R+1, r, G.program.length+t, link, header, dst⟩

/-- A team memory at a read of a transmission or relay bit. Only the processor input,
the routing tables, and the fields naming these allocations need to survive. -/
structure TransferBank (G : Wiring R r t d link inner n Edge) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (width : Fin (R+1) → Fin (R+1) → ℕ)
    (w header : ℕ) (team : Fin (R+1)) where
  /-- Native public arguments. -/
  pub : Arg → Word w
  /-- The team's current native memory. -/
  mem : Memory w
  /-- Scratch base for the substituted row pin. -/
  ibase : ℕ
  /-- Scratch base for the original pin. -/
  hbase : ℕ
  /-- Advice pin base. -/
  starbase : ℕ
  /-- Scratch destination of the common prefix. -/
  dst : ℕ
  /-- The inputs at their actual processor addresses. -/
  physical : (G.processorFields team pin ext ibase hbase starbase).ContainsInput mem
  /-- The populated schedule and its capacity in the allocated physical link. -/
  schedule : Schedule (G.transferFrame team header dst) width pub mem

private theorem hop_relay {N : ℕ} {h : 2 < N} {a : Fin N → Fin N → ℕ} {u v : Fin N}
    (p : Routing.Hop h a u v) :
    ∃ hd : u ≠ p.1, Routing.relay h hd p.2.val = v := by
  have hp := p.2.property
  by_cases hd : u ≠ p.1
  · simp only [Routing.pairBits, dite_eq_left hd] at hp
    exact ⟨hd, (Finset.mem_filter.mp hp).2⟩
  · simp only [Routing.pairBits, dite_eq_right hd, Finset.notMem_empty] at hp

/-- Reading the scheduled position at the logical endpoint and at the intermediate
team yields the same word of the shared physical exterior assignment. -/
theorem TransferBank.leg_read_swap {u v : Fin (R+1)}
    (A : TransferBank G pin ext width w header u) (B : TransferBank G pin ext width w header v)
    {h : 2 < R+1} (bit : Routing.Hop h width u v) :
    A.mem (routedAddress (readings A.pub) (readings A.mem) u v bit.1 (bit.2.val / (R+1-2))) =
      B.mem (routedAddress (readings B.pub) (readings B.mem) u v bit.1 (bit.2.val / (R+1-2))) := by
  obtain ⟨hd, eq⟩ := hop_relay bit
  have hvu : v ≠ u := eq ▸ (Routing.relay_ne_endpoints h hd bit.2.val).1
  have hval : v.val ≠ u.val := fun e => hvu (Fin.ext e)
  let pos := (Routing.legEquiv h width u v bit).val + header +
    (if v < u then Routing.legLoad h width v u else 0)
  have hc := A.schedule.capacity v hval
  change header + Routing.legLoad h width u v + Routing.legLoad h width v u ≤ link*r at hc
  have hp : pos < r*link := by
    have hl := (Routing.legEquiv h width u v bit).isLt
    dsimp only [pos]
    rw [Nat.mul_comm r link]
    split <;> omega
  obtain ⟨a0, a1, _, a3, a4, a5, _⟩ := A.schedule.frame
  obtain ⟨b0, b1, _, b3, b4, b5, _⟩ := B.schedule.frame
  have pa : legPosition (readings A.pub) (readings A.mem) u v bit.1 (bit.2.val/(R+1-2)) = pos :=
    (A.schedule.table.legPosition_eq bit).trans (by rw [a5]; rfl)
  have pb : legPosition (readings B.pub) (readings B.mem) u v bit.1 (bit.2.val/(R+1-2)) = pos :=
    (B.schedule.table.legPosition_eq bit).trans (by rw [b5]; rfl)
  simp only [routedAddress, a0, a1, a3, a4, b0, b1, b3, b4, pa, pb,
    Wiring.transferFrame, ite_true, ite_eq_right hval]
  exact G.read_exterior_swap u v hvu.symm pin ext A.ibase A.hbase A.starbase
    B.ibase B.hbase B.starbase A.mem B.mem A.physical B.physical ⟨pos,hp⟩

/-- A relay that passes its equality test transmits the same word to the two
logical endpoints at their separately computed local addresses. -/
theorem TransferBank.hop_read_eq {u v : Fin (R+1)} {h : 2 < R+1} (bit : Routing.Hop h width u v)
    (A : TransferBank G pin ext width w header u) (V : TransferBank G pin ext width w header v)
    (B : TransferBank G pin ext width w header bit.1)
    (checked : RelayWordAgrees (readings V.pub) (readings V.mem) u v bit.1 (bit.2.val / (R+1-2))) :
    A.mem (routedAddress (readings A.pub) (readings A.mem) u v bit.1 (bit.2.val / (R+1-2))) =
      B.mem (routedAddress (readings B.pub) (readings B.mem) bit.1 v u (bit.2.val / (R+1-2))) :=
  (A.leg_read_swap V bit).trans <| (Fin.ext checked.1).trans
    (B.leg_read_swap V (Routing.otherHop h width bit)).symm

/-- The word read by the actual endpoint register program on a descriptor bit. -/
theorem TransferBank.endpoint_eq {u z : Fin (R+1)} (hd : u ≠ z)
    (A : TransferBank G pin ext width w header u) (B : TransferBank G pin ext width w header z)
    {h : 2 < R+1} {j : ℕ} (bound : j < Routing.demand width u z)
    (V : TransferBank G pin ext width w header (Routing.relay h hd j))
    (checked : RelayWordAgrees (readings V.pub) (readings V.mem) u (Routing.relay h hd j) z (j / (R+1-2)))
    (pA pB : Reg) (sA sB : Bank w) (ha : (sA pA).val = z.val) (hb : (sB pB).val = u.val)
    (oa : (sA 15).val + (sA 16).val = j) (ob : (sB 15).val + (sB 16).val = j) :
    A.mem (endpointNat pA A.pub sA A.mem) = B.mem (endpointNat pB B.pub sB B.mem) := by
  let bit : Routing.Hop h width u (Routing.relay h hd j) :=
    ⟨z, ⟨j, by simp [Routing.pairBits, hd, bound]⟩⟩
  have eq := TransferBank.hop_read_eq bit A V B checked
  obtain ⟨a0, a1, _⟩ := A.schedule.frame
  obtain ⟨b0, b1, _⟩ := B.schedule.frame
  simp only [endpointNat_eq, a0, a1, b0, b1, Wiring.transferFrame, ha, hb, oa, ob,
    endpointRelay_eq h hd, endpointRelay_eq h hd.symm, ← Routing.relay_swap h hd j]
  exact eq

end TeamContraction

end BorderVNP
end Computability
end OAI
