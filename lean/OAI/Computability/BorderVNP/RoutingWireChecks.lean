import OAI.Computability.BorderVNP.RoutingWireBroadcast
import OAI.Computability.BorderVNP.RoutingWirePadding
import OAI.Computability.BorderVNP.RoutingWireRelay

/-! # Reading the complete routing condition in the actual team memories

The fixed header is read at one block. A source reads the payload at its
oriented leg, the intermediate team reads both addressed copies, and the
remaining slots are checked at the physical padding positions. These five
families of memory conditions have exactly one shared exterior assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
  {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}

/-- The source end of the directed leg reads its own initialized RAM word at the
actual frame and table address. -/
theorem TransferBank.read_source_hop (hw : 0 < w) {u v : Fin (R+1)}
    (A : TransferBank G pin ext L.width w L.header u) (p : Hop L.three L.width u v) :
    readings A.mem (routedAddress (readings A.pub) (readings A.mem) u v p.1 (p.2.val/((R+1)-2))) =
      ((L.exteriorEquiv ext).hop u v p).toNat := by
  obtain ⟨f0,f1,_,f3,f4,f5,_⟩ := A.schedule.frame
  simp only [routedAddress,f0,f1,f3,f4,Wiring.transferFrame,ite_true]
  exact G.read_message_leg L u v (hop_ne_relay p) pin ext A.ibase A.hbase A.starbase A.mem
    A.physical hw p rfl (readings A.pub) A.schedule.table f5

/-- The successive native snapshots, each preserving its own processor input and
scheduling table. Every used leg may be read at a different instant. -/
structure WireSnapshots (G : Wiring R r t d link inner n Edge) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (L : WireLayout (R+1) r link) (w : ℕ) where
  /-- Input to the header check at each team. -/
  header : ∀ u, TransferBank G pin ext L.width w L.header u
  /-- Memory from which the source bit is read. -/
  source : ∀ u v, Hop L.three L.width u v → TransferBank G pin ext L.width w L.header u
  /-- Memory used in each comparison of two routed positions. -/
  relay : ∀ u v, Hop L.three L.width u v → TransferBank G pin ext L.width w L.header v
  /-- Memory at the beginning of a complete suffix scan. -/
  padding : ∀ u, TransferBank G pin ext L.width w L.header u

/-- Validity of all five physical predicates at their own snapshots. -/
def WireSnapshots.Passes (S : WireSnapshots G pin ext L w)
    (b : Block (R+1)) (header : Fin L.header → Bool) (high payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) : Prop :=
  (∀ u, (G.transferFrame u L.header (S.header u).dst).Agrees (readings (S.header u).mem)) ∧
  (∀ i : Fin L.header, readings (S.header b.val.1).mem
    (physicalBitAddress b.val.1 (R+1) (G.program.length+t) link b.val.2 i) = (header i).toNat) ∧
  (∀ (u v : Fin (R+1)) (p : Hop L.three L.width u v), u = sourceTeam high u p.1 p.2.val →
    let A := S.source u v p
    readings A.mem (routedAddress (readings A.pub) (readings A.mem) u v p.1 (p.2.val/((R+1)-2))) =
      (payload (min u p.1) (max u p.1) p.2.val).toNat) ∧
  (∀ (u v : Fin (R+1)) (p : Hop L.three L.width u v),
    let A := S.relay u v p
    RelayWordAgrees (readings A.pub) (readings A.mem) u v p.1 (p.2.val/((R+1)-2))) ∧
  (∀ u v : Fin (R+1), u ≠ v →
    let A := S.padding u
    let f := G.transferFrame u L.header A.dst
    f.ZeroFrom (readings A.mem) (f.usedPrefix A.schedule.fit L.width v) v)

/-- Different native scratch states give the same five predicates on the one
shared exterior assignment. -/
theorem WireSnapshots.passes_iff (hw : 0 < w) (S : WireSnapshots G pin ext L w)
    (fixed : Block (R+1)) (header : Fin L.header → Bool) (high payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) :
    S.Passes fixed header high payload ↔ Checks L.three L.width fixed header high payload (L.exteriorEquiv ext) := by
  have inj : Function.Injective Bool.toNat := by decide
  have hf : blockOf fixed.val.1 fixed.val.2 fixed.property.ne = fixed := by
    obtain ⟨⟨u,v⟩,h⟩ := fixed
    simp [blockOf,h]
  let B := S.header fixed.val.1
  have hheader (i : Fin L.header) := G.read_message_header L fixed.val.1 fixed.val.2 fixed.property.ne
    pin ext B.ibase B.hbase B.starbase B.mem B.physical hw i
  simp only [hf] at hheader
  rw [WireSnapshots.Passes, Checks, transfer_broadcasts_iff hw S.header, transfer_padding_iff hw S.padding]
  constructor
  · rintro ⟨broadcast,atFixed,atSource,relays,padding⟩
    exact ⟨broadcast,funext fun i => inj ((hheader i).symm.trans (atFixed i)),
      fun u v p hs => inj (((S.source u v p).read_source_hop hw p).symm.trans (atSource u v p hs)),
      fun u v p => ((S.relay u v p).relay_hop_iff hw p).mp (relays u v p),padding⟩
  · rintro ⟨broadcast,atFixed,atSource,relays,padding⟩
    exact ⟨broadcast,fun i => (hheader i).trans (congrArg Bool.toNat (congrFun atFixed i)),
      fun u v p hs => ((S.source u v p).read_source_hop hw p).trans (congrArg Bool.toNat (atSource u v p hs)),
      fun u v p => ((S.relay u v p).relay_hop_iff hw p).mpr (relays u v p),padding⟩

/-- A single team-bank snapshot for all the physical checks. -/
def WireSnapshots.common (A : ∀ u, TransferBank G pin ext L.width w L.header u) : WireSnapshots G pin ext L w :=
  ⟨A,fun u _ _ => A u,fun _ v _ => A v,A⟩

/-- Validity of the physical tests when each team uses one common bank snapshot. -/
abbrev PhysicalWireChecks (A : ∀ u, TransferBank G pin ext L.width w L.header u)
    (fixed : Block (R+1)) (header : Fin L.header → Bool) (high payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) : Prop :=
  (WireSnapshots.common A).Passes fixed header high payload

/-- At a common bank snapshot the physical RAM checks are equivalent to the
abstract message predicates. -/
theorem physicalWireChecks_iff (hw : 0 < w) (A : ∀ u, TransferBank G pin ext L.width w L.header u)
    (fixed : Block (R+1)) (header : Fin L.header → Bool) (high payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) :
    PhysicalWireChecks A fixed header high payload ↔
      Checks L.three L.width fixed header high payload (L.exteriorEquiv ext) :=
  (WireSnapshots.common A).passes_iff hw fixed header high payload

/-- Even when the initialized banks and scratch states depend on the proposed physical
bits, exactly one exterior assignment passes all word-RAM checks for a fixed term. -/
theorem existsUnique_physicalWireChecks (hw : 0 < w)
    (A : ∀ (ext : Exterior R r link → Bool) u, TransferBank G pin ext L.width w L.header u)
    (fixed : Block (R+1)) (header : Fin L.header → Bool) (high payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) :
    ∃! ext, PhysicalWireChecks (A ext) fixed header high payload := by
  obtain ⟨e,pass,unique⟩ := L.existsUnique_exterior fixed header high payload
  refine ⟨e,(physicalWireChecks_iff hw _ ..).mpr pass,fun ext h => ?_⟩
  exact unique ext ((physicalWireChecks_iff hw _ ..).mp h)

end TeamContraction

end BorderVNP
end Computability
end OAI
