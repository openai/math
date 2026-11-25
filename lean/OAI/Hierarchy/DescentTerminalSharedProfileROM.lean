import OAI.Hierarchy.DescentTerminalEpochHeader
import OAI.Hierarchy.DescentTerminalEpochOrders

namespace OAI
/-! # A single immutable profile lookup table serves every reached level -/
namespace Hierarchy.DescentTerminalEpochDecoder
open DescentSixParty DescentInitialHost DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochHeader DescentTerminalEpochFlags Computability.BorderVNP.Crossing
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section


variable {F P : Type} [Field F] {d : ℕ} {portBits : P→ℕ} {u ε : ℝ}
variable (G : PoweredGadget F) (hu : 0 ≤ u) (he : 0 ≤ ε)
variable {S Z : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop}

theorem extend_uniform {H : Histories F d P portBits} (step : SubroundInput H G (u:=u) he)
    (order : OrdersAt G he step) {root : H.Choice→Z} (b : Chart bits ok root) (h : Uniform G.C b.layout) :
    Uniform G.C (extendWith G he step order b).layout := by
  intro a mem
  change a ∈ b.layout.map (Source.map Sum.inl) ++ [_] at mem
  rcases List.mem_append.mp mem with before|last
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp before
    exact h r hr
  · exact congrArg Source.C (List.mem_singleton.mp last)

theorem schedule_uniform {H : Histories F d P portBits} {t : ℕ} (s : Schedule G (u:=u) he t H)
    (order : ScheduleOrders G he s) {root : H.Choice→Z} (b : Chart bits ok root) (h : Uniform G.C b.layout) :
    Uniform G.C (scheduledWith G he s order b).layout := by
  induction t generalizing H with
  | zero=>exact h
  | succ t ih=>exact ih s.2 order.2 (extendWith G he s.1 order.1 b) (extend_uniform G he s.1 order.1 b h)

theorem epochs_uniform {H : Histories F d P portBits} {t height C Ht J : ℕ}
    (s : Epochs G hu he (h:=height) (C:=C) (Ht:=Ht) (t:=t) J H)
    (order : EpochOrders G hu he s) {root : H.Choice→Z} (b : Chart bits ok root) (h : Uniform G.C b.layout) :
    Uniform G.C (epochsWith G hu he s order b).layout := by
  induction J generalizing H with
  | zero=>exact h
  | succ J ih =>
    exact ih s.2 order.2 (scheduledWith G he s.1.subrounds order.1 b)
      (schedule_uniform G he s.1.subrounds order.1 b h)

theorem actual_uniform {k p : ℕ} (X : Catalyst.Approximation F k p) (R s w : ℕ) (word : s < 2^w)
    {J h C Ht t : ℕ} (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J (initialGroup X R s))
    (order : EpochOrders G hu he run) : Uniform G.C (actualWith G hu he X R s w word run order).layout :=
  epochs_uniform G hu he run order (seedChart X R s w word) (by intro a ha;cases ha)

/-- Reuse the one concrete native literal-table installation across the fixed shelves. -/
theorem shared {A : Type} {C w : ℕ} (lo : ℕ) (ts : List (Source A)) (ctrl : DescentTerminalEpochHeader.Shelf A → Controls)
    (rom : Bank) (uniform : Uniform C ts) (shared : ∀p∈directory lo ts,(ctrl p).rom=rom)
    (room : rom.base+alphabet C < 2^w) (m : Memory w) :
    (install w C rom).Exec m (romMemory C rom m) (4+10*alphabet C) ∧ ProtocolRAM.CheapCode (install w C rom) ∧
      (∀a∈(directory lo ts).map (issued ctrl),HasROM a.C a.rom (romMemory C rom m)) ∧
      ∀i,i < rom.base ∨ rom.base+alphabet C ≤ i → romMemory C rom m i=m i := by
  refine ⟨(installed C rom room m).1,(installed C rom room m).2,?_,fun _ h=>rom_frame C rom m h⟩
  intro a ha
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ha
  have mem : p.source∈ts := by rw [←sources lo ts];exact List.mem_map_of_mem hp
  change HasROM p.source.C (ctrl p).rom _
  rw [uniform p.source mem,shared p hp]
  exact rom_read C rom m

end
end Hierarchy.DescentTerminalEpochDecoder

end OAI
