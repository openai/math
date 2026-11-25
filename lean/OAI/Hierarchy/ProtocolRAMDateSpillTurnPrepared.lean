import OAI.Hierarchy.ProtocolRAMDateSpillTurnPage
import OAI.Hierarchy.ProtocolRAMDateSpillPublish

namespace OAI
/-! # The two offset scans and relocated public shelf on the actual tape -/
noncomputable section
open scoped Fin.CommRing
namespace Hierarchy.ProtocolRAM.DateSpill.TurnPage
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMTurnChart ProtocolRAMTurnItinerary Calendar
open scoped Classical

variable {W roles : ℕ} (P : TurnPage roles)
local notation "T" => P.terminal
local notation "L" => P.window

def offsetState (m : Memory W) := P.offsets.result P.left P.right m
def prepared (m : Memory W) := result P.romPasses (P.offsetState m)

theorem prepare (m : Memory W) (old : P.left.prefix.Fits W P.first) (new : P.right.prefix.Fits W P.first)
    (directory : ∀f (i : ℕ),i<2^(T).romBits→(ProtocolRAMTurnDirectory.bank (T).rom (T).romBits f).read m (i:Word W)=
      ProtocolRAMTurnDirectory.words (T).turns (T).sites (T).seats (T).base f i)
    (low : (T).rom+4*2^(T).romBits≤P.first) (moved : (T).base≤P.base)
    (bits : (T).romBits=(L).romBits) (room : P.stop≤2^W) :
    (((P.offsets.program W P.left P.right).seq (ProtocolRAM.program W P.romPasses)).Exec m (P.prepared m)
      (P.offsets.time P.left P.right+clock P.romPasses)) ∧
    (∀f (i : ℕ),i<2^(T).romBits→(ProtocolRAMTurnDirectory.bank P.directory (T).romBits f).read (P.prepared m) (i:Word W)=
      ProtocolRAMTurnDirectory.words (T).turns (T).sites (T).seats P.base f i) ∧
    (∀i:Fin P.ranks.old,P.added.old.read (P.prepared m) (i.val:Word W)=P.left.prefix.eval m (i.val:Word W)) ∧
    (∀i:Fin P.ranks.edges,P.added.new.read (P.prepared m) (i.val:Word W)=P.right.prefix.eval m (i.val:Word W)) ∧
    ∀a,a<P.first ∨ (L).floor≤a→P.prepared m a=m a := by
  have b:=(L).bounds
  have before : P.first≤P.directory := by
    change P.first≤P.first+_+_;omega
  have floor : (L).floor=P.directory+4*2^(T).romBits:=rfl
  change (L).stop≤2^W at room
  have space : (L).floor<2^W := by omega
  have cap : (T).turns*5≤2^(T).romBits := bits ▸ (L).rom_capacity.1
  have small : 2^(T).romBits<2^W := by omega
  have input (f : Fin 4) (i : ℕ) (hi : i<2^(T).romBits) :
      (ProtocolRAMTurnDirectory.bank (T).rom (T).romBits f).read (P.offsetState m) (i:Word W)=
        ProtocolRAMTurnDirectory.words (T).turns (T).sites (T).seats (T).base f i := by
    apply Eq.trans _ (directory f i hi)
    apply DatedSpillOffsets.Layout.frame
    left
    have mul:=Nat.mul_le_mul_right (2^(T).romBits) (show f.val+1≤4 from f.isLt)
    rw [Nat.succ_mul] at mul
    change (T).rom+f.val*2^(T).romBits+(i:Word W).val%(2^(T).romBits)<P.first
    omega
  obtain ⟨built,read,frame⟩:=Relocate.run (T).rom P.directory (T).romBits (T).turns (T).sites (T).seats
    (T).base P.base (P.offsetState m) input (low.trans before) moved (cap.trans_lt small) space
  have directoryRoom : P.directory < 2^W := by omega
  have offsetRun : (P.offsets.program W P.left P.right).Exec m (P.offsetState m)
      (P.offsets.time P.left P.right) :=
    P.offsets.exec P.left P.right m old new directoryRoom
  have loFit : P.added.old.base+P.added.old.size≤P.directory :=
    Nat.le_add_right (P.first + P.offsets.oldOffset.size) P.offsets.newOffset.size
  have hiFit : P.added.new.base+P.added.new.size=P.directory := rfl
  have keep (c : Bank) (limit : c.base+c.size≤P.directory) (r : Word W) :
      c.read (P.prepared m) r=c.read (P.offsetState m) r :=
    frame _ (.inl ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le limit))
  refine ⟨?_,read,?_,?_,?_⟩
  · intro procs regs keys mach pc reg pub exit installed data cfg raw entry eq
    exact Procedure.Exec.then offsetRun built mach pc reg pub exit installed data cfg raw entry eq
  · intro i
    exact (keep _ loFit _).trans (P.offsets.old_read P.left P.right m i directoryRoom)
  · intro i
    exact (keep _ hiFit.le _).trans (P.offsets.new_read P.left P.right m i new directoryRoom)
  · intro a h
    apply (frame a (by rcases h with h|h;exact .inl (h.trans_le before);exact .inr h)).trans
    apply DatedSpillOffsets.Layout.frame
    rcases h with h|h
    · exact .inl h
    · right;change P.directory≤a;omega

end Hierarchy.ProtocolRAM.DateSpill.TurnPage

end
end OAI
