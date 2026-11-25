import OAI.Hierarchy.DescentPackedDonorCheap
import OAI.Hierarchy.DescentPrivatePanelFrame
import OAI.Hierarchy.DescentPrivateHeaderCheap

namespace OAI
/-! # Two-sided memory frame and unconditional execution of the packed counter instructions -/
namespace Hierarchy.DescentPackedCounter
open DescentPackedPrivateSum DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Counter where
  hosts : ℕ
  rows : ℕ
  lanes : ℕ
  inputBits : ℕ
  scoreBits : ℕ
  quantum : ℕ
  base : ℕ
  header : ℕ

namespace Counter
variable (b : Counter) {bw : ℕ}
local notation "J" => b.rows
local notation "M" => b.lanes
local notation "inputBits" => b.inputBits
local notation "short" => b.scoreBits
local notation "full" => max inputBits (short*11)
local notation "bank" => DescentPackedDonorSpace.banks b.base b.hosts J M inputBits
local notation "L₀" => DescentPackedDonorSpace.layout b.base b.hosts J M inputBits short
local notation "C₀" => DescentPackedDonorSpace.counters b.header b.base b.hosts J M inputBits short
variable (law : Cell (Counter.inputBits b) → Cell ((Counter.scoreBits b)*11)) (score : Cell (Counter.scoreBits b) → ℕ)
def program (w : ℕ) : Procedure w :=
  ((DescentPackedDonorTables.program bank (L₀).rom.base b.hosts J M w law score).seq
    ((DescentSIMDLookup.program bank (L₀).source.base b.hosts J M w).seq
      (DescentPackedPrivateAccumulator.program L₀ C₀ w b.hosts (J*11) (M*11) b.quantum))).seq
    (DescentPrivateHeader.commit w b.header (C₀).out)

def ticks := ((4+10*DescentPackedDonorTables.size bank (L₀).rom.base short M)+
  ((4+44*(b.hosts*chunks J M))+(Layout.billed b.hosts (J*11) (M*11)+(C₀).scaling.steps b.quantum)))+11

def endAddr := DescentPackedDonorSpace.endAt b.base b.hosts J M inputBits short

def image (m : Memory bw) : Memory bw :=
  let pre:=DescentPackedDonorTables.image bank (L₀).rom.base b.hosts J M law score m
  let mid:=ProtocolRAM.image (L₀).source.base (b.hosts*chunks J M) (lookup bank) pre
  let out:=DescentPackedPrivateAccumulator.image L₀ C₀ b.hosts (J*11) (M*11) b.quantum mid
  DescentPrivateHeader.committed b.header (C₀).out out

structure Room (bw : ℕ) : Prop where
  before : b.header≤b.base
  positive : 0<M
  packed : M*full≤bw/2
  room : b.endAddr<2^bw

/-- All loops and lookups follow allocated numeric bounds for every input word. -/
theorem counter_any (m : Memory bw) (fit : b.Room bw) :
    (b.program law score bw).Exec m (b.image law score m) (b.ticks) := by
  let pre:=DescentPackedDonorTables.image bank (L₀).rom.base b.hosts J M law score m
  let mid:=ProtocolRAM.image (L₀).source.base (b.hosts*chunks J M) (lookup bank) pre
  let out:=DescentPackedPrivateAccumulator.image L₀ C₀ b.hosts (J*11) (M*11) b.quantum mid
  have live:0<M:=fit.positive
  have room:=DescentPackedDonorSpace.room fit.before live (fit.packed) fit.room
  have archive:=DescentPackedDonorTables.arena fit.room
  have below:(bank).mask.base≤(L₀).rom.base+2^(short*(M*11)) := by
    exact (Nat.le_add_right ..).trans (archive.masks.trans ((Nat.le_add_right ..).trans
      (archive.dictionary.trans (Nat.le_add_right ..))))
  have space : (bank).mask.base+DescentPackedDonorTables.size bank (L₀).rom.base short M<2^bw := by
    unfold DescentPackedDonorTables.size
    have bound:=archive.endFit
    omega
  have mounted:=@DescentStaticWordColumn.mount bw (bank).mask.base (DescentPackedDonorTables.size bank (L₀).rom.base short M)
    (DescentPackedDonorTables.literal bank (L₀).rom.base b.hosts J M law score) m space
  have lookupFits : (lookup bank).Fits bw (L₀).source.base := by
    simp [lookup,ProtocolRAM.Expr.Fits,room.resolver.dictionary,room.resolver.source,room.resolver.mask]
  have scan:=@ProtocolRAM.scan_exec bw (L₀).source.base (b.hosts*chunks J M) (lookup bank) pre lookupFits room.resolver.output
  have next : (DescentPackedPrivateAccumulator.program L₀ C₀ bw b.hosts (J*11) (M*11) b.quantum).Exec mid out
      (Layout.billed b.hosts (J*11) (M*11)+(C₀).scaling.steps b.quantum) :=
    DescentPackedPrivateAccumulator.run L₀ C₀ b.quantum mid room.reduce room.scale
  have final:=@DescentPrivateHeader.commit_run bw b.header (C₀).out out
    (show b.header≤(C₀).out from (room.scale.volume.trans room.scale.temp).le) (show (C₀).out+1<2^bw from fit.room)
  have lookupTime : 4+(b.hosts*chunks J M)*(2*(lookup bank).work+4)=4+44*(b.hosts*chunks J M) := by rw [lookup_work];ring
  rw [lookupTime] at scan
  intro P₀ R K₀ mach pc reg pub exit rom advice cfg raw enter same
  exact Procedure.Exec.then (Procedure.Exec.then mounted (Procedure.Exec.then scan next)) final
    mach pc reg pub exit rom advice cfg raw enter same

theorem counter_frame (m : Memory bw) (fit : b.Room bw) (addr : ℕ)
    (apart : addr≠b.header) (away : addr≤b.base ∨ b.endAddr≤addr) : b.image law score m addr=m addr := by
  let pre:=DescentPackedDonorTables.image bank (L₀).rom.base b.hosts J M law score m
  let mid:=ProtocolRAM.image (L₀).source.base (b.hosts*chunks J M) (lookup bank) pre
  have live : 0<M:=fit.positive
  have cpu:=fit.packed
  have space:=DescentPackedDonorSpace.room fit.before live cpu fit.room
  have atBase:=DescentPackedDonorSpace.room (prior:=b.base) le_rfl live cpu fit.room
  have lastWord : (C₀).out+1=b.endAddr:=rfl
  have sourceEnd : (L₀).source.base+b.hosts*chunks J M≤(L₀).rom.base:=space.score
  have tableEnd : (L₀).rom.base+2^(short*(M*11))≤(L₀).words:=by
    simpa only [ProtocolRAM.Bank.size,space.bits] using space.reduce.rom.2.2
  have ord:=space.reduce.sep
  have count:=space.last
  have active : (C₀).words<(C₀).scaled:=space.scale.active
  have temp : (C₀).scaled<(C₀).out:=space.scale.temp
  have start : b.base<(bank).mask.base :=by change b.base<b.base+1+_;omega
  have inputStart:=atBase.before
  have upper : (L₀).words≤(L₀).starts := (Nat.le_add_right ..).trans ord
  have packedEnd : (L₀).rom.base≤(C₀).out :=by
    calc
      _ ≤ (L₀).rom.base+2^(short*(M*11)) :=Nat.le_add_right ..
      _ ≤ (L₀).words :=tableEnd
      _ ≤ (L₀).starts :=upper
      _ ≤ (C₀).words :=by rw [count]; exact Nat.le_add_right ..
      _ ≤ (C₀).out :=(active.trans temp).le
  have wordsStart:=atBase.earlier
  have arena:=DescentPackedDonorTables.arena fit.room
  have masks:=arena.masks
  have dictionary:=arena.dictionary
  apply (DescentPrivateHeader.committed_frame b.header (C₀).out _ addr apart).trans
  apply (DescentPackedPrivateAccumulator.image_frame L₀ C₀ b.quantum mid space.reduce space.scale space.last addr
    (away.elim (fun lo=>.inl (lo.trans_lt wordsStart)) (fun hi=>.inr (by omega)))).trans
  apply (ProtocolRAMGeneratedWrite.frame_image (L₀).source.base (b.hosts*chunks J M) (lookup bank) pre addr
    (away.elim (fun lo=>.inl (lo.trans_lt inputStart)) (fun hi=>.inr (sourceEnd.trans (packedEnd.trans (by omega)))))).trans
  apply DescentStaticWordColumn.frame
  rcases away with lo|hi
  · exact .inl (lo.trans_lt start)
  · right
    unfold DescentPackedDonorTables.size
    have sorted : (bank).mask.base≤(L₀).rom.base+2^(short*(M*11)) :=
      (Nat.le_add_right ..).trans (masks.trans ((Nat.le_add_right ..).trans (dictionary.trans (Nat.le_add_right ..))))
    rw [Nat.add_sub_of_le sorted]
    have wordsBound : (L₀).words≤(C₀).out := by
      calc
        _ ≤ (L₀).starts :=upper
        _ ≤ (C₀).words :=by rw [count];exact Nat.le_add_right ..
        _ ≤ _ :=(active.trans temp).le
    exact tableEnd.trans (wordsBound.trans (by omega))

set_option maxHeartbeats 900000 in
theorem counter_cheap (bw : ℕ) : ProtocolRAM.CheapCode (b.program law score bw) :=
  @ProtocolRAM.cheap_seq bw _ (DescentPrivateHeader.commit bw b.header (C₀).out) (@DescentPackedDonorTables.stage_cheap bank L₀ C₀ b.hosts J M bw b.quantum inputBits short law score)
    (@DescentPrivateHeader.commit_cheap bw b.header (C₀).out)

end Counter
end
end Hierarchy.DescentPackedCounter

end OAI
