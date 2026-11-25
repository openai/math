import OAI.Hierarchy.DescentIssuedDonorPayload
import OAI.Hierarchy.DescentPrivateHeaderCheap
import OAI.Hierarchy.DescentPackedDonorHardware

namespace OAI
/-! # A physical private-bit register advances at an actual issued ordinary date -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentHostDegree DescentPackedPrivateSum DescentRawCablePanel DescentSIMDLookup
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)

/-- Scratch for one date, with the real predecessor host ordering padded only at its end. -/
structure MeterPort (source : Reached W G q ε S k i z D wire hist) where
  hosts : ℕ
  enough : Fintype.card source.V≤hosts
  base : ℕ
  payload : ℕ
  groupsPerWord : ℕ

namespace MeterPort
variable (b : MeterPort source) (a : ℕ)
def vertex := source.vertex.trans (Fin.castLEEmb b.enough)

local notation "A" => source.placement
local notation "units" => normBits (A).cap G.b G.C G.k
local notation "J" => S.groupCount i*2^k*(A).cap
local notation "names" => donorNameBits T.k T.Δ
local notation "inputBits" => bundleBits 3 names units
local notation "short" => 2+units
local notation "full" => max inputBits (short*11)
local notation "M" => b.groupsPerWord*(2^k*(A).cap)
local notation "law" => donorROM T.k (gainExponent 20 T.Δ) (2^(packExponent 20 T.Δ)+2) 3 names units
local notation "bank" => DescentPackedDonorSpace.banks b.base b.hosts J M inputBits
local notation "L₀" => DescentPackedDonorSpace.layout b.base b.hosts J M inputBits short
local notation "C₀" => DescentPackedDonorSpace.counters a b.base b.hosts J M inputBits short

def endAddr :=
  let _ := ticket
  DescentPackedDonorSpace.endAt b.base b.hosts J M inputBits short

def program (bw : ℕ) : Procedure bw :=
  let _ := ticket
  ((DescentPackedDonorTables.program bank (L₀).rom.base b.hosts J M bw law score).seq
    ((DescentSIMDLookup.program bank (L₀).source.base b.hosts J M bw).seq
      (DescentPackedPrivateAccumulator.program L₀ C₀ bw b.hosts (J*11) (M*11) T.z))).seq
    (DescentPrivateHeader.commit bw a (C₀).out)

def ticks :=
  let _ := ticket
  ((4+10*DescentPackedDonorTables.size bank (L₀).rom.base short M)+
    ((4+44*(b.hosts*chunks J M))+(Layout.billed b.hosts (J*11) (M*11)+(C₀).scaling.steps T.z)))+11

def image (m : Memory bw) : Memory bw :=
  let _ := ticket
  let pre:=DescentPackedDonorTables.image bank (L₀).rom.base b.hosts J M law score m
  let mid:=ProtocolRAM.image (L₀).source.base (b.hosts*chunks J M) (lookup bank) pre
  let out:=DescentPackedPrivateAccumulator.image L₀ C₀ b.hosts (J*11) (M*11) T.z mid
  DescentPrivateHeader.committed a (C₀).out out

def Pins (m : Memory bw) : Prop :=
  ∀p : Row b.hosts J M,m ((bank).source.base+(row b.hosts J M p).val)=
    (data («M»:=M) (fun v j=>packDonor (ticket.measuredDonors b.vertex v j)) p).val

structure Fits (bw K : ℕ) : Prop where
  before : a≤b.base
  positive : 0<b.groupsPerWord
  packed : M*full≤b.payload/2
  word : b.payload≤bw
  overhead : bw≤K*b.payload
  room : endAddr ticket b<2^bw

def price (bw K : ℕ) :=
  let _ := ticket
  K*((131+4*ProtocolRAMPortScale.bitWidth T.z+
  124*(b.hosts*chunks (S.groupCount i) b.groupsPerWord)+20*2^(b.payload/2))*b.payload)+11*bw

def hardware :=
  let _ := ticket
  15*(DescentPackedDonorTables.size bank (L₀).rom.base short M+1)+308+
  8*ProtocolRAMPortScale.bitWidth T.z

theorem names_le (bw : ℕ) : DescentStaticWordColumn.names (program ticket b a bw)≤hardware ticket b := by
  have bound:=DescentPackedDonorTables.full_hardware bank L₀ C₀ b.hosts J M bw T.z law score
  rw [program,DescentStaticWordColumn.names_seq]
  change _+18≤_
  dsimp only [hardware]
  omega

theorem cheap (bw : ℕ) : ProtocolRAM.CheapCode (program ticket b a bw) :=
  @ProtocolRAM.cheap_seq bw
    ((DescentPackedDonorTables.program bank (L₀).rom.base b.hosts J M bw law score).seq
      ((DescentSIMDLookup.program bank (L₀).source.base b.hosts J M bw).seq
        (DescentPackedPrivateAccumulator.program L₀ C₀ bw b.hosts (J*11) (M*11) T.z)))
    (DescentPrivateHeader.commit bw a (C₀).out)
    (@DescentPackedDonorTables.stage_cheap bank L₀ C₀ b.hosts J M bw T.z inputBits short law score)
    (@DescentPrivateHeader.commit_cheap bw a (C₀).out)

/-- The exact time depends only on the packed dimensions, for all native inputs. -/
theorem ticks_price {K : ℕ} (fit : Fits ticket b a bw K) :
    ticks ticket b a*bw≤price ticket b bw K := by
  have roles : 0<2^k*(A).cap:=Nat.mul_pos (Nat.two_pow_pos _) (A).capPos
  have live:=Nat.mul_pos fit.positive roles
  have clock:=DescentPackedDonorTables.grouped_price b.base b.payload b.hosts J inputBits short T.z M C₀ live fit.packed
  have wordCount : chunks J M=chunks (S.groupCount i) b.groupsPerWord := by
    rw [Nat.mul_assoc]
    exact chunks_group _ _ _ fit.positive roles
  unfold ticks price
  rw [Nat.add_mul]
  apply Nat.add_le_add_right
  calc
    _ ≤ (131+4*ProtocolRAMPortScale.bitWidth T.z+124*(b.hosts*chunks J M)+20*2^(b.payload/2))*(K*b.payload) :=
      Nat.mul_le_mul clock fit.overhead
    _ = _ := by rw [wordCount];ring

/-- Both ends of this program read the same physical header. Its only other writes
lie inside this date's single scratch interval. -/
theorem advance (path : Path start source) (K : ℕ) (m : Memory bw)
    (fit : Fits ticket b a bw K) (pins : Pins ticket b m) (held : path.Held a m) :
    (program ticket b a bw).Exec m (image ticket b a m) (ticks ticket b a) ∧
    (path.ordinary ticket).Held a (image ticket b a m) ∧
    (ticks ticket b a)*bw≤price ticket b bw K ∧
    ∀addr,addr≠a → (addr≤b.base ∨ endAddr ticket b≤addr) → image ticket b a m addr=m addr := by
  have roles : 0<2^k*(A).cap:=Nat.mul_pos (Nat.two_pow_pos _) (A).capPos
  have live:=Nat.mul_pos fit.positive roles
  obtain ⟨run,next,clock,_,frame⟩:=Path.Held.measured_donor_grouped path ticket b.vertex
    a b.base b.payload M m held fit.before live fit.packed fit.word fit.room pins
  have wordCount : chunks J M=chunks (S.groupCount i) b.groupsPerWord := by
    rw [Nat.mul_assoc]
    exact chunks_group _ _ _ fit.positive roles
  have ordered : a≤(C₀).out := by
    apply fit.before.trans
    simp only [DescentPackedDonorSpace.counters,DescentPackedPrivateSpace.counters,
      DescentPackedDonorSpace.consumerBase,DescentPackedDonorSpace.banks,DescentPackedPrivateSpace.layout,
      DescentPackedPrivateSpace.rom,DescentPackedPrivateSpace.source]
    omega
  have room : (C₀).out+1<2^bw := fit.room
  refine ⟨?_,next.keep (DescentPrivateHeader.committed_read a (C₀).out _),?_,?_⟩
  · intro P₀ R K₀ mach pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then run (DescentPrivateHeader.commit_run a (C₀).out _ ordered room)
      mach pc reg pub exit rom advice cfg raw enter same
  · unfold ticks price
    rw [Nat.add_mul]
    apply Nat.add_le_add_right
    calc
      _ ≤ (131+4*ProtocolRAMPortScale.bitWidth T.z+
          124*(b.hosts*chunks J M)+20*2^(b.payload/2))*(K*b.payload) :=
        Nat.mul_le_mul clock fit.overhead
      _ = _ := by rw [wordCount];ring
  · intro addr apart away
    exact (DescentPrivateHeader.committed_frame a (C₀).out _ addr apart).trans (frame addr away)

end MeterPort
end
end Hierarchy.DescentSixParty.Chronology

end OAI
