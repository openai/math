import OAI.Computability.BorderVNP.TransmissionSiteOperands
import OAI.Computability.BorderVNP.TransmissionJointPacket
import OAI.Computability.BorderVNP.TransmissionPinsComplete
import OAI.Computability.BorderVNP.TransmissionPinsIdentity

/-! # A contiguous physical allocation for the signed processor startup

The native input is followed by the 112 scalar frame cells, the gathered advice
(including the reference index), the copied common header, the guessed substitution
array, and the saved live pin array. Subsequent directory and geometry allocations
start at the first word beyond these regions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins

/-- Sizes of actual physical input rows and the two variable-size startup copies. -/
structure StartupArena where
  /-- Number of teams, including the distinguished team. -/
  teams : ℕ
  /-- Physical processors per team. -/
  processors : ℕ
  /-- Width of both the literal and the extra pin field. -/
  literal : ℕ
  /-- Bits per direct peer field per processor. -/
  link : ℕ
  /-- Complete broadcast width (including mode and all proposed counts). -/
  header : ℕ
  /-- Number of distributed literal bits copied to the dense advice region. -/
  copied : ℕ

namespace StartupArena

variable (A : StartupArena)

/-- Whole RAM input width per physical processor. -/
def stride : ℕ := 2*A.literal+(A.teams-1)*A.link
/-- The first writable address, immediately after all physical input words. -/
def frame : ℕ := A.processors*A.stride
/-- First bit word of the residue, extension and H* packet. -/
def dense : ℕ := A.frame+112
/-- Saved header from the exterior block reference scan. -/
def broadcastBase : ℕ := A.dense+A.copied
/-- First substituted pin bit. -/
def ibase : ℕ := A.broadcastBase+A.header
/-- Total width of one full pin field across the team. -/
def count : ℕ := A.processors*A.literal
/-- First saved live pin bit. -/
def hbase : ℕ := A.ibase+A.count
/-- First available scratch address for the demand directory and later stages. -/
def next : ℕ := A.hbase+A.count

/-- Actual scalar operands installed by the packet encoder. Unclaimed fields are
supplied by the subsequent native stages through the public-operand bank. -/
def operands {w d : ℕ} (u : Fin A.teams) (off : ℕ) (p : ReferencePacket w d) : PacketOperands :=
  ⟨⟨u.val,A.teams,A.processors,A.literal,A.link,d,A.ibase,A.hbase,A.dense+p.offset⟩,
    A.frame,A.header,A.broadcastBase,⟨off,A.copied,A.dense⟩,p.entry.length⟩

/-- The complete one-team allocation, used to bound the machine's word width. -/
theorem next_eq : A.next = A.processors*(2*A.literal+(A.teams-1)*A.link)+112+
    A.copied+A.header+2*(A.processors*A.literal) := by
  unfold next hbase ibase broadcastBase dense frame stride count; omega

/-- The wired layout and operand tuple agree whenever the arena dimensions are taken
from the very same processor. Thus the operands enter via ordinary site literal bits. -/
theorem operandsAtSite_eq {R r t d link inner n w : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (u : Fin (R+1)) (header copied off : ℕ) (p : ReferencePacket w d) :
    let arena : StartupArena := ⟨R+1,r,G.program.length+t,link,header,copied⟩
    arena.operands u off p = operandsAtSite G u arena.ibase arena.hbase (arena.dense+p.offset)
      arena.frame header arena.broadcastBase ⟨off,copied,arena.dense⟩ p := rfl

set_option maxHeartbeats 600000 in
/-- All scalar operands, both pin scans and both native advice/header copies fit
simultaneously, including the extension decoder's sentinel. Only the physical counts,
the source slot, and the ceiling of the single contiguous allocation enter the proof. -/
theorem fits {w d : ℕ} (u : Fin A.teams) (off : ℕ) (p : ReferencePacket w d)
    (three : 2 < A.teams) (procs : 0 < A.processors) (lit : 0 < A.literal) (link : 0 < A.link)
    (hdr : 0 < A.header) (block : A.header ≤ A.link*A.processors) (slot : off < A.literal)
    (packet : p.bits.length ≤ A.copied) (copies : A.copied ≤ A.processors) (ceiling : A.next < 2^w) :
    let B := A.operands u off p
    B.Fits w ∧ B.broadcast.Fits w B.frameBase ∧ B.advice.Fits B.broadcast w B.frameBase ∧
      ExtendedFrame.Fits w B.frameBase B.advice.dst B.entryWords ∧
      LoopFits w B.layout ∧ IdentityFits B.layout w ∧ B.layout.width ≤ B.layout.count := by
  intro B
  have hp : p.offset+d ≤ A.copied := p.bits_length ▸ packet
  have stack : A.frame+112+A.copied+A.header+2*A.count = A.next := by
    dsimp only [next,hbase,ibase,broadcastBase,dense]; omega
  have pos : 0 < w := by
    by_contra! hz
    have eq : w=0 := by omega
    rw [eq,pow_zero] at ceiling
    omega
  have entries : p.entry.length ≤ p.offset := (Nat.le_add_right p.entry.length 81).trans
    (Nat.le_mul_of_pos_left _ pos)
  have lstride : B.layout.stride = A.stride := by
    change A.literal+(A.teams-1)*A.link+A.literal = 2*A.literal+(A.teams-1)*A.link
    omega
  have input := Nat.le_mul_of_pos_left A.stride procs
  change A.stride ≤ A.frame at input
  have slit : A.literal ≤ A.stride := by dsimp [stride]; omega
  have teamlt : A.teams ≤ A.stride := by
    have m := Nat.le_mul_of_pos_right (A.teams-1) link
    dsimp [stride]; omega
  have linklt : A.link ≤ A.stride := by
    have h := Nat.le_mul_of_pos_left A.link (by omega : 0 < A.teams-1)
    dsimp [stride]; omega
  have procnt : A.processors ≤ A.count := Nat.le_mul_of_pos_right _ lit
  have dw : d ≤ A.count := by omega
  have slarge : A.frame+112+A.copied+A.header+2*A.count < 2^w := stack ▸ ceiling
  have ib : A.ibase = A.frame+112+A.copied+A.header := rfl
  have hb : A.hbase = A.frame+112+A.copied+A.header+A.count := rfl
  have strideFit : B.layout.processors*B.layout.stride = A.frame := by rw [lstride]; rfl
  refine ⟨?_,?_,?_,?_,?_,?_,dw⟩
  · intro x hx
    change x ∈ [A.frame,u.val,A.teams,A.processors,A.literal,A.link,A.header,A.ibase,A.hbase,d,
      A.dense+p.offset,A.broadcastBase,off,A.copied,A.dense,p.entry.length,w] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    have own := u.isLt
    have hw : w < 2^w := Nat.lt_two_pow_self
    rcases hx with eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq <;> subst x <;>
      first | omega | (dsimp only [dense,broadcastBase]; omega)
  · exact ⟨three,u.isLt,procs,link,hdr,block,le_rfl,by change A.frame+31 ≤ A.frame+112+A.copied; omega,
      by change A.frame+112+A.copied+A.header < 2^w; omega⟩
  · refine ⟨slot,copies,by change A.frame+112+A.copied ≤ 2^w; omega,?_,?_⟩
    · intro x hx
      change x < A.frame at hx
      change ¬ (A.frame+112 ≤ x ∧ _); omega
    · intro j hj
      change ¬ (A.frame+112 ≤ A.frame+j ∧ _); omega
  · refine ⟨by change A.frame+112 < 2^w; omega,le_rfl,?_⟩
    change A.frame+112+p.entry.length*w+81*w < 2^w
    have e : p.entry.length*w+81*w = p.offset := by unfold ReferencePacket.offset; ring
    omega
  · refine ⟨lit, fun x hx => (livePinAddress_lt B.layout hx).trans_le ?_, ?_, ?_⟩
    · rw [strideFit]; omega
    · intro x hx
      change x < A.count at hx
      change A.ibase+x < 2^w
      omega
    · intro x hx _
      change x < A.count at hx
      change A.hbase+x < 2^w
      omega
  · refine ⟨lit,?_,?_⟩
    · intro i hi
      exact (livePinAddress_lt B.layout (show i < B.layout.count from hi.trans_le dw)).trans_le (by rw [strideFit]; omega)
    · intro i hi
      change i < d at hi
      change A.frame+112+p.offset+i < 2^w
      omega

end StartupArena
end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
