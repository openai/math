import OAI.Computability.BorderVNP.PackedHistoryPreparedInput
import OAI.Computability.BorderVNP.FiniteWideBoot
import OAI.Computability.BorderVNP.GeometryAdviceAllocation
import OAI.Computability.BorderVNP.TransmissionJointReads
import OAI.Computability.BorderVNP.TransmissionStartupArena
import OAI.Computability.BorderVNP.GeometryAdviceRate

/-! # Contiguous wide startup allocation for the finite-field history reader

The finite bootstrap copies the entire serialized preamble and its 81 extension words.
One processor can hold multiple copied bits. The pin banks follow the copied exterior
header and the guarded history interpreter starts above both banks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.ProfileArena

open VPVNP BurstRAM TeamContraction ProcessorSlots Routing RoutingISA RoutingISA.Pins
open GeometryAdvice PackedHistoryCircuit

variable {R r t d link inner n W : ℕ} {Edge : Type}
variable (G : Wiring R r t d link inner n Edge) (L : WireLayout (R+1) r link)

/-- Physical layout of the input, scalar frame, wide dense copy, common header and pin banks. -/
def arena (pre : List (Word W)) : StartupArena :=
  ⟨R+1,r,G.program.length+t,link,L.header,(pre.length+81)*W⟩

/-- Bootstrap stripe descriptor pointing into the dense copy immediately after the frame. -/
def advice (A : StartupArena) (start : ℕ) : AdviceLayout := ⟨start,A.copied,A.dense⟩

variable (pre : List (Word W)) (ext : Fin 81 → Word W) (ref : Fin d → Bool)
local notation "A" => arena G L pre
local notation "lit" => G.program.length+t

/-- The exact scalar tuple read by the finite field program. The finite reference base
is the start of the preamble. -/
def operands (start : ℕ) (u : Fin (R+1)) : PacketOperands :=
  operandsAtSite G u (A).ibase (A).hbase (A).dense (A).frame L.header (A).broadcastBase
    (advice A start) (⟨pre,ext,ref⟩ : ReferencePacket W d)

/-- Static checks for the physical boot, copied profile, and pin sweep. -/
structure Placed (B : PacketOperands) (reserve stop : ℕ) : Prop where
  scalar : B.Fits W
  broadcast : B.broadcast.Fits W B.frameBase
  count : B.advice.count = (pre.length+81)*W
  bootRoom : B.advice.offset + FiniteBoot.width B.advice.count r ≤ B.layout.literal
  extension : ExtendedFrame.Fits W B.frameBase B.advice.dst pre.length
  frameEnd : B.frameBase+112 ≤ B.broadcastBase
  profileEnd : B.broadcastBase+1+reserve ≤ (A).next
  stopFits : stop < 2^W
  inputClear : PinClear B.layout 0 (B.layout.processors*B.layout.stride)
  frameClear : PinClear B.layout B.frameBase 112
  headerClear : PinClear B.layout B.broadcastBase B.header
  pinWidth : B.layout.width ≤ B.layout.count
  loopFit : LoopFits W B.layout

set_option maxRecDepth 3000 in
/-- All addresses and scalar operands follow from a single upper address ceiling.
The bound on the bootstrap copy is its rounded width in the real literal. -/
theorem placed (start reserve stop : ℕ) (u : Fin (R+1)) (header : 1+reserve ≤ L.header)
    (boot : start+FiniteBoot.width (A).copied r ≤ lit) (pins : d ≤ r*lit)
    (below : (A).next ≤ stop) (ceiling : stop < 2^W) :
    Placed G L pre (operands G L pre ext ref start u) reserve stop := by
  let B := operands G L pre ext ref start u
  have three := L.three
  let edge : Routing.Block (R+1) := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),Nat.zero_lt_one⟩
  have blockFit : L.header ≤ link*r := by have := L.fits edge; rw [Nat.mul_comm]; omega
  have positive : 0<L.header := by omega
  have procs : 0<r := Nat.pos_of_mul_pos_left (positive.trans_le blockFit)
  have peers : 0<link := Nat.pos_of_mul_pos_right (positive.trans_le blockFit)
  have litPos : 0<lit := by have : 0 < FiniteBoot.width (A).copied r := Nat.zero_lt_succ _; omega
  have large : (A).frame+112+(A).copied+L.header+2*(A).count < 2^W := by
    have last := below.trans_lt ceiling
    change (A).frame+112+(A).copied+L.header+(A).count+(A).count < 2^W at last
    omega
  have wordPos : 0<W := by
    by_contra! hz
    have zero : W=0 := by omega
    have wall : 112 < 2^W := by omega
    rw [zero,pow_zero] at wall
    omega
  have copied : (A).copied = (pre.length+81)*W := rfl
  have entries : pre.length ≤ (A).copied := copied ▸ (Nat.le_add_right pre.length 81).trans (Nat.le_mul_of_pos_right _ wordPos)
  have stride : B.layout.stride = (A).stride := by change lit+R*link+lit = 2*lit+((R+1)-1)*link; simp; omega
  have frame : B.layout.processors*B.layout.stride = (A).frame := by rw [stride]; rfl
  have strideLe : (A).stride ≤ (A).frame := Nat.le_mul_of_pos_left _ procs
  have litLe : lit ≤ (A).stride := by change lit ≤ 2*lit+((R+1)-1)*link; omega
  have teamLe : R+1 ≤ (A).stride := by
    have := Nat.le_mul_of_pos_right R peers
    change R+1 ≤ 2*lit+((R+1)-1)*link; simp; omega
  have linkLe : link ≤ (A).stride := by
    have := Nat.le_mul_of_pos_left link (by omega : 0<R)
    change link ≤ 2*lit+((R+1)-1)*link; simp; omega
  have processors : r ≤ (A).count := Nat.le_mul_of_pos_right _ litPos
  have pin : d ≤ (A).count := pins
  have ib : (A).ibase = (A).frame+112+(A).copied+L.header := rfl
  have hb : (A).hbase = (A).ibase+(A).count := rfl
  have next : (A).next = (A).hbase+(A).count := rfl
  have broad : (A).broadcastBase = (A).frame+112+(A).copied := rfl
  change Placed G L pre B reserve stop
  refine ⟨?_,?_,rfl,boot,?_,?_,?_,ceiling,?_,?_,?_,pin,?_⟩
  · intro x hx
    change x ∈ [(A).frame,u.val,R+1,r,lit,link,L.header,(A).ibase,(A).hbase,d,(A).dense,(A).broadcastBase,
      start,(A).copied,(A).dense,pre.length,W] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    have own := u.isLt
    have hw : W<2^W := Nat.lt_two_pow_self
    have dense : (A).dense=(A).frame+112 := rfl
    rcases hx with eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq <;> subst x <;> omega
  · exact ⟨three,u.isLt,procs,peers,positive,blockFit,le_rfl,
      by change (A).frame+31 ≤ (A).broadcastBase; omega,
      by change (A).broadcastBase+L.header < 2^W; omega⟩
  · refine ⟨by change (A).frame+112 < 2^W; omega,le_rfl,?_⟩
    change (A).frame+112+pre.length*W+81*W < 2^W
    have : pre.length*W+81*W=(A).copied := by rw [copied,Nat.add_mul]
    omega
  · change (A).frame+112 ≤ (A).broadcastBase; omega
  · change (A).broadcastBase+1+reserve ≤ (A).next; omega
  · unfold PinClear
    rw [frame]
    exact ⟨Or.inl (by change 0+(A).frame ≤ (A).ibase; omega),Or.inl (by change 0+(A).frame ≤ (A).hbase; omega)⟩
  · exact ⟨Or.inl (by change (A).frame+112 ≤ (A).ibase; omega),Or.inl (by change (A).frame+112 ≤ (A).hbase; omega)⟩
  · exact ⟨Or.inl (by change (A).broadcastBase+L.header ≤ (A).ibase; omega),
      Or.inl (by change (A).broadcastBase+L.header ≤ (A).hbase; omega)⟩
  · refine ⟨litPos,fun i hi => (livePinAddress_lt B.layout hi).trans_le ?_,?_,?_⟩
    · rw [frame]; omega
    · intro i hi; change i<(A).count at hi; change (A).ibase+i < 2^W; omega
    · intro i hi _; change i<(A).count at hi; change (A).hbase+i < 2^W; omega

/-- The two actual serialized stripes and the data half-tail occupy disjoint ranges in
the field literal. The geometry width uses the true packet bit count. -/
theorem stripes (D : Packing.Directory.Layout) (start free reserve k o b : ℕ) (u : Fin (R+1))
    (hr : 1≤r) (size : start+free=D.literal) (litEq : D.literal=lit)
    (boot : start+FiniteBoot.width (A).copied r ≤ lit/4)
    (geometry : lit/4+GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve k o b*W) r ≤ lit-lit/2) :
    let ell := GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve k o b*W) r
    let f := (operands G L pre ext ref start u).broadcast
    JointRoom D start free (FiniteBoot.bootStripe (advice A start) f (pre.length+81))
      (Allocation.stripe (A).next reserve k o b (lit/4) ell) ∧
      0<ell ∧ lit/4+ell≤lit ∧ GeometryOutput.packetCount reserve k o b*W ≤ r*ell := by
  intro ell f
  refine ⟨⟨size,le_rfl,boot,?_⟩,Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..),?_,
    GeometryAdviceRate.stripe_capacity _ hr⟩
  · rw [litEq]; exact geometry
  · exact geometry.trans (Nat.sub_le ..)

end FiniteDiagonal.ProfileArena

end BorderVNP
end Computability
end OAI
