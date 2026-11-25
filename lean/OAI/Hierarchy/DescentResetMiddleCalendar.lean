import OAI.Hierarchy.DescentIssuedRootWidths
import OAI.Hierarchy.DescentFallbackPacketAllowance
import OAI.Hierarchy.DescentPhysicalResetReceipt
import OAI.Hierarchy.DescentPhysicalResetRoots

namespace OAI
/-! # Public reset middle addresses from the cap calendar and the actual root instructions -/
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentPackedWalsh DescentWalshPrecision
open DescentSIMDLookup DescentPlainTerminal.Suffix DescentFallbackPeriod DescentPackedPrivateMenu
open DescentPackedColony DescentResetGates DescentFallbackPeriod.Projected
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- Bits for a sender root, socket, original shape, or signed old index. -/
def senderWidth (k n Ht cap : ℕ) := 2*k+2*n+Ht+Nat.clog 2 (cap+1)+10

/-- The same operand digit holds the old signed cable, terminal shape, paid cap, and
reservation fields. The five returned private geometry digits have their own width. -/
def fieldWidth (D cap n k Ht : ℕ) :=
  max (packetField D cap n k Ht) (max (k+1) (max (n+1) (max (Nat.clog 2 (cap+1)) (senderWidth k n Ht cap))))

def privateWidth {n h : ℕ} (board : NonlinearExpanders.Graph n h) (k Ht f cap C packet : ℕ) :=
  fieldBits board k Ht (2^k*(2*cap)) (DescentRecordedRotorLayers.width f cap) C packet

def rootArity (D cap n k : ℕ) (p : RootPage k (2^n)) : ℕ :=
  match p.2 with
  | .inl (_, .inl false)=> DescentRotorWindowArchive.count D (2^k) cap
  | .inl (_, .inl true)=>3
  | .inl (_, .inr _)=> DescentIssuedRotorRoles.guardInputs D (2^k) cap
  | .inr _=> inputCount D (2^k) cap n k

/-- Number of words mounted per page. This counts the actual two zip dictionaries for
each input digit, final lookup, masks, width conversion and reservation/depth tables. -/
def lawWidth (D cap n k H G M field prior levels total : ℕ) :=
  let size (p : RootPage k (2^n)) :=
    let N:=rootArity D cap n k p
    N*(2*2^((field*N+field)*M))+2^(field*N*M)+2^(Nat.clog 2 (H*chunks G M))
  1+Finset.univ.sup size+max (2^(prior*M)) (DescentReservationHeader.reserveEntries H levels total)

def fromCalendar (S : AtomSchedule) (k tail age p f D payload e previous n Ht : ℕ)
    (calendar : List ℕ) : ResetMiddle :=
  let H:=S.hostSize age
  let c:=S.groupWidth k tail age
  let m:=c+k
  let cap:=(calendar.take age).prod*256
  let b:=S.localWalshBits p m f (quota S.rounds)
  let field:=fieldWidth D cap n k Ht
  let prior:=k+b+2
  let levels:=Nat.clog 2 (m+2)
  let total:=m+S.censusBits p
  let st : StencilBook :=
    ⟨H,c,m,D,D,m-laneBits m payload b,2^e,b,prior,2*k+n+2,levels,total⟩
  ⟨st,2*cap,H,c-e,e+k,DescentSignedCableCodec.width D cap,2^k,2^e,2^(previous-e),
    H,2^c,2^e,k,n,D,2^Ht,field,lawWidth D cap n k H (2^c) (2^e) field prior levels total⟩

variable (S : AtomSchedule) (k tail age radix p f D payload e previous n Ht : ℕ)
    (calendar : List ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank) (out : ResetOutput)
local notation "middle₀" => fromCalendar S k tail age p f D payload e previous n Ht calendar
local notation "c₀" => S.groupWidth k tail age
local notation "b₀" => S.localWalshBits p (c₀+k) f (quota S.rounds)
set_option quotPrecheck false
local notation "date₀" => PhysicalReset.fromCalendar S k tail age radix p f D payload e (k+b₀+2) (2*k+n+2)
  calendar addr roster {out with middle:=middle₀}

theorem physical_middle : (date₀).successor.middle=middle₀:=rfl

theorem physical_shape : (date₀).RootShape := by
  constructor <;> simp [PhysicalReset.fromCalendar,fromCalendar]

theorem signed_dimensions (batch : e≤ c₀) :
    2^((middle₀).high+(middle₀).low)=(middle₀).rootGroups*(middle₀).oldBlocks ∧
    2^(middle₀).low=(middle₀).signedLanes*(middle₀).oldBlocks := by
  change 2^((c₀-e)+(e+k))=2^c₀*2^k ∧ 2^(e+k)=2^e*2^k
  rw [←pow_add,←pow_add]
  exact ⟨congrArg (2^·) (by omega),rfl⟩

theorem retile_slots (batch : e≤ previous) (small : previous≤ c₀) :
    (middle₀).rootGroups=
      ((middle₀).rootGroups/((middle₀).signedRatio*(middle₀).signedLanes))*
        ((middle₀).signedRatio*(middle₀).signedLanes) := by
  change 2^c₀=(2^c₀/(2^(previous-e)*2^e))*(2^(previous-e)*2^e)
  rw [←pow_add,Nat.sub_add_cancel batch]
  have capacity : 2^(c₀-previous)*2^previous=2^c₀:=by rw [←pow_add,Nat.sub_add_cancel small]
  have divides : 2^previous ∣ 2^c₀ :=
    ⟨2^(c₀-previous), capacity.symm.trans (Nat.mul_comm _ _)⟩
  exact (Nat.div_mul_cancel divides).symm

variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr) (f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "Book" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage

theorem issued_arity_exact (p : RootPage r (2^n)) :
    ((Book).table p).1=rootArity D cap n r p ∧ ((Book).table p).2.field=field := by
  obtain ⟨s,(⟨v,(flag|gate)⟩|v)⟩:=p
  · cases flag <;> exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩

theorem issued_law_width :
    (Book).width H (2^c) M=lawWidth D cap n r H (2^c) M field stencil.n (Nat.clog 2 (E.dim+2)) total := by
  unfold RootBook.width RootBook.payloadWidth lawWidth
  have size (p : RootPage r (2^n)) :
      ((Book).table p).2.stop 0 H (2^c) M=
        let z:=rootArity D cap n r p
        z*(2*2^((field*z+field)*M))+2^(field*z*M)+2^(Nat.clog 2 (H*chunks (2^c) M)) := by
    obtain ⟨arity,width⟩:=issued_arity_exact a E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
      f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage p
    simp only [RootTable.stop,RootTable.split,RootTable.unit,Nat.zero_add,arity,width]
  simp_rw [size]
  rfl

end
end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
