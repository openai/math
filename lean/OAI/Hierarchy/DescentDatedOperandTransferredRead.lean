import OAI.Hierarchy.DescentDatedSampledOperandValues
import OAI.Hierarchy.DescentDatedOperandPhysicalRead
import OAI.Hierarchy.DescentDatedOperandHeaderPair

namespace OAI
/-! # Match all five earlier signed-pitch families to the achieved resolver memory -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip
open DescentRawCablePanel DescentHaloWalkRAM DescentSharedCableNames ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "l" => v.resolver
local notation "g" => v.ticketReadGeometry
local notation "J" => (l).jobs
local notation "d" => v.operandShortBits
local notation "b" => (e).fieldBits
local notation "pwidth" => Packed.bits (breadth (fmt).degree)
local notation "oldVal" n => (Fin (e).hosts → Fin (e).groups → Cell n)
variable (blocks : v.resolver.blocks=v.material.blocks) (bound : v.resolver.hosts≤v.material.hosts) (groups : v.resolver.groups=v.material.groups)
variable (origin : Fin v.resolver.jobs → Fin 6 → Values v.ticketReadGeometry v.operandShortBits)
    (prior : Fin v.resolver.jobs → Fin 4 → Values v.ticketReadGeometry (v.resolver.size+2))
    (born : Fin v.resolver.jobs → Fin 3 → Values v.ticketReadGeometry v.bornBook.bits)
    (wide : v.WideHead → Fin v.material.hosts → Fin v.material.groups → Cell v.material.fieldBits)
    (narrow : v.NarrowHead → Fin v.material.hosts → Fin v.material.groups → Cell (Packed.bits (breadth (v.ticket.depotShape v.short).degree)))

private theorem at_groups {K H G G' w n : ℕ} {expr : Expr} {values : Fin H → Fin G → Cell n} {m : Memory w}
    (same : G'=G) (source : Source expr values K m) : Source expr (fun h (k : Fin G')=>values h (k.cast same)) K m :=by
  subst G'
  exact source

variable {w : ℕ} (floor : ℕ) (c : v.SignedChart) (A : v.ArgumentEntry) («matching» : A.Match v floor) (shape : v.VectorShape)
local notation "base" => v.operandHeaderEnd floor
local notation "top" => v.headTransferEnd floor
set_option maxHeartbeats 900000
theorem transferred_reads (m : Memory w)
    (fw : ∀i,(v.wideHead floor c i).Fits w base) (fn : ∀i,(v.narrowHead floor i).Fits w base)
    (space : top<2^w) (positive : 0<(e).lanes)
    (ww : ∀i,Source (v.wideHead floor c i) (wide i) (e).lanes m)
    (nn : ∀i,Source (v.narrowHead floor i) (narrow i) (e).lanes m)
    (witness : ∀j f,Held g base m (v.originAt floor d shape j f) (origin j f))
    (earlier : ∀j f,Held g base m (v.oldHeaderAt floor j f) (prior j f))
    (mouth : ∀j f,Held g base m (v.mouthAt floor A «matching» shape j f) (born j f)) :
    let code:=v.headTransferPhase floor c w
    Step base top code m ∧ v.OriginalReads floor A «matching» shape blocks (v.sampleHeads blocks bound groups origin prior born wide narrow) (code.image m) :=by
  intro code
  have ran:=v.head_transfer_any floor c m fw fn space
  have step:Step base top code m := ⟨by rw [v.head_transfer_span];exact Nat.le_add_right ..,ran.1,ran.2⟩
  have hi (i : v.WideHead) : Held g top (code.image m) (v.wideWord floor i)
      (fun h k=>wide i (h.castLE bound) (k.cast groups)) :=
    ⟨v.wide_word_fits floor space i,at_groups groups (v.wide_word_source floor c m fw fn space i (wide i) positive (ww i) bound)⟩
  have lo (i : v.NarrowHead) : Held g top (code.image m) (v.narrowWord floor i)
      (fun h k=>narrow i (h.castLE bound) (k.cast groups)) :=
    ⟨v.narrow_word_fits floor space i,at_groups groups (v.narrow_word_source floor c m fw fn space i (narrow i) positive (nn i) bound)⟩
  exact ⟨step,⟨fun j f=>Step.keep g (p:=code) (m:=m) step (witness j f),fun j f=>Step.keep g (p:=code) (m:=m) step (earlier j f),
    fun j f=>Step.keep g (p:=code) (m:=m) step (mouth j f),fun j f i=>hi (.inl (v.receiverBlock blocks j,f,i)),
    fun i=>lo (.inl i),fun j f i=>hi (.inr (.inl (v.receiverBlock blocks j,f,i))),
    fun j f i=>hi (.inr (.inr (v.receiverBlock blocks j,f,i))),fun p=>lo (.inr p)⟩⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
