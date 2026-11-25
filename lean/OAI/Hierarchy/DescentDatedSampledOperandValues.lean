import OAI.Hierarchy.DescentDatedOperandRootSize
import OAI.Hierarchy.DescentDatedMaterialPhase
import OAI.Hierarchy.DescentDatedSortedBroadcast
import OAI.Hierarchy.DescentRootOrderCast

namespace OAI
/-! # Original signed, prior and newborn words at the physical operand reader -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip
open DescentRawCablePanel DescentHaloWalkRAM DescentSharedCableNames
open scoped Classical Fin.CommRing
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
set_option quotPrecheck false
set_option hygiene false
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (fmt).degree
local notation "O" => DepotRAM.Material.roles fmt
local notation "l" => v.resolver
local notation "g" => v.ticketReadGeometry
local notation "J" => (l).jobs
local notation "d" => v.operandShortBits
local notation "b" => (e).fieldBits
local notation "pwidth" => Packed.bits P

set_option hygiene true

def walkValues (reach : Fin (e).oldHosts→Fin P→Option (Fin (e).oldHosts)) :=
  SortedInput.Broadcast.value g v.materialPitch reach

structure OriginalData where
  origin : Fin J → Fin 6 → Values g d
  prior : Fin J → Fin 4 → Values g ((l).size+2)
  mouth : Fin J → Fin 3 → Values g v.bornBook.bits
  old : Fin J → Fin 4 → Fin (P*((fmt).blocks*((fmt).degree*(fmt).cap))) → Values g b
  path : Fin (P*((fmt).degree+1)) → Values g pwidth
  anchor : Fin J → Fin 5 → Fin (P*((fmt).blocks*((fmt).cap*3))) → Values g b
  raw : Fin J → Fin 8 → Fin (P*O) → Values g b
  rank : Fin P → Values g pwidth

section
variable (blocks : (l).blocks=(e).blocks)
def receiverBlock (job : Fin J) := ((l).index.symm job).1.cast blocks

end

variable (data : v.OriginalData)
def originalValues : Data g :=
  ⟨data.origin,
   fun j f h k=>DescentRootOrderCast.widen (data.prior j f h k),
   fun j f h k=>DescentRootOrderCast.widen (data.mouth j f h k),
   fun j f i h k=>DescentRootOrderCast.widen (data.old j f i h k),
   fun i h k=>DescentRootOrderCast.widen (data.path i h k),
   fun j f i h k=>DescentRootOrderCast.widen (data.anchor j f i h k),
   fun j f i h k=>DescentRootOrderCast.widen (data.raw j f i h k),
   fun i h k=>DescentRootOrderCast.widen (data.rank i h k)⟩

section
local notation "oldVal" n => (Fin (e).hosts → Fin (e).groups → Cell n)
variable (blocks : (l).blocks=(e).blocks) (bound : (l).hosts≤(e).hosts) (groups : (l).groups=(e).groups)
variable (origin : Fin J → Fin 6 → Values g d) (prior : Fin J → Fin 4 → Values g ((l).size+2))
    (born : Fin J → Fin 3 → Values g v.bornBook.bits)
    (wide : v.WideHead → oldVal b) (narrow : v.NarrowHead → oldVal pwidth)

def sampleHeads : v.OriginalData :=
  let x:=v.receiverBlock blocks
  let hi:=fun (i : v.WideHead) (h : Fin (l).hosts) (k : Fin (l).groups)=>wide i (h.castLE bound) (k.cast groups)
  let lo:=fun (i : v.NarrowHead) (h : Fin (l).hosts) (k : Fin (l).groups)=>narrow i (h.castLE bound) (k.cast groups)
  ⟨origin,prior,born,fun j f i=>hi (.inl (x j,f,i)),fun i=>lo (.inl i),
    fun j f i=>hi (.inr (.inl (x j,f,i))),fun j f i=>hi (.inr (.inr (x j,f,i))),fun i=>lo (.inr i)⟩

end

theorem widen_operand_value (i : Fin 4) (x : Cell (v.operandWidth i)) :
    (DescentRootOrderCast.widen x : Cell d).val=x.val :=
  Fin.val_cast_of_lt (x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (v.operandWidth_le i)))

theorem original_rank_number (p : Fin P) (h : Fin (g).hosts) (y : Fin (g).groups) :
    ((v.originalValues data).rank p h y).val=(data.rank p h y).val :=
  v.widen_operand_value 3 (data.rank p h y)

theorem original_raw_number (j : Fin J) (f : Fin 8) (i : Fin (P*O)) (h : Fin (g).hosts) (y : Fin (g).groups) :
    ((v.originalValues data).raw j f i h y).val=(data.raw j f i h y).val :=
  v.widen_operand_value 0 (data.raw j f i h y)

theorem original_anchor_number (j : Fin J) (f : Fin 5) (i : Fin (P*((fmt).blocks*((fmt).cap*3))))
    (h : Fin (g).hosts) (y : Fin (g).groups) :
    ((v.originalValues data).anchor j f i h y).val=(data.anchor j f i h y).val :=
  v.widen_operand_value 0 (data.anchor j f i h y)

theorem original_prior_number (j : Fin J) (f : Fin 4) (h : Fin (g).hosts) (y : Fin (g).groups) :
    ((v.originalValues data).prior j f h y).val=(data.prior j f h y).val :=
  v.widen_operand_value 1 (data.prior j f h y)

theorem original_mouth_number (j : Fin J) (f : Fin 3) (h : Fin (g).hosts) (y : Fin (g).groups) :
    ((v.originalValues data).mouth j f h y).val=(data.mouth j f h y).val :=
  v.widen_operand_value 2 (data.mouth j f h y)

theorem original_old_number (j : Fin J) (f : Fin 4) (i : Fin (P*((fmt).blocks*((fmt).degree*(fmt).cap))))
    (h : Fin (g).hosts) (y : Fin (g).groups) :
    ((v.originalValues data).old j f i h y).val=(data.old j f i h y).val :=
  v.widen_operand_value 0 (data.old j f i h y)

theorem original_path_number (i : Fin (P*((fmt).degree+1))) (h : Fin (g).hosts) (y : Fin (g).groups) :
    ((v.originalValues data).path i h y).val=(data.path i h y).val :=
  v.widen_operand_value 3 (data.path i h y)



end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
