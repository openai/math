import OAI.Hierarchy.DescentResetParentAddresses
import OAI.Hierarchy.DescentResetHostParentDirectory
import OAI.Hierarchy.DescentDatedAddressRate
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Fixed fresh quotient, prefix and scatter banks for the genuine previous-host directory -/
namespace Hierarchy.DescentResetParentAperture
open DescentDyadicSpan DescentCensusRAM DescentDatedAddressBook ProtocolRAM Filter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

theorem bounded {ι : ℕ→Type*} {slots pad : ∀h,ι h→ℕ} (s : Bounded slots) (p : Bounded pad) :
    Bounded (fun h i=>endAddress 0 (slots h i) (pad h i)) := by
  apply (((((s.padded.add (s.add (Bounded.const 1)).padded).add s).add s).add ((Bounded.const 2).mul s)).add
    ((p.add (Bounded.const 1)).max' p.padded)).of_le
  intro h i
  rw [extent]
  simp only [span,Nat.zero_add,Nat.le_refl]

def originalProgram (base slots pad shapes : ℕ) (flags : Bank) (w : ℕ) (room : endAddress base slots pad<2^w) : Procedure w :=
  let b:=banks base slots pad w room
  let dest:=DescentHubBits.destination b.bins pad flags (ids base slots)
  (DescentStaticWordColumn.program w (codes base slots).base (fun j=>j/shapes) slots).seq
    ((ProtocolRAMEndpointPrefix.exclusive w flags.base (ids base slots).base slots).seq (tally b dest (.lookup (codes base slots) .row)))

def originalTicks (base slots pad : ℕ) (flags : Bank) (w : ℕ) (room : endAddress base slots pad<2^w) :=
  let b:=banks base slots pad w room
  let dest:=DescentHubBits.destination b.bins pad flags (ids base slots)
  (4+10*slots)+((10+(3+12*slots))+tallyCost b dest (.lookup (codes base slots) .row))

open DescentSixParty DescentDenseHostOrder DescentCommonHost
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Z.Terminals)
local notation "S" => Finset.card (DescentDenseHostOrder.roster Z.graph (Z.k-T.commonDepth) Ht)
variable {H pad : ℕ} (vertex : Z.V↪Fin H) (capacity : Fintype.card ↥(Z.commonNames T)≤pad)
local notation "slots" => H*S

theorem original_publish {w : ℕ} (base : ℕ) (flags : Bank) (mem : Memory w)
    (lo : flags.Fits w base) (rows : slots≤flags.size) (room : endAddress base slots pad<2^w)
    (reads : ∀j:Fin slots,mem (flags.base+j.val)=
      (DescentEdgeTapePrefix.row (fun _ : ↥(Z.commonNames T)=>1) (fun v=>(Z.rawHostRank T vertex v).val) j.val:Word w)) :
    ∃dst : Memory w,(originalProgram base slots pad S flags w room).Exec mem dst (originalTicks base slots pad flags w room) ∧
      CheapCode (originalProgram base slots pad S flags w room) ∧ originalTicks base slots pad flags w room≤220*(1+slots+pad) ∧
      DescentResetStemKeyReindex.Directory (parent base slots pad).base (Z.parentIndex T vertex) dst ∧
      (∀j:Fin pad,(¬∃v : ↥(Z.commonNames T),(Z.denseHostRank T vertex v).castLE capacity=j)→dst ((parent base slots pad).base+j.val)=0) ∧ ∀a<base,dst a=mem a := by
  obtain ⟨codeFit,idFit,exclusiveFit,_⟩:=fits room
  have earlier : base≤first base slots := by
    change base ≤ base + span slots + span (slots+1)
    omega
  have flagsFit : flags.Fits w (first base slots) := ⟨lo.1,lo.2.1,lo.2.2.trans earlier⟩
  have oc : slots≤(codes base slots).size:=Nat.le_pow_clog (by decide : 1 < 2) _
  have oi : slots≤(ids base slots).size :=(Nat.le_succ slots).trans (Nat.le_pow_clog (by decide : 1 < 2) _)
  have fc : flags.base+slots≤(codes base slots).base :=(Nat.add_le_add_left rows _).trans lo.2.2
  have ci : (codes base slots).base+slots≤(ids base slots).base :=Nat.add_le_add_left oc _
  obtain ⟨dst,run,cheap,price,held,ghost,keep⟩:=Z.publish_parents T vertex capacity (banks base slots pad w room)
    flags (ids base slots) (codes base slots) mem flagsFit idFit codeFit rows oi oc fc ci exclusiveFit reads
  refine ⟨dst,run,cheap,price,Z.parent_directory T vertex _ dst ?_,ghost,?_⟩
  · intro v
    exact held v
  · intro a ha
    apply keep
    exact lt_min_iff.mpr ⟨ha,lt_min_iff.mpr ⟨ha.trans_le (Nat.le_add_right ..),ha.trans_le earlier⟩⟩

end
end Hierarchy.DescentResetParentAperture

end OAI
