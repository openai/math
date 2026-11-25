import OAI.Hierarchy.DescentPrivateInstalledWidth
import OAI.Hierarchy.DescentDepotRoom

namespace OAI
/-! # Append an ordinary fee meter to the prior physical matching output -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentRawCablePanel.DepotRAM DescentRawCablePanel DescentSIMDLookup DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
namespace DonorSpace

/-- The middle span is the actual width of the intervening mutable owner and hub computation. -/
def dynamicStart (base setup : ℕ) := base+2*(setup+1)
def source (base setup dynamic rows : ℕ) : Bank :=
  ⟨dynamicStart base setup+dynamic,Nat.clog 2 rows⟩
def meterBase (base setup dynamic rows : ℕ) :=
  let s:=source base setup dynamic rows;s.base+s.size
def endAddress (base setup dynamic rows payload : ℕ) :=
  meterBase base setup dynamic rows+8*rows+2*2^(payload/2)+12

theorem translate (base setup dynamic rows payload : ℕ) :
    endAddress base setup dynamic rows payload=base+endAddress 0 setup dynamic rows payload := by
  simp [endAddress,meterBase,source,dynamicStart,Bank.size,Nat.add_assoc]

theorem bound (base setup dynamic rows payload K : ℕ) (budget : setup≤2*rows+K*2^(payload/2)) :
    endAddress base setup dynamic rows payload ≤base+dynamic+14*rows+(2*K+2)*2^(payload/2)+16 := by
  have padded:=(ceilPage rows).2
  unfold endAddress meterBase source dynamicStart Bank.size
  nlinarith only [padded,budget]

theorem leaves (base setup dynamic rows payload : ℕ) :
    rows≤(source base setup dynamic rows).size ∧
    base+2*(setup+1)≤(source base setup dynamic rows).base ∧
    (source base setup dynamic rows).base+(source base setup dynamic rows).size≤ meterBase base setup dynamic rows+1 ∧
    meterBase base setup dynamic rows+1+rows<endAddress base setup dynamic rows payload := by
  have padded:=ceilPage rows
  refine ⟨padded.1,by dsimp [source,dynamicStart];omega,Nat.le_succ _,?_⟩
  unfold endAddress;omega

end DonorSpace

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k i z D wire hist : ℕ} {W : MarkedWorld F d P bits}
variable {prior : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
variable {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink prior he T c n target)
namespace OrdinaryLink
variable (short profile H h : ℕ)
local notation "fmt" => ticket.depotShape short
local notation "zfmt" => shape (2^k) prior.placement.degree (2*prior.placement.cap) profile
local notation "sum" => ticket.installedDonorWidth short profile
local notation "lan" => lanes h sum
local notation "rows" => H*chunks (S.groupCount i) lan

def setupWords := Setup.words fmt zfmt (2^(k+1)) H (S.groupCount i) lan sum

variable (oldEnd dynamicWords : ℕ)
local notation "bytes" => setupWords ticket short profile H h
def donorStart := DonorSpace.dynamicStart oldEnd bytes
def donorSource := DonorSpace.source oldEnd bytes dynamicWords rows
def donorMeter := DonorSpace.meterBase oldEnd bytes dynamicWords rows
def donorEnd := DonorSpace.endAddress oldEnd bytes dynamicWords rows h

theorem donorEnd_translate :
    donorEnd ticket short profile H h oldEnd dynamicWords =
    oldEnd+donorEnd ticket short profile H h 0 dynamicWords := DonorSpace.translate ..

/-- Includes the complete literal setup, the chosen dynamic geometry, the intermediate
gather bank, both eleven-role dictionaries, the prefix accumulators and the header copy. -/
theorem donorEnd_bound :
    donorEnd ticket short profile H h oldEnd dynamicWords ≤oldEnd+dynamicWords+14*rows+
      (2*(2*Binary.count fmt+3+2^(k+1))+2)*2^(h/2)+16 :=
  DonorSpace.bound _ _ _ _ _ _ (ticket.installed_donor_books short profile H h)

theorem donor_fits (padded : Fintype.card prior.V≤H) {header w factor : ℕ} (historic : header≤oldEnd)
    (width : 2*sum≤h) (word : h≤w) (overhead : w≤factor*h)
    (space : donorEnd ticket short profile H h oldEnd dynamicWords≤2^w) :
    MeterPort.Fits ticket (sizedDepotPort H padded (donorMeter ticket short profile H h oldEnd dynamicWords) h sum) header w factor := by
  have front : oldEnd≤donorMeter ticket short profile H h oldEnd dynamicWords := by
    change oldEnd ≤ oldEnd+2*(bytes+1)+dynamicWords+_
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  apply sizedDepot_fit ticket short H padded _ h sum (ticket.installed_donor_widths short profile).1
    (historic.trans front) width word overhead
  change donorMeter ticket short profile H h oldEnd dynamicWords+8*rows+2*2^(h/2)+12≤2^w at space
  omega

end OrdinaryLink
end
end Hierarchy.DescentSixParty.Chronology

end OAI
