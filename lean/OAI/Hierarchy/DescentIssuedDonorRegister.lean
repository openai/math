import OAI.Hierarchy.DescentIssuedDonors
import OAI.Hierarchy.DescentPackedPrivateStage

namespace OAI
/-! # Advancing the private archive word from the real matched donor column -/

namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM DescentStageEdgeReceipt DescentPacking DescentSIMDLookup
open DescentPackedPrivateSum DescentRawCablePanel DescentHostDegree DescentSixParty.StarKeys
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist} (path : Path start source)
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)
variable {H : ℕ} (vertex : source.V↪Fin H) (previous base : ℕ)
local notation "A" => source.placement
local notation "cellBits" => normBits (A).cap G.b G.C G.k
local notation "J" => S.groupCount i*2^k*(A).cap
local notation "shelf" => 2^(packExponent 20 T.Δ)+2
local notation "gain" => gainExponent 20 T.Δ
local notation "names" => donorNameBits T.k T.Δ
local notation "inputBits" => bundleBits 3 names cellBits
local notation "short" => 2+cellBits
local notation "full" => max inputBits (short*11)
local notation "M" => lanes bw full
local notation "bank" => DescentPackedDonorSpace.banks base H J M inputBits
local notation "L₀" => DescentPackedDonorSpace.layout base H J M inputBits short
local notation "C₀" => DescentPackedDonorSpace.counters previous base H J M inputBits short

/-- All finite digital formats, both owner bits, the scale, the table literals
and the incoming/output count are fixed by this very same issued branch. -/
theorem Path.Held.measured_donor_stage
    (m : Memory bw) (held : path.Held previous m) (prev : previous≤base) (wide : 2*full≤bw)
    (fit : DescentPackedDonorSpace.endAt base H J M inputBits short<2^bw)
    (pins : ∀p : Row H J M,m ((bank).source.base+(row H J M p).val)=
      (data («M»:=M) (fun v j=>packDonor (ticket.measuredDonors vertex v j)) p).val) :
    let init:=DescentPackedDonorTables.program bank (L₀).rom.base H J M bw (donorROM T.k gain shelf 3 names cellBits) score
    ∃out,(init.seq ((DescentSIMDLookup.program bank (L₀).source.base H J M bw).seq
      (DescentPackedPrivateAccumulator.program L₀ C₀ bw H (J*11) (M*11) T.z))).Exec m out
      ((4+10*DescentPackedDonorTables.size bank (L₀).rom.base short M)+
        ((4+44*(H*chunks J M))+(Layout.billed H (J*11) (M*11)+(C₀).scaling.steps T.z))) ∧
      (path.ordinary ticket).Held (C₀).out out :=
  Path.Held.donor_setup_stage path ticket vertex previous base T.k gain shelf (ticket.measuredDonors vertex)
    (ticket.donor_words vertex) m held prev wide fit pins

end
end Hierarchy.DescentSixParty.Chronology

end OAI
