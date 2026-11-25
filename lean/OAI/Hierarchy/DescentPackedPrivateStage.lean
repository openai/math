import OAI.Hierarchy.DescentPrivatePanelFrame
import OAI.Hierarchy.DescentPackedDonorTables
import OAI.Hierarchy.DescentPackedDonorSpace
import OAI.Hierarchy.DescentIssuedPanelRegister
import OAI.Hierarchy.DescentPackedRawDonor

namespace OAI
/-! # Accumulating the eleven emitted cable roles in their original physical words -/

namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM DescentHistoryOrder DescentKernelHistory DescentStageEdgeReceipt DescentPacking
open DescentSIMDLookup DescentPackedPrivateSum DescentPackedPrivateAccumulator DescentRawCablePanel
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist} (path : Path start source)
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)
variable {H loc names M : ℕ} (vertex : source.V↪Fin H)

local notation "A" => source.placement
local notation "r" => BitDescription.scannedRows he T
local notation "cellBits" => normBits source.placement.cap G.b G.C G.k
local notation "J" => S.groupCount i*2^k*source.placement.cap

/-- The lookup pass and accumulator share the exact same packed words. The sole
per-donor semantic input is its eleven local field values in the issued roster.
The prior count and immutable scoring table are recovered through the lookup's
actual memory frame. -/
theorem Path.Held.donor_stage_framed (hostBits groupBits slots : ℕ)
    (banks : DescentSIMDLookup.Banks) (L : Layout) (C : Counters)
    (donors : Fin H→Fin J→Donor loc names cellBits)
    (records : ∀v j,report hostBits groupBits slots
      (donors v (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2=ticket.issuedPanel vertex v j)
    (m : Memory bw) (positive : 0<M) (held : path.Held C.prior m)
    (fit : Fits banks (bundleBits loc names cellBits) ((2+cellBits)*11) M H J bw L.source.base)
    (loaded : PinFrame (M:=M) banks (donorROM hostBits groupBits slots loc names cellBits)
      (fun v j=>packDonor (donors v j)) m)
    (table : ∀key : Cell ((2+cellBits)*(M*11)),m (L.rom.base+key.val)=
      (DescentPackedScore.chunkScore (M:=M*11) score key:Computability.VPVNP.BurstRAM.Word bw))
    (tableApart : L.rom.base+2^((2+cellBits)*(M*11))≤L.source.base ∨
      L.source.base+H*chunks J M≤L.rom.base)
    (keep : C.prior<L.source.base) (room : L.Room bw H (J*11) (M*11)) (space : C.scaling.Room bw)
    (rows : Layout.count H (J*11) (M*11)≤L.source.size) (bitsFit : L.rom.bits=(2+cellBits)*(M*11))
    (atEnd : C.words=L.starts+Layout.count H (J*11) (M*11)) (prior : C.prior<L.words) :
    let mid:=ProtocolRAM.image L.source.base (H*chunks J M) (lookup banks) m
    let out:=DescentPackedPrivateAccumulator.image L C H (J*11) (M*11) T.z mid
    ((DescentSIMDLookup.program banks L.source.base H J M bw).seq
      (DescentPackedPrivateAccumulator.program L C bw H (J*11) (M*11) T.z)).Exec m out
      ((4+44*(H*chunks J M))+(Layout.billed H (J*11) (M*11)+C.scaling.steps T.z)) ∧
      (path.ordinary ticket).Held C.out out ∧
      ∀addr,(addr<L.source.base ∨ L.source.base+H*chunks J M≤addr) →
        (addr<L.words ∨ C.out<addr) → out addr=m addr := by
  dsimp only
  let mid:=ProtocolRAM.image L.source.base (H*chunks J M) (lookup banks) m
  obtain ⟨lookupRun,read,frame⟩:=donor_emitted banks L.source.base positive fit donors m loaded
  have equal : (fun v (j : Fin (J*11))=>report hostBits groupBits slots
      (donors v (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2)=ticket.issuedPanel vertex :=
    funext fun v=>funext (records v)
  have ready : DescentPackedScore.Input (M:=M*11) L.source L.rom score (ticket.issuedPanel vertex) mid := by
    constructor
    · intro p
      have got := read p
      rw [equal] at got
      exact got
    · intro key
      apply (frame _ ?_).trans (table key)
      rcases tableApart with before|afterWord
      · exact .inl ((Nat.add_lt_add_left key.isLt _).trans_le before)
      · exact .inr (afterWord.trans (Nat.le_add_right _ _))
  have carried:=held.keep (frame _ (.inl keep))
  obtain ⟨fold,next⟩:=Path.Held.issued_panel path ticket vertex
    (fun e : Live source.placement (BitDescription.scannedRows he T).pick =>
      normalized_fits source.placement S source.valid ((BitDescription.scannedRows he T).profile c) e.val) L C mid carried room space
    (Nat.mul_pos positive (by decide)) rows bitsFit ready atEnd prior
  refine ⟨?_,next,?_⟩
  · intro P R C₀ mach pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then lookupRun fold mach pc reg pub exit rom advice cfg raw enter same
  · intro addr noLookup noCount
    exact (DescentPackedPrivateAccumulator.image_frame L C T.z mid room space atEnd addr noCount).trans
      (frame addr noLookup)

theorem Path.Held.donor_stage (hostBits groupBits slots : ℕ)
    (banks : DescentSIMDLookup.Banks) (L : Layout) (C : Counters)
    (donors : Fin H→Fin J→Donor loc names cellBits)
    (records : ∀v j,report hostBits groupBits slots
      (donors v (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2=ticket.issuedPanel vertex v j)
    (m : Memory bw) (positive : 0<M) (held : path.Held C.prior m)
    (fit : Fits banks (bundleBits loc names cellBits) ((2+cellBits)*11) M H J bw L.source.base)
    (loaded : PinFrame (M:=M) banks (donorROM hostBits groupBits slots loc names cellBits)
      (fun v j=>packDonor (donors v j)) m)
    (table : ∀key : Cell ((2+cellBits)*(M*11)),m (L.rom.base+key.val)=
      (DescentPackedScore.chunkScore (M:=M*11) score key:Computability.VPVNP.BurstRAM.Word bw))
    (tableApart : L.rom.base+2^((2+cellBits)*(M*11))≤L.source.base ∨
      L.source.base+H*chunks J M≤L.rom.base)
    (keep : C.prior<L.source.base) (room : L.Room bw H (J*11) (M*11)) (space : C.scaling.Room bw)
    (rows : Layout.count H (J*11) (M*11)≤L.source.size) (bitsFit : L.rom.bits=(2+cellBits)*(M*11))
    (atEnd : C.words=L.starts+Layout.count H (J*11) (M*11)) (prior : C.prior<L.words) :
    ∃out,((DescentSIMDLookup.program banks L.source.base H J M bw).seq
      (DescentPackedPrivateAccumulator.program L C bw H (J*11) (M*11) T.z)).Exec m out
      ((4+44*(H*chunks J M))+(Layout.billed H (J*11) (M*11)+C.scaling.steps T.z)) ∧
      (path.ordinary ticket).Held C.out out := by
  obtain ⟨run,next,_⟩:=Path.Held.donor_stage_framed path ticket vertex hostBits groupBits slots
    banks L C donors records m positive held fit loaded table tableApart keep room space rows bitsFit atEnd prior
  exact ⟨_,run,next⟩

variable (previous base : ℕ)
local notation "inputBits" => bundleBits loc names cellBits
local notation "short" => 2+cellBits
local notation "full" => max inputBits (short*11)
local notation "m₀" => lanes bw full
local notation "bank" => DescentPackedDonorSpace.banks base H J m₀ inputBits
local notation "L₀" => DescentPackedDonorSpace.layout base H J m₀ inputBits short
local notation "C₀" => DescentPackedDonorSpace.counters previous base H J m₀ inputBits short

set_option maxHeartbeats 1000000 in
/-- All producer/consumer address and capacity obligations follow from a single
upper bound on the arena. The earlier genuine count stays at its original address. -/
theorem Path.Held.donor_arena (hostBits groupBits slots : ℕ)
    (donors : Fin H→Fin J→Donor loc names cellBits)
    (records : ∀v j,report hostBits groupBits slots
      (donors v (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2=ticket.issuedPanel vertex v j)
    (m : Memory bw) (held : path.Held previous m) (prev : previous≤base) (wide : 2*full≤bw)
    (fit : DescentPackedDonorSpace.endAt base H J m₀ inputBits short<2^bw)
    (loaded : PinFrame (M:=m₀) bank (donorROM hostBits groupBits slots loc names cellBits)
      (fun v j=>packDonor (donors v j)) m)
    (table : ∀key : Cell (short*(m₀*11)),m ((L₀).rom.base+key.val)=
      (DescentPackedScore.chunkScore (M:=m₀*11) score key:Computability.VPVNP.BurstRAM.Word bw)) :
    ∃out,((DescentSIMDLookup.program bank (L₀).source.base H J m₀ bw).seq
      (DescentPackedPrivateAccumulator.program L₀ C₀ bw H (J*11) (m₀*11) T.z)).Exec m out
      ((4+44*(H*chunks J m₀))+(Layout.billed H (J*11) (m₀*11)+(C₀).scaling.steps T.z)) ∧
      (path.ordinary ticket).Held (C₀).out out ∧
      ((4+44*(H*chunks J m₀))+(Layout.billed H (J*11) (m₀*11)+(C₀).scaling.steps T.z))*bw≤
        (21+(56+4*ProtocolRAMPortScale.bitWidth T.z))*bw+84*(H*bw+4*H*J*full) := by
  have hp:0<full := lt_of_lt_of_le (by positivity : 0< short*11) (Nat.le_max_right _ _)
  have hm:0< m₀ := (occupancy bw full hp wide).1
  have space : DescentPackedDonorSpace.Room previous base H J m₀ inputBits short bw :=
    DescentPackedDonorSpace.room prev hm (lanes_fit bw full) fit
  obtain ⟨out,run,next⟩:=Path.Held.donor_stage path ticket vertex hostBits groupBits slots bank L₀ C₀
    donors records m hm held space.resolver loaded table (.inr space.score) space.before
    space.reduce space.scale space.rows space.bits space.last space.earlier
  exact ⟨out,run,next,(donor_stage_tariff C₀ bw H J full short T.z hp (Nat.le_max_right _ _) wide).1⟩

set_option maxHeartbeats 1000000 in
/-- Starting with just the packed donor input column and earlier private count,
write the format-dependent tables, run the resolver, and advance the issued
register at the single arena's allocated output. Setup ticks are counted here. -/
theorem Path.Held.donor_setup_stage (hostBits groupBits slots : ℕ)
    (donors : Fin H→Fin J→Donor loc names cellBits)
    (records : ∀v j,report hostBits groupBits slots
      (donors v (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2=ticket.issuedPanel vertex v j)
    (m : Memory bw) (held : path.Held previous m) (prev : previous≤base) (wide : 2*full≤bw)
    (fit : DescentPackedDonorSpace.endAt base H J m₀ inputBits short<2^bw)
    (pins : ∀p : Row H J m₀,m ((bank).source.base+(row H J m₀ p).val)=
      (data (M:=m₀) (fun v j=>packDonor (donors v j)) p).val) :
    let init:=DescentPackedDonorTables.program bank (L₀).rom.base H J m₀ bw
      (donorROM hostBits groupBits slots loc names cellBits) score
    ∃out,(init.seq ((DescentSIMDLookup.program bank (L₀).source.base H J m₀ bw).seq
      (DescentPackedPrivateAccumulator.program L₀ C₀ bw H (J*11) (m₀*11) T.z))).Exec m out
      ((4+10*DescentPackedDonorTables.size bank (L₀).rom.base short m₀)+
        ((4+44*(H*chunks J m₀))+(Layout.billed H (J*11) (m₀*11)+(C₀).scaling.steps T.z))) ∧
      (path.ordinary ticket).Held (C₀).out out := by
  dsimp only
  have setup:=DescentPackedDonorTables.install bank (L₀).rom.base (donorROM hostBits groupBits slots loc names cellBits)
    score (fun v j=>packDonor (donors v j)) m (DescentPackedDonorTables.arena fit) pins
  obtain ⟨run,loaded,table,frame⟩:=setup
  have earlier : previous<(bank).mask.base := by
    exact (Nat.lt_succ_of_le prev).trans_le (Nat.le_add_right (base+1) _)
  obtain ⟨out,main,next,_⟩:=Path.Held.donor_arena path ticket vertex previous base hostBits groupBits slots
    donors records _ (held.keep (frame _ earlier)) prev wide fit loaded table
  refine ⟨out,?_,next⟩
  intro P R C₁ mach pc reg pub exit rom advice cfg raw enter same
  exact Procedure.Exec.then run main mach pc reg pub exit rom advice cfg raw enter same

end
end Hierarchy.DescentSixParty.Chronology

end OAI
