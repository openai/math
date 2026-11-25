import OAI.Hierarchy.DescentDonorGroupedPrice
import OAI.Hierarchy.DescentIssuedDonorRegister

namespace OAI
/-! # A short payload controls both actual donor ROMs inside a larger address word -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentHostDegree DescentPackedPrivateSum DescentRawCablePanel DescentSIMDLookup
open Computability.VPVNP.BurstRAM
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
variable {H : ℕ} (vertex : source.V↪Fin H) (previous base payload : ℕ)

local notation "A" => source.placement
local notation "units" => normBits (A).cap G.b G.C G.k
local notation "J" => S.groupCount i*2^k*(A).cap
local notation "shelf" => 2^(packExponent 20 T.Δ)+2
local notation "gain" => gainExponent 20 T.Δ
local notation "names" => donorNameBits T.k T.Δ
local notation "inputBits" => bundleBits 3 names units
local notation "short" => 2+units
local notation "full" => max inputBits (short*11)
section Grouped
variable (laneCount : ℕ)
local notation "bank" => DescentPackedDonorSpace.banks base H J laneCount inputBits
local notation "L₀" => DescentPackedDonorSpace.layout base H J laneCount inputBits short
local notation "C₀" => DescentPackedDonorSpace.counters previous base H J laneCount inputBits short
local notation "pages" => DescentPackedDonorTables.size bank (L₀).rom.base short laneCount
local notation "ticks" => (4+10*pages)+((4+44*(H*chunks J laneCount))+(Layout.billed H (J*11) (laneCount*11)+(C₀).scaling.steps T.z))

theorem Path.Held.measured_donor_grouped (m : Memory bw)
    (held : path.Held previous m) (prev : previous≤base)
    (live : 0<laneCount) (packed : laneCount*full≤payload/2) (word : payload≤bw)
    (fit : DescentPackedDonorSpace.endAt base H J laneCount inputBits short<2^bw)
    (pins : ∀p : Row H J laneCount,m ((bank).source.base+(row H J laneCount p).val)=
      (data (M:=laneCount) (fun v j=>packDonor (ticket.measuredDonors vertex v j)) p).val) :
    let init:=DescentPackedDonorTables.program bank (L₀).rom.base H J laneCount bw (donorROM T.k gain shelf 3 names units) score
    let pre:=DescentPackedDonorTables.image bank (L₀).rom.base H J laneCount (donorROM T.k gain shelf 3 names units) score m
    let mid:=ProtocolRAM.image (L₀).source.base (H*chunks J laneCount) (lookup bank) pre
    let out:=DescentPackedPrivateAccumulator.image L₀ C₀ H (J*11) (laneCount*11) T.z mid
    (init.seq ((DescentSIMDLookup.program bank (L₀).source.base H J laneCount bw).seq
      (DescentPackedPrivateAccumulator.program L₀ C₀ bw H (J*11) (laneCount*11) T.z))).Exec m out ticks ∧
      (path.ordinary ticket).Held (C₀).out out ∧
      ticks≤131+4*ProtocolRAMPortScale.bitWidth T.z+124*(H*chunks J laneCount)+20*2^(payload/2) ∧
      DescentPackedDonorSpace.endAt base H J laneCount inputBits short≤base+8*(H*chunks J laneCount)+2*2^(payload/2)+11 ∧
      ∀addr,addr≤base ∨ DescentPackedDonorSpace.endAt base H J laneCount inputBits short≤addr → out addr=m addr := by
  dsimp only
  have fitCPU:=packed.trans (Nat.div_le_div_right word)
  have space:=DescentPackedDonorSpace.room prev live fitCPU fit
  obtain ⟨setup,loaded,table,frame⟩:=DescentPackedDonorTables.install bank (L₀).rom.base
    (donorROM T.k gain shelf 3 names units) score (fun v j=>packDonor (ticket.measuredDonors vertex v j))
    m (DescentPackedDonorTables.arena fit) pins
  have first : previous<(bank).mask.base := by
    change previous<base+1+_
    omega
  obtain ⟨main,next,kept⟩:=Path.Held.donor_stage_framed path ticket vertex T.k gain shelf bank L₀ C₀
    (ticket.measuredDonors vertex) (ticket.donor_words vertex) _ live (held.keep (frame _ first))
    space.resolver loaded table (.inr space.score) space.before space.reduce space.scale
    space.rows space.bits space.last space.earlier
  have clock:=DescentPackedDonorTables.grouped_price base payload H J inputBits short T.z laneCount C₀ live packed
  refine ⟨?_,next,clock,?_,?_⟩
  · intro P R C₁ mach pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then setup main mach pc reg pub exit rom advice cfg raw enter same
  · have memory:=DescentPackedDonorSpace.footprint base H J laneCount inputBits short live
    obtain ⟨firstPage,last⟩:=DescentPackedDonorTables.grouped_pages packed
    omega

  · intro addr away
    let endAddr:=DescentPackedDonorSpace.endAt base H J laneCount inputBits short
    have lastWord : (C₀).out+1=endAddr:=rfl
    have sourceEnd : (L₀).source.base+H*chunks J laneCount≤(L₀).rom.base:=space.score
    have tableEnd : (L₀).rom.base+2^(short*(laneCount*11))≤(L₀).words:=by
      have e:=space.reduce.rom.2.2
      simpa only [ProtocolRAM.Bank.size,space.bits] using e
    have ord:=space.reduce.sep
    have count:=space.last
    have active : (C₀).words<(C₀).scaled:=space.scale.active
    have temp : (C₀).scaled<(C₀).out:=space.scale.temp
    have atBase:=DescentPackedDonorSpace.room (prior:=base) le_rfl live fitCPU fit
    have inputStart:=atBase.before
    have wordsStart:=atBase.earlier
    have pageStart : base<(bank).mask.base := by change base<base+1+_; omega
    rcases away with low|high
    · exact (kept addr (.inl (low.trans_lt inputStart)) (.inl (low.trans_lt wordsStart))).trans
        (frame addr (low.trans_lt pageStart))
    · change endAddr≤addr at high
      have past : (C₀).out < addr := lt_of_lt_of_le (Nat.lt_succ_self _) (lastWord.le.trans high)
      have words : (L₀).words ≤ (C₀).words :=
        (Nat.le_add_right ..).trans (ord.trans ((Nat.le_add_right ..).trans count.symm.le))
      have tablePast : (L₀).rom.base+2^(short*(laneCount*11)) ≤ addr :=
        tableEnd.trans (words.trans (active.le.trans (temp.le.trans past.le)))
      have sourcePast : (L₀).source.base+H*chunks J laneCount ≤ addr :=
        sourceEnd.trans ((Nat.le_add_right ..).trans tablePast)
      apply (kept addr (.inr sourcePast) (.inr past)).trans
      have roomTables:=DescentPackedDonorTables.arena fit
      have onward:=roomTables.masks
      have dict:=roomTables.dictionary
      apply DescentStaticWordColumn.frame _ _ _ _ _ (.inr ?_)
      have maskLow : (bank).mask.base ≤ (bank).dictionary.base := (Nat.le_add_right ..).trans onward
      have dictLow : (bank).dictionary.base ≤ (L₀).rom.base := (Nat.le_add_right ..).trans dict
      exact (Nat.add_sub_of_le (maskLow.trans (dictLow.trans (Nat.le_add_right ..)))).le.trans tablePast

end Grouped

local notation "M" => lanes payload full
local notation "bank" => DescentPackedDonorSpace.banks base H J M inputBits
local notation "L₀" => DescentPackedDonorSpace.layout base H J M inputBits short
local notation "C₀" => DescentPackedDonorSpace.counters previous base H J M inputBits short
local notation "pages" => DescentPackedDonorTables.size bank (L₀).rom.base short M
local notation "ticks" => (4+10*pages)+((4+44*(H*chunks J M))+(Layout.billed H (J*11) (M*11)+(C₀).scaling.steps T.z))

theorem Path.Held.measured_donor_payload_framed (K : ℕ) (m : Memory bw)
    (held : path.Held previous m) (prev : previous≤base)
    (wide : 2*full≤payload) (word : payload≤bw) (overhead : bw≤K*payload)
    (fit : DescentPackedDonorSpace.endAt base H J M inputBits short<2^bw)
    (pins : ∀p : Row H J M,m ((bank).source.base+(row H J M p).val)=
      (data («M»:=M) (fun v j=>packDonor (ticket.measuredDonors vertex v j)) p).val) :
    let init:=DescentPackedDonorTables.program bank (L₀).rom.base H J M bw (donorROM T.k gain shelf 3 names units) score
    let pre:=DescentPackedDonorTables.image bank (L₀).rom.base H J M (donorROM T.k gain shelf 3 names units) score m
    let mid:=ProtocolRAM.image (L₀).source.base (H*chunks J M) (lookup bank) pre
    let out:=DescentPackedPrivateAccumulator.image L₀ C₀ H (J*11) (M*11) T.z mid
    (init.seq ((DescentSIMDLookup.program bank (L₀).source.base H J M bw).seq
      (DescentPackedPrivateAccumulator.program L₀ C₀ bw H (J*11) (M*11) T.z))).Exec m out ticks ∧
      (path.ordinary ticket).Held (C₀).out out ∧
      ticks*bw≤K*((131+4*ProtocolRAMPortScale.bitWidth T.z)*payload+
        124*(H*payload+4*H*J*full)+20*2^(payload/2)*payload) ∧
      DescentPackedDonorSpace.endAt base H J M inputBits short≤base+8*(H*chunks J M)+2*2^(payload/2)+11 ∧
      ∀addr,addr≤base ∨ DescentPackedDonorSpace.endAt base H J M inputBits short≤addr → out addr=m addr := by
  dsimp only
  have hp:0<full := lt_of_lt_of_le (by positivity : 0< short*11) (Nat.le_max_right _ _)
  have live:0<M := (occupancy payload full hp wide).1
  obtain ⟨run,next,_,memory,frame⟩:=Path.Held.measured_donor_grouped path ticket vertex
    previous base payload M m held prev live (lanes_fit ..) word fit pins
  have paid:=DescentPackedDonorTables.complete_price base payload H J inputBits short T.z C₀ hp wide
  refine ⟨run,next,?_,memory,frame⟩
  calc
    _ ≤ ticks*(K*payload) := Nat.mul_le_mul_left _ overhead
    _ = K*(ticks*payload) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ paid

theorem Path.Held.measured_donor_payload (K : ℕ) (m : Memory bw)
    (held : path.Held previous m) (prev : previous≤base)
    (wide : 2*full≤payload) (word : payload≤bw) (overhead : bw≤K*payload)
    (fit : DescentPackedDonorSpace.endAt base H J M inputBits short<2^bw)
    (pins : ∀p : Row H J M,m ((bank).source.base+(row H J M p).val)=
      (data («M»:=M) (fun v j=>packDonor (ticket.measuredDonors vertex v j)) p).val) :
    let init:=DescentPackedDonorTables.program bank (L₀).rom.base H J M bw (donorROM T.k gain shelf 3 names units) score
    ∃out,(init.seq ((DescentSIMDLookup.program bank (L₀).source.base H J M bw).seq
      (DescentPackedPrivateAccumulator.program L₀ C₀ bw H (J*11) (M*11) T.z))).Exec m out ticks ∧
      (path.ordinary ticket).Held (C₀).out out ∧
      ticks*bw≤K*((131+4*ProtocolRAMPortScale.bitWidth T.z)*payload+
        124*(H*payload+4*H*J*full)+20*2^(payload/2)*payload) ∧
      DescentPackedDonorSpace.endAt base H J M inputBits short≤base+8*(H*chunks J M)+2*2^(payload/2)+11 := by
  dsimp only
  obtain ⟨run,next,clock,space,_⟩:=Path.Held.measured_donor_payload_framed path ticket vertex
    previous base payload K m held prev wide word overhead fit pins
  exact ⟨_,run,next,clock,space⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
