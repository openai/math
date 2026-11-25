import OAI.Hierarchy.TraceCompactArchive
import OAI.Hierarchy.TraceReceiverAge
import OAI.Hierarchy.TraceReceiverTemplateMount
import OAI.Hierarchy.TraceReceiverSelector
import OAI.Hierarchy.GridStructuralHeader
import OAI.Hierarchy.TraceSeedVisit

namespace OAI
/-! # Initializing the selected history visitor on the actual compact tick pin tape -/
namespace Hierarchy.TraceCompactSeed
open ThreeFlat Diagonal Diagonal.PhysicalStage NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure NavigationDirectory TraceAdmission TraceDistribution
open Filter
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base d fuel : ℕ}
variable (B : Block F) (axes n cap off rowSlots : ℕ) (M : Machine (64*w) pc regs slots)
    (fit : NativeTrace.Fits M S base d fuel) (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w))
    (raw gateBase : ℕ)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "G" => TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs slots d
local notation "ed" => GridStructuralHeader.directory (w:=w) B axes n cap
local notation "tc" => TraceReceiverTemplate.count G
local notation "libSize" => RAM.HistoryStageBody.Physical.libraryWords B W
local notation "total" => GridStructuralHeader.wordCount (ed).length tc libSize
local notation "text" => SelfAdvice.textSize W pc slots
local notation "phase" => GridStructuralHeader.receiverPhase w text total
local notation "beta" => GridStructuralHeader.recipientBase w
local notation "src" => 2+text+W*(1+(ed).length+tc)
local notation "params" => GridStructuralHeader.parameters B axes n cap M fit hF st raw gateBase
local notation "arch" => archive B w beta axes off rowSlots cap src phase
local notation "P" => B.repeat n
local notation "rem" => axes-(P).charge
local notation "ss" => (P).directory rem axes
local notation "edges" => (P).finalEdges rem axes

omit [Fintype F] in
theorem archive_placement (w β axes off slots cap rawStatic flag : ℕ) :
    ArchivePlacement (archive B w β axes off slots cap rawStatic flag) β w :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

variable (textFit : SelfAdvice.textSize (64*w) pc slots ≤ w^2) (self : Fin (w^2)→Bool)
    (index : Word (64*w)) (sel : Fin (cap+1)→Bool) {p : ℕ} (input : ℕ→Bool)
private abbrev mountedHeader : List Bool :=
  GridReceiverHeader.header (w:=w) (SelfAdvice.textSize (64*w) pc slots) textFit self index
    (GridStructuralHeader.parameters B axes n cap M fit hF st raw gateBase) sel
variable (padded : (mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length ≤ p)
    (stored : TraceFactorReceiver.Selector.headerReads (SelfAdvice.textSize (64*w) pc slots)
      textFit self index (GridStructuralHeader.parameters B axes n cap M fit hF st raw gateBase) sel input)
local notation "pins" => (fun j : Fin p => input j.val)
local notation "mem" => TickMountedPins.memory (w:=W) pins
local notation "bits" => GridStructuralHeader.selectorBit cap sel
local notation "td" => directory B w beta axes n cap phase

/-- The flag and the full body exactly exhaust the mounted header. -/
theorem selector_end : phase+1+cap=2+(mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length := by
  rw [mountedHeader,GridReceiverHeader.length]
  dsimp only [GridStructuralHeader.receiverPhase]
  omega

/-- A compact input with at most sixteen width scales of pin addresses fits completely
below S20 at the actual (rounded) receiver age. -/
theorem header_room (pinBound : p≤2^(16*w)) (headBound : (mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length ≤ p) :
    2+(mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length ≤ beta := by
  let age:=receiverAge w
  let step:=TickWorkspace.stride age
  have lo : 4*w ≤ age^10 := receiverAge_lower w
  have bank : 2^(16*w) ≤ step := by
    change 2^(16*w)≤(2^(age^10))^4
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have positive : 0<step := Nat.pow_pos (Nat.two_pow_pos _)
  change 2+(mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length≤21*step
  omega

include padded stored

/-- Decode the final directory block at its true offset after the E directory and the
verifier template. The header also contains the tick ordinal in its first word. -/
theorem directory_read (i : ℕ) (hi : i<(td).length) (j : Fin W) :
    mem (src+W*i+j.val)=(((((td)[i]?.getD 0:ℕ):Word W).val.testBit (W-1-j.val)).toNat : Word W) := by
  let h : Fin (ed).length:=⟨i,by rw [GridStructuralHeader.directory_length];simpa only [directory_length] using hi⟩
  let k : Fin total := Fin.natAdd (ed).length (Fin.natAdd tc (h.castAdd libSize))
  let b : Fin ((total+1)*W) := finProdFinEquiv (k.succ,j)
  have bound : text+b.val<(mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length := by
    rw [mountedHeader,GridReceiverHeader.length]
    have within : b.val < (total+1)*W := b.isLt
    omega
  let atBit : Fin p:=⟨text+b.val,bound.trans_le padded⟩
  have addr : src+W*i+j.val=2+atBit.val := by
    change _=2+(text+(j.val+W*((ed).length+(tc+i)+1)))
    ring
  rw [addr,TickMountedPins.memory_at]
  have read : input atBit.val=(((td)[i]?.getD 0:ℕ):Word W).val.testBit (W-1-j.val) := by
    change input (text+b.val)=_
    rw [stored ⟨text+b.val,bound⟩]
    refine (TraceReceiverTemplate.header_param (n:=total) text textFit self index params sel k j).trans ?_
    apply congrArg (fun value : Word W => value.val.testBit (W-1-j.val))
    refine (GridStructuralHeader.third B axes n cap M fit hF st raw gateBase h).trans ?_
    simp only [List.getElem?_eq_getElem hi,Option.getD_some,h]
  rw [read]
  cases ((((td)[i]?.getD 0:ℕ):Word W).val.testBit (W-1-j.val)) <;> rfl

/-- The selector lives on the same mounted tape as the two machine directories. -/
theorem selector_read (j : Fin (cap+1)) :
    mem (phase+j.val)=(sel j).toNat := by
  have got:=TraceFactorReceiver.Selector.word_at text textFit self index params sel input padded stored j
  simpa only [GridStructuralHeader.receiverPhase,TraceFactorReceiver.Selector.phase,
    TraceFactorReceiver.Selector.first,Nat.add_assoc] using got

/-- The public numeric layout and the actual mounted compact pin tape supply all inputs
read by the original stage seed writer, for either selector branch. -/
theorem sources (room : 2+(mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length ≤ beta) (seedRoom : beta<2^W)
    (short : (td).length≤(2^w)^4) (body : W*(arch).histWords ss ≤ cap)
    (words : ∀v∈(arch).directory ss edges W,v<2^W) :
    (arch).SeedSources ss edges [] [] bits mem := by
  have dirEq : (arch).directory ss edges W=td := archive_directory ..
  have size:=(GridReceiverHeader.length text textFit self index params sel)
  have directorySize : (td).length=(ed).length := by
    rw [directory_length,GridStructuralHeader.directory_length]
  have staticBound : src+W*(td).length ≤ beta := by
    rw [directorySize]
    apply le_trans _ room
    rw [mountedHeader,size]
    unfold GridStructuralHeader.wordCount
    ring_nf
    omega
  have packed : phase+(cap+1) ≤ beta := by
    apply le_trans _ room
    rw [mountedHeader,size]
    dsimp only [GridStructuralHeader.receiverPhase]
    omega
  apply TraceSeedWriter.sources (arch) ss edges src (phase+1) bits mem rfl rfl rfl rfl (by change phase<beta;omega) rfl rfl seedRoom
  · rwa [dirEq]
  · change phase+1+W*(arch).histWords ss ≤ beta;omega
  · rw [dirEq];change beta+(td).length ≤ beta+(2^w)^4;omega
  · exact words
  · rw [dirEq]
    intro i hi j hj
    exact directory_read B axes n cap M fit hF st raw gateBase textFit self index sel input padded stored i hi ⟨j,hj⟩
  · intro i hi
    have small : i<cap := by omega
    have rd:=selector_read B axes n cap M fit hF st raw gateBase textFit self index sel input padded stored (Fin.succ ⟨i,small⟩)
    simpa only [show phase+1+i=phase+(i+1) by omega,Fin.val_succ,
      GridStructuralHeader.selectorBit,dite_eq_left small] using rd

private theorem selected_sources {k : ℕ} (hk : 2 ≤ k+1) (ax : k+1=axes)
    (room : 2+(mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length ≤ beta) (body : W*(arch).histWords ss ≤ cap)
    (fitSeed : TraceSeedWriter.Fits (arch) ss edges n k W)
    (limits : (arch).TraceLimits (2^w) ((arch).control:Word W) ss edges (2^(3*w/5)))
    (term : (arch).TerminalRoom ss edges W) :
    (arch).SeedSources ss edges [] [] bits mem := by
  have seedBound : beta<2^W := (Nat.le_add_right beta (6*(2^w)^4)).trans_lt fitSeed.space.controlRoom
  have short : (td).length≤(2^w)^4 := by
    have hp:=limits.tables
    rw [archive_directory] at hp
    change beta+(td).length ≤ beta+(2^w)^4 at hp
    omega
  have hdr : ∀v∈(arch).directory ss edges W,v<2^W := by
    apply TraceSeedWriter.directory_fits (P) (arch) rem fitSeed.space ((arch).control:Word W) ss edges
      rfl (by change 0<axes;omega) limits rfl rfl
      (by change 2^axes<2^W;rw [←ax];exact fitSeed.lanes) fitSeed.degree fitSeed.denseGraph
    · change beta+4*(2^w)^4 ≤ beta+5*(2^w)^4;omega
    · exact term.bounds.capacity
    · exact (Nat.le_add_right ..).trans_lt term.bounds.prefix
    · exact (Nat.le_add_left ..).trans_lt term.bounds.prefix
  exact sources B axes n cap off rowSlots M fit hF st raw gateBase textFit self index sel input
    padded stored room seedBound short body hdr

/-- Execute the genuine seed scanner on the mounted compact pin tape. All data-dependent
stage records come from the selected body; the only shift in the public directory is the
recipient's actual archive location. The frame includes the entire input header. -/
theorem «initialize» {k : ℕ} (hk : 2 ≤ k+1) (ax : k+1=axes)
    (room : 2+(mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length ≤ beta) (body : W*(arch).histWords ss ≤ cap)
    (fitSeed : TraceSeedWriter.Fits (arch) ss edges n k W)
    (limits : (arch).TraceLimits (2^w) ((arch).control:Word W) ss edges (2^(3*w/5)))
    (term : (arch).TerminalRoom ss edges W)
    (time : (arch).bootTime ss edges W+(arch).seedTime+6≤2^(3*w/5)) :
    let result:=TraceSeedWriter.memory (arch) ss edges [] bits mem n
    (TraceSeedWriter.procedure (arch) ss edges n).Spec (fun m=>m=mem) (fun _ o=>o=result) (2^(3*w/5)) ∧
    (arch).Visit ss edges bits ((arch).control:Word W) [] (B.cursorState hk (w/2) off rowSlots) result ∧
    (result ((((arch).control+1:ℕ):Word W).val)).val=n ∧
    (arch).seedData.Reads (fun i=>(result i).val) ∧
    (arch).seedData.Footprint (fun i=>(arch).initialRecords ≤ i ∧ i<(arch).metadataEnd) (fun i=>(result i).val) ∧
    ∀i,i<beta ∨ beta+7*(2^w)^4 ≤ i → result i=mem i := by
  intro result
  have srcOk:=selected_sources B axes n cap off rowSlots M fit hF st raw gateBase textFit self index sel input
    padded stored hk ax room body fitSeed limits term
  obtain ⟨run,visit,clock,rows,foot,low⟩:=
    TraceSeedWriter.«initialize» B hk (arch) ss edges n rfl ax (by change 2^axes=2^(k+1);rw [ax])
      rfl rfl fitSeed bits mem srcOk
  refine ⟨?_,visit,clock,rows,foot,?_⟩
  · intro programCount registerCount wordCount machine
    exact Procedure.Spec.mono run (fun _ e => e) (fun _ _ e => e) time machine
  intro i hi
  rcases hi with lower|upper
  · exact low _ lower
  · apply TraceSeedWriter.memory_above (arch) ss edges bits mem n fitSeed.space fitSeed.mount srcOk i
    change beta+6*(2^w)^4+1 < i
    have size : 2≤(2^w)^4 := by
      have axesFit : k+1 ≤ 64*w := fitSeed.axes
      have positive : 0<w := by omega
      calc
        2 ≤ 2^w := by simpa using Nat.pow_le_pow_right (by decide : 0<2) positive
        _ ≤ (2^w)^4 := by simpa only [pow_one] using Nat.pow_le_pow_right (Nat.two_pow_pos w) (by decide : 1≤4)
    omega

/-- The unguarded five seed descriptor columns after executing native initialization,
including the actual lane and axis of every original seed site. -/
theorem initial_kernel {k : ℕ} (hk : 2 ≤ k+1) (ax : k+1=axes)
    (room : 2+(mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length ≤ beta) (body : W*(arch).histWords ss ≤ cap)
    (fitSeed : TraceSeedWriter.Fits (arch) ss edges n k W)
    (limits : (arch).TraceLimits (2^w) ((arch).control:Word W) ss edges (2^(3*w/5)))
    (term : (arch).TerminalRoom ss edges W) :
    let result:=TraceSeedWriter.memory (arch) ss edges [] bits mem n
    ∀ (j : Fin (arch).initialSites) (c : Fin 5),
      result ((arch).initialRecords+5*j.val+c.val)=
        ((![(arch).seed,j.val,0,j.val%(arch).remainingLanes,j.val/(arch).remainingLanes] : Fin 5→ℕ) c : Word W) := by
  intro result j c
  have srcOk:=selected_sources B axes n cap off rowSlots M fit hF st raw gateBase textFit self index sel input
    padded stored hk ax room body fitSeed limits term
  have ready:=TraceSeedWriter.ready (arch) ss edges B hk (w/2) off rowSlots rfl ax
    (by change 2^axes=2^(k+1);rw [ax]) rfl [] [] bits mem n fitSeed.space fitSeed.mount srcOk
    fitSeed.bits fitSeed.axes fitSeed.degree fitSeed.lanes fitSeed.word rfl fitSeed.clock
  have rd:=ready.nodes.kernel j c
  change result ((arch).initialRecords+(j.val*5+c.val))=_ at rd
  simpa only [Nat.add_assoc,Nat.mul_comm 5 j.val] using rd


end

noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- The exact aged workspace, including the largest retained arrays, is addressable in
the compact recipient's native word. This holds throughout the age interval. -/
theorem recipient_top {w v : ℕ} (hw : 1 ≤ w) (lower : 4*w ≤ v^10) (upper : v^10≤5*w) :
    TickWorkspace.base v 20+8*(2^w)^4<2^(64*w) := by
  let step:=TickWorkspace.stride v
  have slab : (2^w)^4 ≤ step := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (by omega : w ≤ v^10)) 4
  calc
    _ ≤ 32*step := by change 21*step+8*(2^w)^4≤32*step;omega
    _ = 2^(5+v^10*4) := by
      rw [pow_add, pow_mul]
      rfl
    _ < 2^(64*w) := Nat.pow_lt_pow_right (by decide) (by omega)

/-- Simultaneous resource certificate for the selected native T directory, counting all
bootstrap scans and retaining the original loop's chronological and terminal geometry. -/
theorem eventual_resources {u s : ℕ→ℕ} (scale : Scale u s) (a b : ℕ) :
    ∀ᶠ w : ℕ in Filter.atTop, ∀ (β k off rowSlots cap rawStatic flag : ℕ)
      (_charge : B.blockCharge*s w ≤ k+1) (_axes : k+1=u w+1-w/2)
      (_ports : off*rowSlots*3 ≤ a*(w+1)^b) (_small : flag+1+cap≤β) (_top : β+8*(2^w)^4<2^(64*w)),
      let A:=archive B w β (k+1) off rowSlots cap rawStatic flag
      let P:=B.repeat (s w)
      let rem:=k+1-P.charge
      let ss:=P.directory rem (k+1)
      let edges:=P.finalEdges rem (k+1)
      TraceSeedWriter.Fits A ss edges (s w) k (64*w) ∧
      A.TraceLimits (2^w) (A.control:Word (64*w)) ss edges (2^(3*w/5)) ∧
      A.TerminalRoom ss edges (64*w) ∧ A.bootTime ss edges (64*w)+A.seedTime+6≤2^(3*w/5) := by
  filter_upwards [TraceSeedWriter.eventual_fits B scale a b,TraceSeedWriter.eventual_seed_time B scale,
    eventual_iteration_limits B scale,eventual_terminal_room_at B scale,Filter.eventually_ge_atTop 1]
    with w seeds clocks limits terminal large
  intro β k off rowSlots cap rawStatic flag charge axes ports small top A P rem ss edges
  let base:=β
  have address:=archive_placement B w base (k+1) off rowSlots cap rawStatic flag
  have good:=seeds A base edges k off rowSlots charge axes rfl rfl rfl rfl ports rfl address top
  have ch : B.blockCharge*s w ≤ u w+1-w/2 := by simpa only [←axes] using charge
  have pointer : (A.control:Word (64*w)).val=A.control := Fin.val_cast_of_lt good.space.controlRoom
  have hist : A.oldHistory+A.pairCapacity ≤ base := small
  have control : A.phase ≤ base := by change flag≤β;omega
  refine ⟨good,?_,?_,?_⟩
  · simpa only [ss,rem,P,←axes] using limits ch A base edges (A.control:Word (64*w)) rfl address pointer
  · simpa only [ss,rem,edges,P,←axes] using (terminal ch A base address rfl top control hist hist).2
  · have archiveAxes : A.axes = k+1 := rfl
    simpa only [ss,rem,P,archiveAxes] using clocks A edges ch rfl axes rfl rfl rfl


end
end Hierarchy.TraceCompactSeed

end OAI
