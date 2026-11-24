import OAI.Computability.VPVNP.CompressorRefreshStageFrame
import OAI.Computability.VPVNP.CompressorRecordRefreshPrepareAllocation

/-!
# Scheduler frames for the refresh demand, supply and expander-ROM workers

These three passes read and write inside the packed refresh allocation.
A single tie pass preserves every previously completed demand cell. Supply
visits preserve the term records and advance the supply prefix. Each fixed
ROM row starts at its own edge ordinal and fills the two reverse-edge cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TermDataFrame

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.Refresh
open Compression.DegreeRefresh SpectralGeometry SourceTransport NewSlots Allocation
open scoped Fin.CommRing

open private src_eq dst_val halfSlot layout one_step saved_congr pack_lt
  from OAI.Computability.VPVNP.CompressorRecordRefreshDemandScan
open private physical_addresses finPair_val step from OAI.Computability.VPVNP.CompressorRecordRefreshSupplyScan
open private address value written from OAI.Computability.VPVNP.CompressorRecordRefreshExpanderROM
open private Plan.address_val from OAI.Computability.VPVNP.CompressorRecordRefreshAllocation

/-- Addresses from the refresh allocation's start inclusive to its stop exclusive. -/
def InArena (P : Plan) (addr : ℕ) := P.start ≤ addr ∧ addr < P.stop

/-- The two premises a concrete deterministic source supplies to the guarded
scheduler scan. Native entry is required only at the actual active ordinals. -/
structure Scan {w : ℕ} {Q : Type*} (P : Plan) (program : BurstRAM.Program w Q)
    (fuel first N : ℕ) (inv : ℕ → Memory w → Prop) (events : Memory w → W w → List (Event w)) : Prop where
  native : ∀ j, first ≤ j → j < N → ∀ m, execute program fuel (program.start (j : W w)) m [] =
    some ⟨events m (j : W w), some ((j : W w)+1)⟩
  step : ∀ j, first ≤ j → j < N → ∀ m, inv j m →
    inv (j+1) (after m (events m (j : W w))) ∧
    Reads (InArena P) (events m (j : W w)) ∧ Writes (InArena P) (events m (j : W w))

theorem Scan.run {w fuel first N : ℕ} {Q : Type*} {P : Plan} {program : BurstRAM.Program w Q}
    {inv : ℕ → Memory w → Prop} {events : Memory w → W w → List (Event w)}
    (scan : Scan P program fuel first N inv events) (first_le : first ≤ N) (m : Memory w)
    (rs : List (Report w)) (initial : inv first m)
    (run : runSegment program fuel (some (first : W w)) m (List.replicate (N-first) []) = some rs) :
    StageFrame.Scanned first N rs ∧ inv N (after m (eventLog rs)) ∧
      Reads (InArena P) (eventLog rs) ∧ Writes (InArena P) (eventLog rs) :=
  StageFrame.scan program fuel first N inv events _ _ scan.native scan.step first_le m rs initial run

private theorem ranges (P : Plan) : P.start ≤ P.demand ∧ P.demand ≤ P.term ∧ P.term ≤ P.supply ∧
    P.supply ≤ P.targetPort ∧ P.targetPort ≤ P.reverseSlot ∧ P.reverseSlot ≤ P.next ∧ P.next ≤ P.stop :=
  ⟨Nat.le_add_right .., Nat.le_add_right .., Nat.le_add_right .., Nat.le_add_right ..,
    Nat.le_add_right .., Nat.le_add_right .., Nat.le_add_right ..⟩

variable {a g t w : ℕ} (X : State a (a+g)) (a₀ dH stride start : ℕ)
local notation "P" => plan X a₀ dH t stride start
local notation "B" => Fintype.card X.Base * 2^g
local notation "sitesN" => Fintype.card X.Base * 2^a * 2^g
local notation "Q" => Plan.scratch P w

section Demand

variable (ties : Fin t ≃ Tie (2^a))
local notation "dBank" => DemandScan.words (r := 2^g) ties Q (word (Plan.demand P))

private theorem demand_ranges (room : (P).stop < 2^w) (k : Fin t) (j : Fin B) :
    start ≤ (DemandScan.src dBank k j).val ∧ (DemandScan.src dBank k j).val < (P).demand ∧
    (P).demand ≤ (DemandScan.dst dBank k j).val ∧ (DemandScan.dst dBank k j).val < (P).term := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩ := ranges P
  have segments : (P).segments ≤ (P).demand := by dsimp only [Plan.demand]; omega
  have fit : sitesN*2^a ≤ 2^w := by change (P).segments ≤ _; omega
  have lanes : 2^g < 2^w := by
    have h₁ : 2^g ≤ sitesN := Nat.le_mul_of_pos_left _ (Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos _))
    have h₂ : sitesN ≤ (P).segments := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    omega
  let s := (DemandScan.blocks X).symm j
  have hs := src_eq X ties Q (word (P).demand) fit lanes k s
  rw [(DemandScan.blocks X).apply_symm_apply j] at hs
  let z := idWord (sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)) fit (halfSlot X s (ties k))
  have hz : z.val < (P).segments := (numbered (sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)) _).isLt
  have src : start ≤ (DemandScan.src dBank k j).val ∧ (DemandScan.src dBank k j).val < (P).demand := by
    rw [hs]
    split <;> first | exact (P).scratch_interval (by omega) 1 (by decide) z hz |
      exact (P).scratch_interval (by omega) 7 (by decide) z hz
  have hv : (word (bits := w) (P).demand).val = (P).demand := Nat.mod_eq_of_lt (by omega)
  have hterm : (P).term = (P).demand+B*t := rfl
  have dst := dst_val X ties Q (word (P).demand) (by rw [hv]; omega) j k
  rw [hv] at dst
  have hkey := pack_lt j.isLt k.isLt
  exact ⟨src.1,src.2,by omega,by omega⟩

/-- One tie's native scan and the exact prefix invariant for all earlier
ties and blocks. Its only read is from a segment column and its only store
lies in the dense demand array. -/
theorem demandScan (room : (P).stop < 2^w) (k : Fin t) (ref : Memory w)
    (done : Fin t → Fin B → Prop) :
    Scan P ((template DemandScan.visit 0).instantiate w (dBank k)).program 26 0 B
      (fun j m ↦ DemandScan.Saved dBank ref m (fun u i ↦ done u i ∨ u=k ∧ i.val<j))
      (DemandScan.events (dBank k)) := by
  have valid : DemandScan.Layout dBank B := by
    constructor
    · intro u v i j he
      have h := demand_ranges X a₀ dH stride start ties room u i
      have h' := demand_ranges X a₀ dH stride start ties room v j
      have eq := congrArg Fin.val he
      omega
    · intro u v i j he
      have hterm : (P).demand+B*t ≤ 2^w := by
        have h := ranges P; change (P).term ≤ _; omega
      have hv : (word (bits := w) (P).demand).val = (P).demand := Nat.mod_eq_of_lt (by have h := ranges P; omega)
      have h := congrArg Fin.val he
      rw [dst_val X ties Q (word (P).demand) (by rw [hv]; exact hterm) i u,
        dst_val X ties Q (word (P).demand) (by rw [hv]; exact hterm) j v] at h
      have hpair : i.val*t+u.val = j.val*t+v.val := by omega
      have eq := finProdFinEquiv.injective (show finProdFinEquiv (i,u) = finProdFinEquiv (j,v) from
        Fin.ext (by change u.val+t*i.val=v.val+t*j.val; simpa only [Nat.add_comm, Nat.mul_comm] using hpair))
      exact ⟨congrArg Prod.snd eq,congrArg Prod.fst eq⟩
  refine ⟨fun j _ _ m ↦ DemandScan.native (dBank k) m (j : W w), ?_⟩
  intro j _ hj m current
  let i : Fin B := ⟨j,hj⟩
  obtain ⟨hs,hs',ht,ht'⟩ := demand_ranges X a₀ dH stride start ties room k i
  have h := ranges P
  have r : InArena P (DemandScan.src dBank k i).val := ⟨hs,by omega⟩
  have v : InArena P (DemandScan.dst dBank k i).val := ⟨h.1.trans ht,by omega⟩
  refine ⟨saved_congr dBank ref (one_step dBank ref valid m current k i) ?_, ?_, ?_⟩
  · intro u l
    have hi : l=i ↔ l.val=j := Fin.ext_iff
    change (done u l ∨ u=k ∧ l.val<j) ∨ u=k ∧ l=i ↔ _
    rw [hi, show l.val<j+1 ↔ l.val<j ∨ l.val=j by omega]
    tauto
  · intro addr val read
    simp [DemandScan.events] at read
    exact read.1 ▸ r
  · intro addr val write
    simp [DemandScan.events] at write
    exact write.1 ▸ v

/-- Replay evidence for an actual tie stage, without any prepared scheduler
frame. Its input memory may contain the results of any earlier stages. -/
theorem demand_trace (room : (P).stop < 2^w) (k : Fin t) (m : Memory w) (rs : List (Report w))
    (run : runSegment ((template DemandScan.visit 0).instantiate w (dBank k)).program 26
      (some 0) m (List.replicate B []) = some rs) :
    StageFrame.Scanned 0 B rs ∧ Reads (InArena P) (eventLog rs) ∧ Writes (InArena P) (eventLog rs) := by
  let done : Fin t → Fin B → Prop := fun _ _ ↦ False
  have h := demandScan X a₀ dH stride start ties room k m done
  have initial : DemandScan.Saved dBank m m (fun u i ↦ done u i ∨ u=k ∧ i.val<0) :=
    ⟨fun _ _ h ↦ False.elim (by simp [done] at h),fun _ _ ↦ rfl⟩
  obtain ⟨shape,_,rd,wr⟩ := h.run (Nat.zero_le _) m rs initial (by simpa only [Nat.sub_zero,Nat.cast_zero] using run)
  exact ⟨shape,rd,wr⟩

end Demand

section Supply

variable {K : Type*} [_root_.Field K] {K₁ K₂ : ℝ}
  (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock K (expanderSupply E hdH conn) (2^a₀) K₁ K₂)
local notation "sBank" => SupplyScan.params (bits := w) (2^a) (2^g) dH (word (Plan.term P)) stride F.selectorBits
  (word (Plan.supply P))
local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)

private theorem supply_ranges (room : (P).stop < 2^w) (rowSize : 2+2^a*dH ≤ stride)
    (i : W w) (hi : i.val < sitesN*dH) :
    (P).term ≤ (SupplyScan.header sBank i+1).val ∧ (SupplyScan.header sBank i+1).val < (P).supply ∧
    (P).term ≤ (SupplyScan.payload sBank i).val ∧ (SupplyScan.payload sBank i).val < (P).supply ∧
    (P).supply ≤ (sBank 6+i).val ∧ (sBank 6+i).val < (P).targetPort := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩ := ranges P
  have upto : (P).targetPort = (P).supply + sitesN*dH := rfl
  have endTerm : (P).supply = (P).term + B*stride := rfl
  have hsites : 0 < sitesN := by positivity
  have siteFit : sitesN < 2^w := (Nat.le_mul_of_pos_right _ hdH).trans_lt (by omega)
  have vpos : 0 < Fintype.card X.Base := Fintype.card_pos
  have portsFit : 2^a < 2^w := ((Nat.le_mul_of_pos_left _ vpos).trans
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g))).trans_lt siteFit
  have laneFit : 2^g < 2^w := (Nat.le_mul_of_pos_left _ (Nat.mul_pos vpos (Nat.two_pow_pos a))).trans_lt siteFit
  have dims : SupplyScan.Fits (dH := dH) X w :=
    ⟨portsFit, laneFit, (Nat.le_mul_of_pos_left _ hsites).trans_lt (by omega), by omega⟩
  let pos := (finProdFinEquiv (m := sitesN) (n := dH)).symm ⟨i.val,hi⟩
  let s := (O).symm pos.1
  let k := pos.2
  let key := (DemandScan.blocks X s.1).val
  have hk : key < B := (DemandScan.blocks X s.1).isLt
  have endRow := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hk)
  rw [Nat.succ_mul] at endRow
  have bval : (SupplyScan.recordBase X (word (bits := w) (P).term) stride s.1).val =
      (P).term+key*stride := by
    dsimp only [key]
    rw [DemandScan.blocks_val]
    change (((P).term % 2^w + (((_ : ℕ) % 2^w)*(stride % 2^w)) % 2^w) % 2^w) = _
    rw [Nat.mod_mul_mod,Nat.mul_mod_mod,Nat.add_mod_mod,Nat.mod_add_mod]
    apply Nat.mod_eq_of_lt
    rw [← DemandScan.blocks_val]
    change (P).term+key*stride < 2^w
    omega
  have index : (O s).val*dH+k.val = i.val := by
    have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply (⟨i.val,hi⟩ : Fin (sitesN*dH)))
    rw [show (finProdFinEquiv pos).val = pos.1.val*dH+pos.2.val from finPair_val ..] at h
    simpa only [s,k,Equiv.apply_symm_apply] using h
  have eqw : word ((O s).val*dH+k.val) = i := by rw [index]; exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hrow : (SupplyScan.recordBase X (word (bits := w) (P).term) stride s.1).val+2+2^a*dH < 2^w := by
    rw [bval]; omega
  obtain ⟨hh,hp⟩ := physical_addresses X E hdH conn F (word (P).term) stride (word (P).supply) dims s k hrow
  rw [eqw,bval] at hh hp
  have hc := pack_lt s.2.isLt k.isLt
  have ho : (sBank 6+i).val = (P).supply+i.val :=
    Plan.address_val (len := sitesN*dH) (by omega) i hi
  rw [hh,hp,ho]
  constructor <;> omega

/-- The actual term-operand reads stay below the selected supply column.
Therefore later visits retain their source values while earlier output
rows stay intact. -/
theorem supplyScan (room : (P).stop < 2^w) (rowSize : 2+2^a*dH ≤ stride) (ref : Memory w) :
    Scan P ((template SupplyScan.visit 0).instantiate w sBank).program 34 0 (sitesN*dH)
      (fun j m ↦ SupplyScan.Prefix sBank ref m j) (SupplyScan.events sBank) := by
  have bounds := supply_ranges (t := t) X a₀ dH stride start E hdH conn F room rowSize
  have apart : SupplyScan.Apart sBank (sitesN*dH) := by
    intro i j hi hj
    have x := bounds i hi
    have y := bounds j hj
    constructor <;> omega
  refine ⟨fun j _ _ m ↦ SupplyScan.visit_native sBank m (j : W w), ?_⟩
  intro j _ hj m current
  let i := (j : W w)
  have upto : (P).targetPort = (P).supply+sitesN*dH := rfl
  have h := ranges P
  have hv : i.val = j := Nat.mod_eq_of_lt (by omega)
  have hi : i.val < sitesN*dH := hv ▸ hj
  obtain ⟨hh,hh',hp,hp',ho,ho'⟩ := bounds i hi
  have readH : InArena P (SupplyScan.header sBank i+1).val := ⟨by omega,by omega⟩
  have readP : InArena P (SupplyScan.payload sBank i).val := ⟨by omega,by omega⟩
  have writeO : InArena P (sBank 6+i).val := ⟨by omega,by omega⟩
  refine ⟨?_,?_,?_⟩
  · rw [SupplyScan.events_after]
    have next := step sBank ref m apart i hi (by rwa [hv])
    rwa [hv] at next
  · intro addr val read
    simp only [SupplyScan.events,List.mem_cons,List.not_mem_nil,Event.read.injEq,
      reduceCtorEq, false_or, or_false] at read
    rcases read with ⟨ha,_⟩ | ⟨ha,_⟩
    · exact ha ▸ readH
    · exact ha ▸ readP
  · intro addr val wr
    simp [SupplyScan.events] at wr
    exact wr.1 ▸ writeO

/-- Replay evidence for the whole dense supply column. -/
theorem supply_trace (room : (P).stop < 2^w) (rowSize : 2+2^a*dH ≤ stride)
    (m : Memory w) (rs : List (Report w))
    (run : runSegment ((template SupplyScan.visit 0).instantiate w sBank).program 34
      (some 0) m (List.replicate (sitesN*dH) []) = some rs) :
    StageFrame.Scanned 0 (sitesN*dH) rs ∧ Reads (InArena P) (eventLog rs) ∧ Writes (InArena P) (eventLog rs) := by
  have h := supplyScan (t := t) X a₀ dH stride start E hdH conn F room rowSize m
  have initial : SupplyScan.Prefix sBank m m 0 := ⟨fun _ hi ↦ False.elim (Nat.not_lt_zero _ hi),fun _ _ ↦ rfl⟩
  obtain ⟨shape,_,rd,wr⟩ := h.run (Nat.zero_le _) m rs initial (by simpa only [Nat.sub_zero,Nat.cast_zero] using run)
  exact ⟨shape,rd,wr⟩

end Supply

section ROM

variable (E : RegularArcGraph (Fin (2^a)) dH)
local notation "I" => Plan.inputs P w

/-- Publication of the two reverse-edge cells for one fixed ROM row. -/
theorem romScan (room : (P).stop < 2^w) (i : Fin (2^a*dH)) :
    let words := ExpanderROM.words E I i
    Scan P ((template ExpanderROM.put 0).instantiate w words).program 12 i.val (i.val+1)
      (fun j m ↦ j=i.val ∨ m ((P).targetPort+i.val) = word (E.reverse (finProdFinEquiv.symm i)).1.val ∧
        m ((P).reverseSlot+i.val) = word (E.reverse (finProdFinEquiv.symm i)).2.val)
      (fun _ _ ↦ ExpanderROM.events words) := by
  intro words
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩ := ranges P
  have headR : (P).targetPort+2^a*dH = (P).reverseSlot := rfl
  have headN : (P).reverseSlot+2^a*dH = (P).next := rfl
  have hp : (I).targetPort.val = (P).targetPort := Nat.mod_eq_of_lt (by omega)
  have hs : (I).reverseSlot.val = (P).reverseSlot := Nat.mod_eq_of_lt (by omega)
  have reg : ExpanderROM.Regions I (2^a*dH) := by
    constructor
    · rw [hp]; omega
    · rw [hs]; omega
    · exact Or.inl (by rw [hp,hs,headR])
  have hi : (word (bits := w) i.val).val = i.val := Nat.mod_eq_of_lt (by have := i.isLt; omega)
  have portVal : (words 3+words 0).val = (P).targetPort+i.val :=
    (Plan.address_val (len := 2^a*dH) (by omega) _ (hi ▸ i.isLt)).trans (congrArg (_+·) hi)
  have slotVal : (words 4+words 0).val = (P).reverseSlot+i.val :=
    (Plan.address_val (len := 2^a*dH) (by omega) _ (hi ▸ i.isLt)).trans (congrArg (_+·) hi)
  have hp' : InArena P (words 3+words 0).val := ⟨by rw [portVal]; omega,by rw [portVal]; have := i.isLt; omega⟩
  have hs' : InArena P (words 4+words 0).val := ⟨by rw [slotVal]; omega,by rw [slotVal]; have := i.isLt; omega⟩
  refine ⟨?_,?_⟩
  · intro j hlo hhi m
    have : j = i.val := by omega
    subst j
    exact ExpanderROM.native words _ m
  · intro j _ _ m _
    have hport := written E I reg i m true
    have hslot := written E I reg i m false
    change after m (ExpanderROM.events words) (words 3+words 0).val = _ at hport
    change after m (ExpanderROM.events words) (words 4+words 0).val = _ at hslot
    rw [portVal] at hport
    rw [slotVal] at hslot
    refine ⟨.inr ⟨hport,hslot⟩,?_,?_⟩
    · intro addr val read
      simp [ExpanderROM.events] at read
    · intro addr val wr
      simp [ExpanderROM.events] at wr
      rcases wr with ⟨ha,_⟩ | ⟨ha,_⟩
      · exact ha ▸ hp'
      · exact ha ▸ hs'

/-- The hardwired ROM stage has exactly one source report, even when its
initial edge ordinal is positive. -/
theorem rom_trace (room : (P).stop < 2^w) (i : Fin (2^a*dH)) (m : Memory w) :
    let rep := ExpanderROM.report E I i
    StageFrame.Scanned i.val (i.val+1) [rep] ∧ Reads (InArena P) (eventLog [rep]) ∧
      Writes (InArena P) (eventLog [rep]) := by
  intro rep
  let pub := ExpanderROM.words E I i
  let M := (template ExpanderROM.put 0).instantiate w pub
  have run : runSegment M.program 12 (some (i.val : W w)) m [[]] = some [rep] := by
    rw [runSegment,ExpanderROM.native]
    rfl
  obtain ⟨shape,_,rd,wr⟩ := (romScan (t := t) X a₀ dH stride start E room i).run
    (Nat.le_succ _) m [rep] (.inl rfl) (by rw [Nat.add_sub_cancel_left]; exact run)
  exact ⟨shape,rd,wr⟩

end ROM
end CompressorRecords.PortRefresh.TermDataFrame

end VPVNP
end Computability
end OAI
