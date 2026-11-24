import OAI.Computability.VPVNP.CompressionHistory
import OAI.Computability.VPVNP.CompressorRecordRefreshPrepareAllocation
import OAI.Computability.VPVNP.CompressorRecordRefreshAdmitted

/-!
# Native construction of a complete degree-refresh level

The sole data input is a represented old incidence directory. On each legal branch, the
program prepares both segment endpoints, reads the block demands, chooses admitted terms,
installs their supply widths and builds the next six incidence columns. All arrays use
the packed allocation, with a single end-address bound. The same final memory retains the
individual demands, selected grid rows, repetition counts and payload coordinates used by
the local history tests.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.Build

open BurstRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry MotifConversion
open NewSlots RefreshRAM Allocation

variable {bits a a₀ g dH t : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K')
  (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀) (choice : DyadicRefreshChoice X E hdH conn F)
  (ties : Fin t ≃ Tie (2^a)) (T : IncidenceDirectory bits) (start stride : ℕ)

local notation "P" => plan X a₀ dH t stride start
local notation "Q" => Plan.scratch P bits
local notation "Iₛ" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) E hdH conn F choice
local notation "Y" => dyadicRefreshNext X E hdH conn F hD hd choice
local notation "N" => Fintype.card X.Base * 2^a * 2^g
local notation "B" => Fintype.card X.Base * 2^g
local notation "S" => N*2^a
local notation "sourceBase" => word (bits := bits) (Plan.demand P)
local notation "termBase" => word (bits := bits) (Plan.term P)
local notation "demand" => blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
local notation "frame" => PrepareLayout X T a₀ dH t stride start

private theorem append_memory (m : Memory bits) (x y : List (Report bits)) :
    after m (eventLog (x++y)) = after (after m (eventLog x)) (eventLog y) := by
  change List.foldl BurstRAM.update m ((x++y).flatMap Report.events) = _
  rw [List.flatMap_append,List.foldl_append]; rfl

private theorem prepare_memory {q : Fin 8 → W bits} {base lanes : W bits} {fit : S ≤ 2^bits}
    {m m' : Memory bits} {rs : List (Report bits)} (run : PrepareRun X T q base ties lanes fit m m' rs) :
    m' = after m (eventLog rs) := by
  rcases run with ⟨rg,rd,re,ds,_,_,rfl,rfl⟩
  simp only [append_memory]

/-- One full execution, segmented at its preparation, term selection and output stages.
The term bits belong to the selected mathematical branch in physical block order. -/
def Run (cap : ℕ) (L : frame) (m : Memory bits) (rs : List (Report bits)) : Prop :=
  ∃ pre terms post,
    let m₁ := after m (eventLog pre)
    let m₂ := after m₁ (eventLog terms)
    rs = (pre ++ terms) ++ post ∧
    PrepareRun X T Q sourceBase ties (word (2^g)) L.regions.fits m m₁ pre ∧
    termRun E hdH conn F ties X sourceBase termBase stride cap (blockTapes E hdH conn F X choice bits) m₁ = some terms ∧
    Finish.Run X E hdH conn F hD hd choice termBase stride ((P).inputs bits) ((P).output bits) m₂ post

/-- All local input fields that the subsequent history traversal can read from this level. -/
structure Stored (fit : S ≤ 2^bits) (m : Memory bits) : Prop where
  segments : SegmentFields X Q fit m
  demands : ∀ s, DemandPreparation.demandAt ties (DemandScan.rowBase X t sourceBase s) m = demand s
  terms : SupplyScan.TermFields X E hdH conn F choice termBase stride m
  readback : ∀ s, TermRecordScan.Fields F finProdFinEquiv.symm (fun _ => zero_lt_one)
    (demand s) (choice s).val (SupplyScan.recordBase X termBase stride s) m

/-- The report count plus all RAM probes. Only the fixed expander ROM is independent of
the old graph's position and block counts. -/
noncomputable def charge : ℕ := 6*N + 12*S + 3*B*t + B*(1+TermRecordScan.probesPerRow F t (2^a*dH)) +
  (4*(N*dH) + 3*(2^a*dH) + ((6+7*dH+4*(2^a₀-(dH+1)))*X.positions + 5*BaseOutput.baseCount Y))

/-- A coefficient depending only on the fixed refresh motif and degrees. -/
noncomputable def chargeFactor (tiesCount : ℕ) := 6 + 12*2^a + 3*tiesCount +
  (1+TermRecordScan.probesPerRow F tiesCount (2^a*dH)) + 4*dH + 3*dH +
  (6+7*dH+4*(2^a₀-(dH+1))) + 5*2^a₀

/-- In particular, the actual phase reports have a uniform linear charge in the number
of positions, independently of the old or selected wire widths. -/
theorem charge_le_positions :
    charge (t := t) X E hdH conn F hD hd choice ≤ chargeFactor E hdH conn F t * X.positions := by
  have pos : N = X.positions := bundleCount_positions X (IncidenceDirectory.baseOrder X)
  have blocks : B ≤ N := by
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a))
  have ports : 2^a ≤ N := (Nat.le_mul_of_pos_left _ Fintype.card_pos).trans
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g))
  have sites : Fintype.card X.Base * 2^a ≤ N := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g)
  have baseCount : BaseOutput.baseCount Y = (Fintype.card X.Base * 2^a)*2^a₀ := by
    change Fintype.card (X.Base × Fin (2^a)) * _ = _
    simp only [Fintype.card_prod,Fintype.card_fin]
  have c₁ := Nat.mul_le_mul_right (3*t) blocks
  have c₂ := Nat.mul_le_mul_right (1+TermRecordScan.probesPerRow F t (2^a*dH)) blocks
  have c₃ := Nat.mul_le_mul_right (3*dH) ports
  have c₄ := Nat.mul_le_mul_right (5*2^a₀) sites
  unfold charge chargeFactor
  rw [baseCount,← pos]
  simp only [Nat.add_mul]
  linarith only [c₁,c₂,c₃,c₄]

private theorem bounds (nextWidth : (Y).maxWireWidth < 2^bits) :
    (∀ b, (∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) b j) < 2^bits) ∧
    (∀ (b : (X.Base × BitWord g) × Fin (2^a)) (i : Fin dH), Iₛ b.1 (b.2,i) < 2^bits) := by
  have h (b : (X.Base × BitWord g) × Fin (2^a)) (slot : RefreshSlot dH (2^a₀)) :=
    ((Y).width_le_maxWireWidth (refreshedCoordinates.symm (b, refreshSlots hd slot))).trans_lt nextWidth
  change ∀ b slot, newWidths hd _ Iₛ (refreshedCoordinates (refreshedCoordinates.symm _)).1
    (refreshedCoordinates (refreshedCoordinates.symm (b, refreshSlots hd slot))).2 < 2^bits at h
  simp only [Equiv.apply_symm_apply,newWidths,Equiv.symm_apply_apply] at h
  exact ⟨fun b => h b (.inl 0),fun b i => h b (.inr (.inl i))⟩

private theorem demand_bound (s : X.Base × BitWord g) (e : Tie (2^a)) : demand s e ≤ X.maxWireWidth := by
  unfold blockDemandWidths internalWidth
  split <;> exact X.width_le_maxWireWidth _

/-- The packed level produces the directory of the actual selected next state, retains
all fields needed by the local history, and writes only to its reserved interval. -/
theorem build (m : Memory bits) (old : T.Represents X m)
    (before : ∀ c : Fin 6, (T.column c).val + S ≤ start)
    (wide : 2+2^a*dH ≤ stride) (room : (P).stop < 2^bits)
    (termBits : termConstant E hdH conn F ties + 4*Nat.clog 2 (X.maxWireWidth+1) ≤ bits)
    (nextWidth : (Y).maxWireWidth < 2^bits)
    (cap : ℕ) (capFit : TermWorker.budget F t (2^a*dH) bits X.maxWireWidth ≤ cap) :
    let L := prepare_layout X T a₀ dH t stride start before room
    ∃ rs, Run X E hdH conn F hD hd choice ties T start stride cap L m rs ∧
      ((P).output bits).Represents Y (after m (eventLog rs)) ∧
      Stored X E hdH conn F choice ties start stride L.regions.fits (after m (eventLog rs)) ∧
      (∀ addr, addr < start ∨ (P).stop ≤ addr → after m (eventLog rs) addr = m addr) ∧
      RAMBuckets.cost Report.probes rs ≤ charge (t := t) X E hdH conn F hD hd choice := by
  let L := prepare_layout X T a₀ dH t stride start before room
  obtain ⟨external,internal⟩ := bounds X E hdH conn F hD hd choice nextWidth
  obtain ⟨pre,m₁,prun,seg₁,demands,preFrame,pcost⟩ :=
    prepare_demands X T Q sourceBase ties m old (word (2^g)) L.degree L.lanes L.regions L.directory L.gather
      L.baseApart external L.demandRoom L.demandApart
  have pm := prepare_memory X ties T prun
  obtain ⟨terms,trun,term₂,readback₂,termFrame,tcost,_⟩ := term_pass E hdH conn F ties X sourceBase termBase
    stride wide L.demandTerm L.termRoom m₁ X.maxWireWidth termBits (demand_bound X) demands cap capFit choice
  let m₂ := after m₁ (eventLog terms)
  change ∀ addr, addr < (termBase).val ∨ (termBase).val+B*stride ≤ addr → m₂ addr = m₁ addr at termFrame
  have h₀ : start+7*S = (P).demand := rfl
  have h₁ : (P).demand+B*t = (P).term := rfl
  have h₂ : (P).term+B*stride = (P).supply := rfl
  have h₃ : (P).supply ≤ (P).stop := by dsimp only [Plan.stop,Plan.next,Plan.reverseSlot,Plan.targetPort]; omega
  have w₁ : (sourceBase).val = (P).demand := Nat.mod_eq_of_lt (by omega)
  have w₂ : (termBase).val = (P).term := Nat.mod_eq_of_lt (by omega)
  have seg₂ : SegmentFields X Q L.regions.fits m₂ :=
    seg₁.transfer X Q fun c hc i hi => termFrame _ (Or.inl (by rw [w₂]; have := ((P).scratch_interval (by omega) c hc i hi).2; omega))
  obtain ⟨post,frun,next,seg₃,postFrame,fcost⟩ := Finish.finish X E hdH conn F hD hd choice Q termBase stride
    ((P).inputs bits) ((P).output bits) m₂ L.regions.fits seg₂ term₂
    (finish_layout X E hdH conn F hD hd choice t stride start wide room.le) internal
  let rs := (pre ++ terms) ++ post
  let m₃ := after m₂ (eventLog post)
  change ∀ addr, Finish.Outside X E hdH conn F hD hd choice termBase stride ((P).inputs bits) ((P).output bits) addr → m₃ addr = m₂ addr at postFrame
  have fm : after m (eventLog rs) = m₃ := by simp only [rs,m₃,m₂,pm,append_memory]
  have low (j : ℕ) (hj : j < (P).supply) : m₃ j = m₂ j :=
    postFrame j (outside_finish_of_lt_supply X E hdH conn F hD hd choice t stride start room.le j hj)
  have daddr (s : X.Base × BitWord g) (i : Fin t) : (DemandScan.rowBase X t sourceBase s).val + i.val < (P).term := by
    have h := Nat.mul_le_mul_right t (DemandScan.blocks X s).isLt
    rw [Nat.succ_mul] at h
    rw [DemandScan.rowBase,Fin.val_add,w₁]
    have hmod := Nat.mod_le ((DemandScan.blocks X s).val*t) (2^bits)
    have hmod' := Nat.mod_le ((P).demand + ((DemandScan.blocks X s).val*t) % (2^bits)) (2^bits)
    change ((P).demand + ((DemandScan.blocks X s).val*t) % (2^bits)) % (2^bits) + i.val < _
    have := i.isLt; omega
  have demand₃ (s) : DemandPreparation.demandAt ties (DemandScan.rowBase X t sourceBase s) m₃ = demand s := by
    funext e
    obtain ⟨i,rfl⟩ := ties.surjective e
    have h := DemandPreparation.demandAt_address ties (DemandScan.rowBase X t sourceBase s) m₃
      (DemandScan.rowBase_fits X sourceBase L.demandRoom s) i
    have h' := DemandPreparation.demandAt_address ties (DemandScan.rowBase X t sourceBase s) m₁
      (DemandScan.rowBase_fits X sourceBase L.demandRoom s) i
    have bound := daddr s i
    rw [h,low _ (by omega),termFrame _ (Or.inl (by rw [w₂]; exact bound)),← h',demands]
  have termAddr (s : X.Base × BitWord g) :
      (SupplyScan.recordBase X termBase stride s).val + stride ≤ (P).supply := by
    let i := (DemandScan.blocks X s).val
    have h := Nat.mul_le_mul_right stride (DemandScan.blocks X s).isLt
    rw [Nat.succ_mul] at h
    rw [SupplyScan.recordBase,← DemandScan.blocks_val,Fin.val_add,Fin.val_mul,w₂]
    change ((P).term + (((i % 2^bits) * (stride % 2^bits)) % 2^bits)) % 2^bits + stride ≤ _
    rw [Nat.mul_mod_mod,Nat.mod_mul_mod,Nat.add_mod_mod]
    have hr : (P).term + i*stride < 2^bits := by dsimp only [i]; omega
    rw [Nat.mod_eq_of_lt hr]
    dsimp only [i]; omega
  have fields₃ : SupplyScan.TermFields X E hdH conn F choice termBase stride m₃ := by
    refine ⟨term₂.fits,fun s => ?_,fun s e => ?_⟩
    · rw [low]; exact term₂.repetitions s
      have := termAddr s; omega
    · rw [low]; exact term₂.payload s e
      have h := Nat.mul_le_mul_right dH e.1.isLt
      rw [Nat.succ_mul] at h
      have := e.2.isLt; have := termAddr s; omega
  have stored : Stored X E hdH conn F choice ties start stride L.regions.fits m₃ := by
    refine ⟨seg₃,demand₃,fields₃,fun s => ?_⟩
    have h := termAddr s
    refine ⟨?_,?_,fun i => ?_⟩
    · rw [low _ (by omega)]; exact (readback₂ s).1
    · rw [low _ (by omega)]; exact (readback₂ s).2.1
    · rw [low _ (by have := i.isLt; omega)]; exact (readback₂ s).2.2 i
  refine ⟨rs,⟨pre,terms,post,rfl,pm ▸ prun,pm ▸ trun,pm ▸ frun⟩,fm ▸ next,fm ▸ stored,fun addr outside => ?_,?_⟩
  · rw [fm,postFrame _ (outside_finish_of_outside X E hdH conn F hD hd choice t stride start room.le _ outside)]
    rw [termFrame _ (by rw [w₂]; omega)]
    apply preFrame
    · intro c hc i hi
      have hh := (P).scratch_interval (by omega) c hc i hi
      change start ≤ _ ∧ _ < (P).demand at hh
      omega
    · rw [w₁]; omega
  · rw [show rs = (pre++terms)++post from rfl,RAMBuckets.cost_append,RAMBuckets.cost_append,pcost,fcost]
    unfold charge
    omega

end CompressorRecords.PortRefresh.Build

end VPVNP
end Computability
end OAI
