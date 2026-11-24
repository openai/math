import OAI.Computability.VPVNP.CompressorRecordRefreshPrepare
import OAI.Computability.VPVNP.CompressorRecordRefreshSupplyScan
import OAI.Computability.VPVNP.CompressorTermWorkerScan

/-!
# The native term choices of a degree refresh

Each port block's dense demand vector is read from its generated record. A single native
call at the block ordinal selects a fixed grid row, computes the repetition count and checks the admitted
supply payload. The successful bit streams biject with the actual branch choices of the
refresh. The width threshold is fixed before the number of blocks or the old widths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry MotifConversion
open NewSlots RefreshRAM
open scoped Fin.CommRing

variable {a a₀ g dH t bits : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH) (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K') (ties : Fin t ≃ Tie (2^a))

private theorem massPos (e : Fin (2^a) × Fin dH) : 0 < expanderMass (2^a₀) e :=
  div_pos (Nat.cast_pos.mpr (Nat.two_pow_pos a)) (Nat.cast_pos.mpr (Nat.two_pow_pos a₀))

/-- A sufficient word-width constant for this fixed motif, independent of the old state
and the number of its port blocks. -/
noncomputable def termConstant := (TermWorker.scan_native F ties finProdFinEquiv.symm
  (fun _ => zero_lt_one) massPos).choose

variable (X : State a (a+g)) (q : Fin 8 → BurstRAM.Word bits)
  (demandBase termBase : BurstRAM.Word bits) (stride : ℕ)

local notation "B" => Fintype.card X.Base * 2^g
local notation "D" => 2^a
local notation "S" => Fintype.card X.Base * D * 2^g * D
local notation "demand" => blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X)

/-- Tightly packed input rows and arbitrarily strided output records, both in block order. -/
def termRows (wide : 2+D*dH ≤ stride) (sep : demandBase.val+B*t ≤ termBase.val)
    (room : termBase.val+B*stride < 2^bits) :=
  TermRecordScan.strided B t (D*dH) bits demandBase.val termBase.val t stride le_rfl wide sep room

variable (wide : 2+2^a*dH ≤ stride) (sep : demandBase.val + Fintype.card X.Base * 2^g * t ≤ termBase.val)
  (room : termBase.val + Fintype.card X.Base * 2^g * stride < 2^bits)
local notation "L" => termRows X demandBase termBase stride wide sep room

private theorem termRows_source (s : X.Base × BitWord g) : (L).source (DemandScan.blocks X s) =
    DemandScan.rowBase X t demandBase s := by
  apply Fin.ext
  change (demandBase.val + (DemandScan.blocks X s).val * t) % _ =
    (demandBase + word ((DemandScan.blocks X s).val * t)).val
  rw [Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]

private theorem termRows_base (s : X.Base × BitWord g) : (L).base (DemandScan.blocks X s) =
    SupplyScan.recordBase X termBase stride s := by
  apply Fin.ext
  change (termBase.val + (DemandScan.blocks X s).val * stride) % _ =
    (termBase + word _ * word stride).val
  rw [DemandScan.blocks_val,Fin.val_add,Fin.val_mul,Fin.val_ofNat,Fin.val_ofNat,
    Nat.mul_mod_mod,Nat.mod_mul_mod,Nat.add_mod_mod]

/-- The supplied numerical rows are read by the exact term compiler. -/
private theorem termInputs (m : Memory bits)
    (prepared : ∀ s, DemandPreparation.demandAt ties (DemandScan.rowBase X t demandBase s) m = demand s) :
    TermRecordScan.Inputs ties L (fun i => demand ((DemandScan.blocks X).symm i)) m := by
  intro i
  obtain ⟨s,rfl⟩ := (DemandScan.blocks X).surjective i
  rw [termRows_source]
  simpa only [Equiv.symm_apply_apply] using prepared s

/-- The concrete choice stream supplied to the block's nondeterministic calls. -/
noncomputable def blockTapes (choice : DyadicRefreshChoice X E hdH conn F) (bits : ℕ) (i : Fin B) :=
  let s := (DemandScan.blocks X).symm i
  TermRecordScan.tape F finProdFinEquiv.symm (demand s) bits (choice s).val

/-- The admissible mathematical term families, reindexed in the native scan order. -/
noncomputable def blockChoicesEquiv : DyadicRefreshChoice X E hdH conn F ≃
    TermRecordScan.Choices F (fun i : Fin B => demand ((DemandScan.blocks X).symm i)) :=
  Equiv.piCongrLeft' (fun s => ↥(outerIndices F (demand s))) (DemandScan.blocks X)

/-- Four public address operands of the native term worker. -/
def termAddresses (t : ℕ) : Fin 4 → BurstRAM.Word bits := ![demandBase.val, t, termBase.val, stride]

/-- The same fixed native program serves every block ordinal. -/
noncomputable abbrev termRun (cap : ℕ) (tapes : Fin B → List Bool) (m : Memory bits) :=
  runSegment (TermWorker.program F ties finProdFinEquiv.symm (termAddresses demandBase termBase stride t)) cap
    (some 0) m (List.ofFn tapes)

local notation "run" => termRun E hdH conn F ties X demandBase termBase stride

include wide sep room in
/-- A successful complete native stream selects precisely one actual refresh branch,
including when the block needs zero copies and its term takes no bits. -/
theorem term_stream_iff (m : Memory bits) (M : ℕ)
    (bound : termConstant E hdH conn F ties + 4*Nat.clog 2 (M+1) ≤ bits)
    (hw : ∀ s e, demand s e ≤ M)
    (prepared : ∀ s, DemandPreparation.demandAt ties (DemandScan.rowBase X t demandBase s) m = demand s)
    (cap : ℕ) (hcap : TermWorker.budget F t (D*dH) bits M ≤ cap) (tapes : Fin B → List Bool) :
    (run cap tapes m).isSome ↔ ∃! choice : DyadicRefreshChoice X E hdH conn F,
      tapes = blockTapes E hdH conn F X choice bits := by
  let indexed := blockChoicesEquiv E hdH conn F X
  let d := fun i : Fin B => demand ((DemandScan.blocks X).symm i)
  have h := (TermWorker.scan_native F ties finProdFinEquiv.symm (fun _ => zero_lt_one) massPos).choose_spec
    B M bits bound L (termAddresses demandBase termBase stride t)
    (TermWorker.addresses_strided demandBase.val termBase.val t stride le_rfl wide sep room) d
    (fun i => hw _) m (termInputs ties X demandBase termBase stride wide sep room m prepared) cap hcap
  dsimp only at h
  rw [h.1]
  let P := fun c : TermRecordScan.Choices F d =>
    tapes = fun i => TermRecordScan.tape F finProdFinEquiv.symm (d i) bits (c i).val
  change (∃! c, P c) ↔ ∃! c, P (indexed c)
  constructor
  · rintro ⟨c,hc,uniq⟩
    refine ⟨indexed.symm c, by simpa using hc, fun j hj => indexed.injective ?_⟩
    simpa using uniq _ hj
  · rintro ⟨c,hc,uniq⟩
    refine ⟨indexed c,hc,fun j hj => ?_⟩
    have he := uniq (indexed.symm j) (by simpa using hj)
    simpa using congrArg indexed he

private theorem cost_reports (rs : List (Report bits)) : RAMBuckets.cost Report.probes rs =
    rs.length + countProbes (eventLog rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [RAMBuckets.cost,ih,List.length_cons]
    change 1 + countProbes r.events + (rs.length + countProbes (eventLog rs)) =
      rs.length + 1 + countProbes (r.events ++ eventLog rs)
    rw [DemandPreparation.probes_append]; omega

include wide sep room in
/-- Each selected branch produces its grid IDs, repetition words and payload coordinates
through native calls. Every term field survives the complete pass. -/
theorem term_pass (m : Memory bits) (M : ℕ)
    (bound : termConstant E hdH conn F ties + 4*Nat.clog 2 (M+1) ≤ bits)
    (hw : ∀ s e, demand s e ≤ M)
    (prepared : ∀ s, DemandPreparation.demandAt ties (DemandScan.rowBase X t demandBase s) m = demand s)
    (cap : ℕ) (hcap : TermWorker.budget F t (D*dH) bits M ≤ cap) (choice : DyadicRefreshChoice X E hdH conn F) :
    ∃ rs, run cap (blockTapes E hdH conn F X choice bits) m = some rs ∧
      SupplyScan.TermFields X E hdH conn F choice termBase stride (after m (eventLog rs)) ∧
      (∀ s, TermRecordScan.Fields F finProdFinEquiv.symm (fun _ => zero_lt_one)
        (demand s) (choice s).val (SupplyScan.recordBase X termBase stride s) (after m (eventLog rs))) ∧
      (∀ addr, (addr < termBase.val ∨ termBase.val + B * stride ≤ addr) → after m (eventLog rs) addr = m addr) ∧
      RAMBuckets.cost Report.probes rs ≤ B * (1 + TermRecordScan.probesPerRow F t (D*dH)) ∧
      (eventLog rs).length ≤ B * TermWorker.budget F t (D*dH) bits M := by
  let d := fun i : Fin B => demand ((DemandScan.blocks X).symm i)
  have h := (TermWorker.scan_native F ties finProdFinEquiv.symm (fun _ => zero_lt_one) massPos).choose_spec
    B M bits bound L (termAddresses demandBase termBase stride t)
    (TermWorker.addresses_strided demandBase.val termBase.val t stride le_rfl wide sep room) d
    (fun i => hw _) m (termInputs ties X demandBase termBase stride wide sep room m prepared) cap hcap
  dsimp only at h
  obtain ⟨rs,hr,fields,frame,_,nr,_,probes,steps⟩ := h.2 (blockChoicesEquiv E hdH conn F X choice)
  have hs (s) := fields (DemandScan.blocks X s)
  have hs' (s : X.Base × BitWord g) : TermRecordScan.Fields F finProdFinEquiv.symm (fun _ => zero_lt_one)
      (demand s) (choice s).val (SupplyScan.recordBase X termBase stride s) (after m (eventLog rs)) := by
    have hv := congrArg (fun b => (choice b).val) ((DemandScan.blocks X).symm_apply_apply s)
    simpa only [d, blockChoicesEquiv, Equiv.piCongrLeft'_apply,Equiv.symm_apply_apply,termRows_base,hv] using hs s
  have tf := SupplyScan.TermFields.ofValues X E hdH conn F choice termBase stride (after m (eventLog rs))
    (fun s => (termRows_base X demandBase termBase stride wide sep room s) ▸ (L).termFits (DemandScan.blocks X s))
    (fun s => (hs' s).2.1) (fun s => (hs' s).2.2)
  refine ⟨rs,hr,tf,hs',fun addr ha => frame addr (fun i => ?_),?_,steps⟩
  · change addr < ((L).base i).val ∨ ((L).base i).val + 2 + D*dH ≤ addr
    have hi := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hi
    have hb : ((L).base i).val = termBase.val + i.val*stride := Nat.mod_eq_of_lt (by omega)
    rw [hb]; omega
  · rw [cost_reports,nr,Nat.mul_add,Nat.mul_one]
    omega

end CompressorRecords.PortRefresh

end VPVNP
end Computability
end OAI
