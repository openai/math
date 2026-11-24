import OAI.Computability.VPVNP.CompressorSurvivingPass
import OAI.Computability.VPVNP.CompressorSurvivingVisit
import OAI.Computability.VPVNP.CompressorSurvivingReadback

/-!
# Chosen surviving intervals in one native shrinking step

The role programs read the same dense motif table but publish split widths
by absolute source arc. Their outputs also provide both endpoint directories
for every surviving role. The native reports retain the physical input and
output addresses for use by the online dispatcher.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep.SurvivingSweep

open BurstRAM Compression Compression.PackingData Allocation SurvivingNative
open ShrinkSliceArrays SliceSchedule MotifBlocks MotifGrid MotifConversion MotifDemandPadding ShrinkMotif

variable {w : ℕ}

/-- One stage of the native sweep satisfies the guarded calendar and can
be replayed across scheduler writes outside its input region. -/
theorem guarded {n A d : ℕ} {T : Allocation w n A} (fit : T.Fits) {width : Id n → ℕ} {t : Fin 4}
    {abs layout : Word w} {cap : ℕ} {initial : Memory w} {rs : List (Report w)}
    (run : SurvivingPass.RoleRun T width t (program T t abs layout) cap (SurvivingNative.Site T t abs layout) initial rs)
    (catalog : Schedule.Catalog d) (worker : Fin d) (ports : Schedule.Ports w) (pub : Fin (catalog worker).params → Word w)
    (apart : ∀ x, OrdinalRun.ControlCell (catalog worker).params ports x → ¬ writeRegion T t x)
    (active : Schedule.Ready catalog worker ports pub (Fin.ofNat _ (n*T.subdiv t)) initial) :
    Schedule.ValidTrace catalog worker ports pub (Fin.ofNat _ (n*T.subdiv t)) 0 initial rs ∧
      OrdinalRun.Preserved (catalog worker).params ports initial (after initial (eventLog rs)) ∧
      SourceTransport.Reads (readRegion T abs layout) (eventLog rs) ∧
      SourceTransport.Writes (writeRegion T t) (eventLog rs) := by
  obtain ⟨valid,frame⟩ := run.toSegment.validTrace catalog worker ports pub (count_fit T fit t)
    (fun r h m x hx => SourceTransport.after_outside m h.writes (apart x hx)) active
  exact ⟨valid,frame,run.toSegment.footprint (fun r h => ⟨h.reads,h.writes⟩)⟩

private theorem cost {rs : List (Report w)} (all : ∀ r ∈ rs, r.probes = 17) :
    RAMBuckets.cost Report.probes rs = 18*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [RAMBuckets.cost,all r List.mem_cons_self,ih (fun s hs => all s (List.mem_cons_of_mem r hs)),
      List.length_cons,Nat.mul_succ]; omega

variable {d c n N J nL : ℕ} {V H Tag L : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (cd : P.BundleNumbering) (site : Compression.Site V Tag L ≃ Fin n)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

local notation "M" => (n*d)*pieceCount d c
local notation "A" => Slots.oldBaseArcCount N J d c * nL
local notation "order" => ShrinkMotifOrder.number P cd site
local notation "arc" => Slots.oldArcIndex P vertices tags lanes

variable (T : Allocation w ((n*d)*pieceCount d c) (Slots.oldBaseArcCount N J d c * nL))
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable {K : Type*} [_root_.Field K] {factor : ℝ}
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (old : Arc V H Tag L d c → ℕ) (choice : ∀ m : P.Motif, P.ShrinkChoice cd old F m)
local notation "chosen" => selected P cd site T F old choice

/-- Decode the next incidence pass's absolute-arc width addresses in the
same memory as the dense interval records. -/
theorem sparse_widths (habs : T.absolute = absolute P cd site vertices tags lanes) (fit : T.Fits)
    (out : Memory w) (images : ∀ i, Image (T.row i) (chosen i) out)
    (m : P.Motif) (t : Fin 4) (j : Fin (T.subdiv t)) :
    (out (T.widthBase+((arc m.val).val*4+t.val)*T.stride+j.val)).val =
      splitWidth (P.termWidths F cd old choice m T.layout t) (T.subdiv t) j := by
  let i : Id M := (order m,t)
  obtain ⟨_,_,_,hd,hc⟩ := T.row_vals fit i
  have key : (T.absoluteKey i).val = (T.absolute i.1).val*4+i.2.val := by
    change i.2.val+4*(T.absolute i.1).val = _; omega
  have hpos : j.val < (T.row i).count.val := lt_of_lt_of_eq j.isLt hc.symm
  have read := (images i).widths ⟨j.val,hpos⟩
  rw [hd,widthStart,key,habs] at read
  simpa only [i,absolute,Function.Embedding.coeFn_mk,Equiv.symm_apply_apply,selected,splitWidth,hc] using read

/-- Native execution of the four fixed role visits, including the absolute
width rectangle used by the slot compiler. Every call performs four reads
and thirteen writes. With its call charge the total cost is exactly eighteen
times the number of motif subdivisions. -/
theorem graph (habs : T.absolute = absolute P cd site vertices tags lanes)
    (fit : T.Fits) (selectors : T.selectors.val = F.selectorBits) (bound : ∀ i, chosen i < 2^w)
    (abs layout : Word w) (absFit : abs.val+M ≤ 2^w)
    (absOutside : ∀ i (j : Fin M), (T.row i).Outside (abs.val+j.val))
    (layoutOutside : ∀ i, (T.row i).Outside layout.val)
    (cap : ℕ) (fuel : ops.length < cap) (initial : Memory w)
    (directory : ∀ j, (initial (abs.val+j.val)).val = (T.absolute j).val)
    (side : (initial layout.val).val = T.layout.toNat) (terms : Terms P cd site T F old choice initial) :
    ∃ out batches,
      SurvivingPass.Roles T chosen (fun t => program T t abs layout) (fun _ => cap)
        (fun t => SurvivingNative.Site T t abs layout) (List.finRange 4) initial out batches ∧
      Inputs T abs layout chosen out ∧ Terms P cd site T F old choice out ∧
      (∀ i, Image (T.row i) (chosen i) out) ∧
      (∀ (m : P.Motif) (t : Fin 4) (j : Fin (T.subdiv t)),
        (out (T.widthBase+((arc m.val).val*4+t.val)*T.stride+j.val)).val =
          splitWidth (P.termWidths F cd old choice m T.layout t) (T.subdiv t) j) ∧
      (∀ x, x < T.widthBase ∨ T.last ≤ x → out x = initial x) ∧
      batches.map List.length = List.ofFn (fun t => M*T.subdiv t) ∧
      batches.flatten.length = M*T.stride ∧ RAMBuckets.cost Report.probes batches.flatten = 18*(M*T.stride) := by
  have inputs : Inputs T abs layout chosen initial := by
    refine ⟨directory,side,fun i t => ?_⟩
    simpa only [Nat.add_assoc] using selected_width_word P cd site T F old choice fit selectors terms i t (bound (i,t))
  let ready (m : Memory w) := Inputs T abs layout chosen m ∧ Terms P cd site T F old choice m
  have keep (i : Id M) (m out : Memory w) (hm : ready m)
      (frame : ∀ x, (T.row i).Outside x → out x = m x) : ready out :=
    ⟨hm.1.keep fit i (absOutside i) (layoutOutside i) frame,
      keep_terms P cd site T F old choice fit i m out hm.2 frame⟩
  obtain ⟨out,batches,runs,next,images,frame,lengths⟩ := SurvivingPass.full fit ready keep
    (fun t i j m hm => one T fit abs layout absFit chosen t cap fuel i j m hm.1) initial ⟨inputs,terms⟩
  have stable (x : ℕ) (hx : x < T.widthBase ∨ T.last ≤ x) := frame x (fun i => T.rowOutside fit i x hx)
  have work := cost (rs := batches.flatten) (fun r hr => by
    obtain ⟨t,_,s⟩ := runs.sites hr
    exact s.probes)
  rw [runs.calls] at work
  exact ⟨out,batches,runs,next.1,next.2,images,
    sparse_widths P cd site vertices tags lanes T F old choice habs fit out images,
    stable,lengths,runs.calls,work⟩

end CompressorRecords.ShrinkSliceSweep.SurvivingSweep

end VPVNP
end Computability
end OAI
