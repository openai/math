import OAI.Computability.VPVNP.CompressorShrinkSliceSweep

/-!
# Complete surviving width and slice tables of one shrinking step

The dense CD order is the assigned bundle followed by the relative-key rank.
Every role of every chosen CD term runs once. The next slot directory can
read all surviving widths from the same final external memory by absolute
arc number and subdivision.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData
open ShrinkSliceArrays Allocation SliceSchedule MotifBlocks MotifGrid MotifConversion
open MotifDemandPadding ShrinkMotif

variable {w d c n N J nL : ℕ} {V H Tag L : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (cd : P.BundleNumbering) (site : Site V Tag L ≃ Fin n)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

local notation "M" => (n*d)*pieceCount d c
local notation "A" => Slots.oldBaseArcCount N J d c * nL
local notation "order" => ShrinkMotifOrder.number P cd site
local notation "arc" => Slots.oldArcIndex P vertices tags lanes

/-- Convert a dense motif ordinal into its absolute surviving-slot source
identifier. The native dense-to-absolute table stores this embedding. -/
def absolute : Fin M ↪ Fin A where
  toFun i := arc ((order).symm i).val
  inj' := (arc).injective.comp (Subtype.val_injective.comp (order).symm.injective)

variable (T : Allocation w ((n*d)*pieceCount d c) (Slots.oldBaseArcCount N J d c * nL))
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable {K : Type*} [_root_.Field K] {factor : ℝ}
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (old : Arc V H Tag L d c → ℕ)
variable (choice : ∀ m : P.Motif, P.ShrinkChoice cd old F m)

/-- Memory contains the chosen term fields at every dense motif record, with the motif's actual
two demand widths. -/
def Terms (mem : Memory w) : Prop :=
  ∀ i : Fin M, let m := (order).symm i
    TermRecordScan.Fields F supplyRoles demandMass_pos (P.shrinkDemandWidths cd old m)
      (choice m).val (Fin.ofNat _ (T.termStart i)) mem

/-- The surviving width of a particular dense motif and supply role for the stored term choice
and selected layout. -/
noncomputable def selected (i : Id M) : ℕ := P.termWidths F cd old choice ((order).symm i.1) T.layout i.2

private theorem term_val (fit : T.Fits) (i : Fin M) :
    (Fin.ofNat (2^w) (T.termStart i)).val = T.termStart i := (T.row_vals fit (i,0)).1

/-- A surviving-row write preserves every admitted term in the dense directory. -/
theorem keep_terms (fit : T.Fits) (i : Id M) (m out : Memory w)
    (ht : Terms P cd site T F old choice m) (frame : ∀ x, (T.row i).Outside x → out x = m x) :
    Terms P cd site T F old choice out := by
  intro j
  let base := Fin.ofNat (2^w) (T.termStart j)
  have hv : base.val = T.termStart j := term_val T fit j
  have keep (x : ℕ) (hx : x < base.val+10) : out x = m x := frame x (T.termOutside fit i j _ (hv ▸ hx))
  obtain ⟨g,u,v⟩ := ht j
  exact ⟨(keep base.val (by omega)) ▸ g,(keep (base.val+1) (by omega)) ▸ u,
    fun k => (keep (base.val+2+k.val) (by have := k.isLt; omega)) ▸ v k⟩

private theorem key_val (i : Id M) :
    (T.absoluteKey i).val = (T.absolute i.1).val*4+i.2.val := by
  change i.2.val + 4*(T.absolute i.1).val = _
  omega

private theorem row_worker (habs : T.absolute = absolute P cd site vertices tags lanes)
    (fit : T.Fits) (selector : T.selectors.val = F.selectorBits)
    (cap : ∀ m, outerCap F (P.shrinkDemandWidths cd old m) < 2^w)
    (bound : ∀ i, selected P cd site T F old choice i < 2^w)
    (i : Id M) (mem : Memory w) (ht : Terms P cd site T F old choice mem) :
    ∃ out rs, Run (T.row i) (selected P cd site T F old choice i) mem out rs := by
  let m := (order).symm i.1
  let r := T.row i
  let width := selected P cd site T F old choice i
  obtain ⟨hterm,_,_,hd,hc⟩ := T.row_vals fit i
  have eqw : survivingRowBase P vertices tags lanes T.widthBase T.subdiv m i.2 = T.widthStart i := by
    simp only [survivingRowBase,widthStart,key_val,habs,absolute,stride,m]
    rfl
  have hhead : (Fin.ofNat (2^w) (survivingRowBase P vertices tags lanes T.widthBase T.subdiv m i.2)) = r.dst :=
    Fin.ext (by rw [eqw,← hd]; exact Nat.mod_eq_of_lt r.dst.isLt)
  have hsub : (Fin.ofNat (2^w) (T.subdiv i.2)) = r.count := Fin.ext (by rw [← hc]; exact Nat.mod_eq_of_lt r.count.isLt)
  have hsel : (Fin.ofNat (2^w) F.selectorBits) = T.selectors := Fin.ext (by rw [← selector]; exact Nat.mod_eq_of_lt T.selectors.isLt)
  have htermFit : r.term.val+2+8 < 2^w := by
    have ht := T.term_stop fit i.1
    have h₁ : T.widthBase ≤ T.widthEnd := Nat.le_add_right ..
    have h₂ : T.widthEnd ≤ T.last := Nat.le_add_right ..
    have hf := fit.room
    rw [hterm]; omega
  have space : Workspace r.total r.dst r.bank 1 (T.subdiv i.2) := hc ▸ (T.space fit i)
  have sep := T.apart fit i
  rw [hd,hc,← eqw] at sep
  have stages := surviving_build P vertices tags lanes F cd old choice T.subdiv m T.layout i.2 mem
    r.term r.total r.bank T.widthBase htermFit (cap m) (ht i.1)
    (selector ▸ T.selectors.isLt) (bound i) (fit.positive i.2) (hc ▸ r.count.isLt)
    ((eqw.trans hd.symm) ▸ r.dst.isLt) (hhead ▸ space) sep
  dsimp only at stages
  rw [hhead,hsub,hsel] at stages
  obtain ⟨exec,htotal,s,ds,hs,hdsc,_⟩ := stages
  let call := supplyReport r.supply r.term mem
  let mid := after mem call.events
  let post := after mid (eventLog s)
  have eqn : List.ofFn (splitWidth width (T.subdiv i.2)) = List.ofFn (splitWidth width r.count.val) :=
    congrArg (fun q => List.ofFn (splitWidth width q)) hc.symm
  refine ⟨ds.result post,call :: (s++ds.all),⟨s,ds,exec,htotal,hs,?_,rfl,rfl⟩⟩
  exact eqn ▸ hdsc

/-- The linear dense order has one visit per surviving role, with the role
type varying fastest. -/
def schedule (n : ℕ) : List (Id n) := List.ofFn (fun i : Fin (n*4) => finProdFinEquiv.symm i)

/-- Construct all the chosen width rows and both directories on each row in
one shared memory. The count bound depends only on the fixed subdivisions. -/
theorem graph_run (habs : T.absolute = absolute P cd site vertices tags lanes)
    (fit : T.Fits) (selector : T.selectors.val = F.selectorBits)
    (cap : ∀ m, outerCap F (P.shrinkDemandWidths cd old m) < 2^w)
    (bound : ∀ i, selected P cd site T F old choice i < 2^w)
    (mem : Memory w) (input : Terms P cd site T F old choice mem) :
    ∃ out reports, Runs T.row (selected P cd site T F old choice) (schedule M) mem out reports ∧
      Terms P cd site T F old choice out ∧
      (∀ i, Image (T.row i) (selected P cd site T F old choice i) out) ∧
      (∀ (m : P.Motif) (t : Fin 4) (j : Fin (T.subdiv t)),
        (out (T.widthBase+((arc m.val).val*4+t.val)*T.stride+j.val)).val =
          splitWidth (P.termWidths F cd old choice m T.layout t) (T.subdiv t) j) ∧
      reports.length ≤ (M*4)*(5+5*T.stride) ∧
      (reports.map Report.probes).sum ≤ (M*4)*(10+21*T.stride) ∧
      (reports.map fun r => r.events.length+1).sum ≤ (M*4)*(54+112*T.stride) := by
  have nd : (schedule M).Nodup := List.nodup_ofFn_ofInjective finProdFinEquiv.symm.injective
  obtain ⟨out,rs,run,keep,all⟩ := scan (Terms P cd site T F old choice) (T.space fit) (T.apart fit)
    (T.separate fit) (keep_terms P cd site T F old choice fit)
    (row_worker P cd site vertices tags lanes T F old choice habs fit selector cap bound)
    (schedule M) mem input nd
  have images (i : Id M) := all i (List.mem_ofFn.mpr ⟨finProdFinEquiv i,finProdFinEquiv.symm_apply_apply _⟩)
  have hsub (t : Fin 4) : T.subdiv t ≤ T.stride :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (T.subdiv j)) (Finset.mem_univ t)
  have cost := run.cost (Q := T.stride) (fun i _ => (T.row_vals fit i).2.2.2.2 ▸ hsub i.2)
  refine ⟨out,rs,run,keep,images,?_,by simpa only [schedule,List.length_ofFn] using cost⟩
  intro m t j
  let i : Id M := (order m,t)
  obtain ⟨_,_,_,hd,hc⟩ := T.row_vals fit i
  have hpos : j.val < (T.row i).count.val := lt_of_lt_of_eq j.isLt hc.symm
  have hrow := (images i).widths ⟨j.val,hpos⟩
  change (out ((T.row i).dst.val+j.val)).val =
    splitWidth (selected P cd site T F old choice i) (T.row i).count.val ⟨j.val,hpos⟩ at hrow
  rw [hd,widthStart,key_val,habs] at hrow
  simpa only [i,absolute,Function.Embedding.coeFn_mk,Equiv.symm_apply_apply,selected,splitWidth,hc] using hrow

end CompressorRecords.ShrinkSliceSweep

end VPVNP
end Computability
end OAI
