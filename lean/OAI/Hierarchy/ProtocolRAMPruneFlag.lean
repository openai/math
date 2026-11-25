import OAI.Hierarchy.ProtocolRAMSumScoresCheap
import OAI.Hierarchy.ProtocolRAMPrune
import OAI.Hierarchy.ProtocolRAMHistogram

namespace OAI
/-! # Computing the keep bit from the physical endpoint and metric tables -/

noncomputable section
namespace Hierarchy.ProtocolRAM.PruneFlag
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open ProtocolRAMEmit TaggedPrune CorrectionFrame
open scoped Classical BigOperators Fin.CommRing
variable {W n h w k M den : ℕ} {b : Fin k → ℕ}

/-- Row-major triple columns of the actual common controller output. -/
def field (table : Bank) (j : Fin 3) : Expr :=
  .lookup table (.op .add (scale 3 .row) (.lit j.val))

theorem field_read (table : Bank) (j : Fin 3) (m : Memory W) (i : Fin n)
    (len : 3*n≤table.size) (room : 3*n<2^W) :
    (field table j).eval m (i.val:Word W) = m (table.base+3*i.val+j.val) := by
  have hj := j.isLt
  have hi := i.isLt
  have lt : 3*i.val+j.val<3*n := by omega
  simp only [field,Expr.eval,eval_scale,RowOp.opcode,BinaryOp.eval,Bank.read]
  have addr : ((3:ℕ):Word W)*(i.val:Word W)+(j.val:Word W)=((3*i.val+j.val:ℕ):Word W) := by simp
  rw [addr,Fin.val_cast_of_lt (lt.trans room),Nat.mod_eq_of_lt (lt.trans_le len),Nat.add_assoc]

def term (endpoints metrics layers : Bank) (maxCode : ℕ) : Expr :=
  .branch .eq (.lookup layers (field endpoints 0)) (.lookup layers (field endpoints 1))
    (.lit 0) (boundedMul maxCode (field metrics 1) (field metrics 2))

/-- The row cost depends only on the fixed numerator menu. -/
theorem term_work (endpoints metrics layers : Bank) (maxCode : ℕ) :
    (term endpoints metrics layers maxCode).work = 47+20*maxCode+9*maxCode*(maxCode+1) := by
  have fieldWork (table : Bank) (j : Fin 3) : (field table j).work=17 := rfl
  have scaleWork (t : ℕ) (x : Expr) : (scale t x).work=1+t*(x.work+1) := by
    induction t with
    | zero => simp [scale,Expr.work]
    | succ t ih => simp only [scale,Expr.work,ih,Nat.succ_mul]; omega
  have codeWork (t : ℕ) : (boundedMul t (field metrics 1) (field metrics 2)).work =
      1+20*t+9*t*(t+1) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [boundedMul,Expr.work,fieldWork,scaleWork,ih]
      ring
  simp only [term,Expr.work,fieldWork,codeWork]
  ring

theorem term_fits (endpoints metrics layers : Bank) (maxCode out : ℕ)
    (ep : endpoints.Fits W out) (mt : metrics.Fits W out) (layer : layers.Fits W out) :
    (term endpoints metrics layers maxCode).Fits W out := by
  have fieldOk (bank : Bank) (ok : bank.Fits W out) (j : Fin 3) : (field bank j).Fits W out :=
    ⟨ok,by simp [scale,Expr.Fits]⟩
  have scaled (m : ℕ) (x : Expr) (hx : x.Fits W out) : (scale m x).Fits W out := by
    induction m with
    | zero => trivial
    | succ m ih => exact ⟨hx,ih⟩
  have bounded (m : ℕ) (x c : Expr) (hx : x.Fits W out) (hc : c.Fits W out) :
      (boundedMul m x c).Fits W out := by
    induction m with
    | zero => trivial
    | succ m ih => exact ⟨hc,trivial,scaled _ x hx,ih⟩
  exact ⟨⟨layer,fieldOk _ ep 0⟩,⟨layer,fieldOk _ ep 1⟩,trivial,
    bounded _ _ _ (fieldOk _ mt 1) (fieldOk _ mt 2)⟩

def layerCode (D : Layout h w b) (s : ℕ) : ℕ :=
  if hs : s<D.last+1 then ((Fintype.equivFin (Location k)) (D.layer ⟨s,hs⟩)).val else 0

/-- The static site-to-layer table is independent of selectors. -/
def layerAdvice (D : Layout h w b) (layers : Bank) (m : Memory W) : Memory W :=
  fillSegment layers.base layers.size (fun a => (layerCode D (a-layers.base):Word W)) m

theorem read_layerAdvice (D : Layout h w b) (layers : Bank) (m : Memory W) (dst : ℕ)
    (rows : Fin n → Row) (s : ℕ) (address : s<layers.size)
    (fit : layers.size<2^W) (precedes : layers.base+layers.size≤dst) :
    layers.read (emitted dst rows (layerAdvice D layers m)) (s:Word W)=(layerCode D s:Word W) := by
  have below : layers.base+s<dst := by omega
  have inside : layers.base≤layers.base+s ∧ layers.base+s<layers.base+layers.size := by omega
  simp only [Bank.read,Fin.val_cast_of_lt (address.trans fit),Nat.mod_eq_of_lt address,emitted,
    layerAdvice,fillSegment,ite_eq_right (by omega : ¬(dst+6*n≤layers.base+s ∧ layers.base+s<dst+6*n+3*n)),
    ite_eq_right (by omega : ¬(dst+3*n≤layers.base+s ∧ layers.base+s<dst+3*n+3*n)),ite_eq_right (by omega : ¬(dst≤layers.base+s ∧ layers.base+s<dst+3*n)),
    ite_eq_left inside,Nat.add_sub_cancel_left]

def charge (D : Layout h w b) (r : Row) :=
  if layerCode D r.endpoint=layerCode D r.opposite then 0 else r.lengthCode*r.width

theorem sum_charge_le (D : Layout h w b) (rows : Fin n → Row) (maxCode maxWidth : ℕ)
    (codes : ∀ i,(rows i).lengthCode≤ maxCode) (widths : ∀ i,(rows i).width≤ maxWidth) :
    (∑ i, charge D (rows i)) ≤ n*(maxCode*maxWidth) := by
  calc
    _ ≤ ∑ _ : Fin n, maxCode*maxWidth := Finset.sum_le_sum fun i _ => by
      unfold charge
      split
      · exact Nat.zero_le _
      · exact Nat.mul_le_mul (codes i) (widths i)
    _ = _ := by simp

private theorem layer_fits (D : Layout h w b) (s : ℕ)
    (space : Fintype.card (Location k)<2^W) : layerCode D s<2^W := by
  unfold layerCode
  split
  · exact Fin.isLt _ |>.trans space
  · exact Nat.two_pow_pos _

/-- On each input row, endpoint words index the advised layer codes.
Only positive cross-layer widths contribute to the running total. -/
theorem reads (D : Layout h w b) (rows : Fin n → Row) (m : Memory W)
    (dst maxCode : ℕ) (endpoints metrics layers : Bank)
    (ep : endpoints.base=dst) (mt : metrics.base=dst+3*n)
    (es : 3*n≤endpoints.size) (ms : 3*n≤ metrics.size) (room : 3*n<2^W)
    (cap : maxCode<2^W) (codes : ∀i,(rows i).lengthCode≤ maxCode)
    (space : Fintype.card (Location k)<2^W)
    (advice : ∀ i, ∀ s ∈ [ (rows i).endpoint, (rows i).opposite ],
      layers.read (emitted dst rows m) (s:Word W)=(layerCode D s:Word W)) :
    SumScores.Reads (emitted dst rows m) (term endpoints metrics layers maxCode) (fun i=>charge D (rows i)) := by
  intro i
  let mem := emitted dst rows m
  let r := rows i
  have fields (j : Fin 3) :
      (field endpoints j).eval mem (i.val:Word W)=(r.field (endpointFields j):Word W) ∧
      (field metrics j).eval mem (i.val:Word W)=(r.field (metricFields j):Word W) := by
    rw [field_read endpoints j _ i es room,field_read metrics j _ i ms room,ep,mt]
    exact ⟨(emitted_read dst rows m i j).1,(emitted_read dst rows m i j).2.1⟩
  have e0 : (field endpoints 0).eval mem (i.val:Word W)=(r.endpoint:Word W) := (fields 0).1
  have e1 : (field endpoints 1).eval mem (i.val:Word W)=(r.opposite:Word W) := (fields 1).1
  have w1 : (field metrics 1).eval mem (i.val:Word W)=(r.width:Word W) := (fields 1).2
  have l2 : (field metrics 2).eval mem (i.val:Word W)=(r.lengthCode:Word W) := (fields 2).2
  have left : layers.read mem (r.endpoint:Word W)=(layerCode D r.endpoint:Word W) := advice i _ (by simp [r])
  have right : layers.read mem (r.opposite:Word W)=(layerCode D r.opposite:Word W) := advice i _ (by simp [r])
  have code : ((field metrics 2).eval mem (i.val:Word W)).val ≤ maxCode := by
    rw [l2,Fin.val_cast_of_lt ((codes i).trans_lt cap)]
    exact codes i
  have equal : ((layerCode D r.endpoint:Word W)=(layerCode D r.opposite:Word W)) ↔
      layerCode D r.endpoint=layerCode D r.opposite := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt (layer_fits _ _ space),Fin.val_cast_of_lt (layer_fits _ _ space)]
  change (term endpoints metrics layers maxCode).eval mem (i.val:Word W) = (charge D r:Word W)
  simp only [term,Expr.eval,e0,e1,left,right,Comparison.test,beq_iff_eq,equal,
    eval_boundedMul _ _ _ _ _ code cap,w1,l2,charge]
  split <;> simp_all [mul_comm]

private theorem charge_sum {D : Layout h w b} {rows : Fin n → Row} (G : Geometry D M den rows) :
    (∑ i, charge D (rows i)) =
      ∑ j ∈ G.links.cross, (rows (activeIndex rows j).val).lengthCode * G.links.bits j := by
  let f (i : Fin n) := charge D (rows i)
  have split := Fintype.sum_subtype_add_sum_subtype (fun i => 0<(rows i).width) f
  have inactive : (∑ a : {i // ¬0<(rows i).width}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have z : (rows i.val).width=0 := Nat.eq_zero_of_not_pos i.property
    simp [f,charge,z]
  rw [inactive,add_zero] at split
  change (∑ i, f i) = _
  rw [←split,TaggedPrune.Links.cross,Finset.sum_filter]
  rw [← (Fintype.equivFin (ActiveRows rows)).symm.sum_comp (fun i => f i.val)]
  apply Finset.sum_congr rfl
  intro j _
  let i := activeIndex rows j
  have le : (rows i.val).endpoint<D.last+1 := Nat.lt_succ_of_le (G.fits i).1
  have ri : (rows i.val).opposite<D.last+1 := Nat.lt_succ_of_le (G.fits i).2
  have test : (layerCode D (rows i.val).endpoint=layerCode D (rows i.val).opposite) ↔
      D.layer ⟨(rows i.val).endpoint,le⟩ = D.layer ⟨(rows i.val).opposite,ri⟩ := by
    simp only [layerCode,dite_eq_left le,dite_eq_left ri,Fin.val_inj,(Fintype.equivFin (Location k)).injective.eq_iff]
  change (if layerCode D (rows i.val).endpoint=layerCode D (rows i.val).opposite then 0 else _) =
    if D.layer (G.edge i).1.1 ≠ D.layer (G.edge i).1.2 then _ else _
  by_cases equal : layerCode D (rows i.val).endpoint=layerCode D (rows i.val).opposite
  · have core := (G.edge_layer_eq i).mpr (test.mp equal)
    simp only [ite_eq_left equal,ite_eq_right (not_not.mpr core)]
  · have core : D.layer (G.edge i).val.1≠D.layer (G.edge i).val.2 :=
      fun same=>equal (test.mpr ((G.edge_layer_eq i).mp same))
    change (if layerCode D (rows i.val).endpoint=layerCode D (rows i.val).opposite then 0 else _) =
      if D.layer (G.edge i).val.1≠D.layer (G.edge i).val.2 then _ else 0
    simp only [ite_eq_right equal,ite_eq_left core]
    rfl

/-- The word threshold is truncated below at zero, so a negative excess demand
accepts every term as required by the original pruning test. -/
theorem keep_iff {D : Layout h w b} {rows : Fin n → Row} (G : Geometry D M den rows)
    (ticks : ℕ) (hw : 0<w) (hd : 0<den) :
    G.links.Keep ticks ↔ 2*M*(∑ j,b j)*den - ticks*w*den ≤ ∑ i, charge D (rows i) := by
  rw [G.links.keep_iff_integer hw hd (fun j => (rows (activeIndex rows j).val).lengthCode) (fun _ => rfl),
    charge_sum G]
  omega

/-- The concrete output memory image of the scan. -/
def output (D : Layout h w b) (rows : Fin n → Row) (out bound : ℕ) (start : Memory W) : Memory W :=
  fillSegment out (n+1) (SumScores.word out bound (fun i=>charge D (rows i))) start

theorem output_below (D : Layout h w b) (rows : Fin n → Row) (out bound : ℕ) (start : Memory W)
    {a : ℕ} (below : a<out) : output D rows out bound start a=start a := by
  simp [output,fillSegment,not_le.mpr below]

/-- Native execution on the actual emitted endpoint/metric tables, and exact
readback of the keep bit. All three fields are read by each selector's fixed
program, including on an empty padded board. -/
theorem run_exact {D : Layout h w b} {rows : Fin n → Row} (G : Geometry D M den rows)
    (m : Memory W) (dst maxCode out ticks : ℕ) (endpoints metrics layers : Bank)
    (hw : 0<w) (hd : 0<den)
    (ep : endpoints.base=dst) (mt : metrics.base=dst+3*n)
    (es : 3*n≤endpoints.size) (ms : 3*n≤ metrics.size) (inputRoom : 3*n<2^W)
    (cap : maxCode<2^W) (codes : ∀i,(rows i).lengthCode≤ maxCode)
    (space : Fintype.card (Location k)<2^W)
    (advice : ∀ i, ∀ s ∈ [(rows i).endpoint,(rows i).opposite],
      layers.read (emitted dst rows m) (s:Word W)=(layerCode D s:Word W))
    (fit : (term endpoints metrics layers maxCode).Fits W out) (room : out+(n+1)<2^W)
    (threshold : 2*M*(∑ j,b j)*den-ticks*w*den<2^W)
    (sumroom : (∑ i, charge D (rows i))<2^W) :
    let bound := 2*M*(∑ j,b j)*den-ticks*w*den
    let e := term endpoints metrics layers maxCode
    let result := output D rows out bound (emitted dst rows m)
    (SumScores.procedure W out n bound e).Exec (emitted dst rows m) result
      (4+(n+1)*(42+2*e.work)) ∧ result (out+n) = if G.links.Keep ticks then 1 else 0 := by
  let bound := 2*M*(∑ j,b j)*den-ticks*w*den
  let e := term endpoints metrics layers maxCode
  let q (i : Fin n) := charge D (rows i)
  let start := emitted dst rows m
  have score := reads D rows m dst maxCode endpoints metrics layers ep mt es ms inputRoom cap codes space advice
  have execution : (SumScores.procedure W out n bound e).Exec start
      (fillSegment out (n+1) (SumScores.word out bound q) start) (4+(n+1)*(42+2*e.work)) :=
    by
      have spec : (SumScores.procedure W out n bound e).Spec (fun a=>SumScores.Reads a e q)
          (fun a result=>result=fillSegment out (n+1) (SumScores.word out bound q) a) (4+(n+1)*(42+2*e.work)) :=
        SumScores.run out bound e q fit room threshold sumroom
      intro P R K machine pc reg pub exit instr data cfg mem entry same
      subst mem
      exact spec machine pc reg pub exit instr data cfg start entry score
  refine ⟨execution,?_⟩
  change fillSegment out (n+1) (SumScores.word out bound q) start (out+n)=_
  simp only [SumScores.read_flag,keep_iff G ticks hw hd,bound,q]

theorem flag_iff {D : Layout h w b} {rows : Fin n → Row} (G : Geometry D M den rows)
    (ticks out : ℕ) (after : Memory W) (room : out+(n+1)<2^W)
    (result : after (out+n) = if G.links.Keep ticks then 1 else 0) :
    (after (out+n)).val=1 ↔ G.links.Keep ticks := by
  have wide : 1<2^W := by omega
  have one : (1:Word W).val=1 := by change 1 % 2^W=1;exact Nat.mod_eq_of_lt wide
  by_cases h : G.links.Keep ticks
  · exact ⟨fun _=>h,fun _=>by rw [result,ite_eq_left h];exact one⟩
  · refine ⟨fun flag=>?_,fun keep=>False.elim (h keep)⟩
    rw [result,ite_eq_right h] at flag
    exact False.elim (Nat.zero_ne_one flag)

theorem run {D : Layout h w b} {rows : Fin n → Row} (G : Geometry D M den rows)
    (m : Memory W) (dst maxCode out ticks : ℕ) (endpoints metrics layers : Bank)
    (hw : 0<w) (hd : 0<den)
    (ep : endpoints.base=dst) (mt : metrics.base=dst+3*n)
    (es : 3*n≤endpoints.size) (ms : 3*n≤ metrics.size) (inputRoom : 3*n<2^W)
    (cap : maxCode<2^W) (codes : ∀i,(rows i).lengthCode≤ maxCode)
    (space : Fintype.card (Location k)<2^W)
    (advice : ∀ i, ∀ s ∈ [(rows i).endpoint,(rows i).opposite],
      layers.read (emitted dst rows m) (s:Word W)=(layerCode D s:Word W))
    (fit : (term endpoints metrics layers maxCode).Fits W out) (room : out+(n+1)<2^W)
    (threshold : 2*M*(∑ j,b j)*den-ticks*w*den<2^W)
    (sumroom : (∑ i, charge D (rows i))<2^W) :
    let bound := 2*M*(∑ j,b j)*den-ticks*w*den
    let e := term endpoints metrics layers maxCode
    ∃ after, (SumScores.procedure W out n bound e).Exec (emitted dst rows m) after
      (4+(n+1)*(42+2*e.work)) ∧ after (out+n) = if G.links.Keep ticks then 1 else 0 := by
  obtain ⟨exec,flag⟩ := run_exact G m dst maxCode out ticks endpoints metrics layers hw hd
    ep mt es ms inputRoom cap codes space advice fit room threshold sumroom
  exact ⟨_,exec,flag⟩

/-- Installing the fixed layer table before emission supplies the advice and
all row lookups using only bank capacities and the ordinary word bounds. -/
theorem run_mounted {D : Layout h w b} {rows : Fin n → Row} (G : Geometry D M den rows)
    (m : Memory W) (dst maxCode out ticks : ℕ) (endpoints metrics layers : Bank)
    (hw : 0<w) (hd : 0<den)
    (ep : endpoints.base=dst) (mt : metrics.base=dst+3*n)
    (es : 3*n≤endpoints.size) (ms : 3*n≤ metrics.size) (inputRoom : 3*n<2^W)
    (cap : maxCode<2^W) (codes : ∀i,(rows i).lengthCode≤ maxCode)
    (space : Fintype.card (Location k)<2^W) (before : layers.base+layers.size≤dst)
    (sites : ∀i,(rows i).endpoint<layers.size ∧ (rows i).opposite<layers.size)
    (ef : endpoints.Fits W out) (mf : metrics.Fits W out) (lf : layers.Fits W out)
    (room : out+(n+1)<2^W) (threshold : 2*M*(∑ j,b j)*den-ticks*w*den<2^W)
    (sumroom : (∑ i, charge D (rows i))<2^W) :
    let bound := 2*M*(∑ j,b j)*den-ticks*w*den
    let e := term endpoints metrics layers maxCode
    ∃ after, (SumScores.procedure W out n bound e).Exec
      (emitted dst rows (layerAdvice D layers m)) after (4+(n+1)*(42+2*e.work)) ∧
      after (out+n) = if G.links.Keep ticks then 1 else 0 := by
  refine run G (layerAdvice D layers m) dst maxCode out ticks endpoints metrics layers
    hw hd ep mt es ms inputRoom cap codes space ?_ (term_fits _ _ _ _ _ ef mf lf) room threshold sumroom
  intro i s hs
  refine read_layerAdvice D layers m dst rows s ?_ lf.2.1 before
  rcases List.mem_cons.mp hs with he | rem
  · simpa only [he] using (sites i).1
  · have he := List.mem_singleton.mp rem
    simpa only [he] using (sites i).2

end Hierarchy.ProtocolRAM.PruneFlag

end
end OAI
