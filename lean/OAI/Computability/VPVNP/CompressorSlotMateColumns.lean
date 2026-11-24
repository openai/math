import OAI.Computability.VPVNP.CompressorSlotOutputLayout
import OAI.Computability.VPVNP.CompressorSlotIncidence

/-!
# The three remaining incidence permutations

After the base-target scan, invert its permutation and expand both directions
to all binary lanes. Each pass starts with the previous pass's physical memory.
The base mate, inverse, displacement and two actual mate columns coexist in
the final memory; older tables and the reserved width region are preserved.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots

open SlotLevel BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression IncidenceDirectory

variable {a l w : ℕ} (Y : State a l) (s : Shape) (h : Heads)

/-- Memory represents the next state's forward and inverse base matching, base displacements,
and both directions of actual port incidence in canonical port order. -/
structure Mates (m : Memory w) : Prop where
  forward : BaseForward Y (targetsHead s h) (shiftsHead s h) m
  baseIn : ∀ e, m (inverseBaseHead s h+(baseOrder Y e).val) = Fin.ofNat _ (baseOrder Y (Y.slots.base.target.symm e)).val
  actualOut : ∀ e, m (outHead s h+(actualOrder Y e).val) = Fin.ofNat _ (actualOrder Y (Y.slots.actualGraph.target e)).val
  actualIn : ∀ e, m (inHead s h+(actualOrder Y e).val) = Fin.ofNat _ (actualOrder Y (Y.slots.actualGraph.target.symm e)).val

/-- Reports for the base inverse scan followed by the two scans that lift the matching to every
residual lane. -/
structure MateReports (w : ℕ) where
  /-- Reports that invert the base-target permutation, giving the source base port at each
  incoming base port. -/
  baseIn : List (Report w)
  /-- Reports that expand the forward base matching and displacements into the outgoing
  actual-port mate column. -/
  actualOut : List (Report w)
  /-- Reports that expand the inverse base matching and source displacements into the incoming
  actual-port mate column. -/
  actualIn : List (Report w)

/-- Concatenate the base inverse, actual forward, and actual inverse reports in execution
order. -/
def MateReports.all (r : MateReports w) := r.baseIn++r.actualOut++r.actualIn

/-- Memory after replaying the base inverse and the two actual mate scans in sequence. -/
def MateReports.final (r : MateReports w) (m : Memory w) :=
  after (after (after m (eventLog r.baseIn)) (eventLog r.actualOut)) (eventLog r.actualIn)

/-- The three mate report lists arise from their native workers starting at cursor zero on
successive memory states. -/
def MateReports.Native (r : MateReports w) (s : Shape) (h : Heads) (m : Memory w) : Prop :=
  let m₁ := after m (eventLog r.baseIn)
  let m₂ := after m₁ (eventLog r.actualOut)
  runSegment ((template SlotScatter.visit 0).instantiate w (inverseBank s h w)).program 10 (some 0) m
      (List.replicate (baseArcs s) []) = some r.baseIn ∧
    runSegment ((template (SlotIncidencePass.visit false) 0).instantiate w (actualBank s h false w)).program 28
      (some 0) m₁ (List.replicate (actualCount s) []) = some r.actualOut ∧
    runSegment ((template (SlotIncidencePass.visit true) 0).instantiate w (actualBank s h true w)).program 28
      (some 0) m₂ (List.replicate (actualCount s) []) = some r.actualIn

/-- The base inverse scan returns the base port count and both lifted mate scans return the
actual port count. -/
def MateReports.Cursors (r : MateReports w) (s : Shape) : Prop :=
  endState (some 0) r.baseIn=some (Fin.ofNat _ (baseArcs s)) ∧
    endState (some 0) r.actualOut=some (Fin.ofNat _ (actualCount s)) ∧ endState (some 0) r.actualIn=some (Fin.ofNat _ (actualCount s))

/-- The three passes share and preserve the prior target and displacement
columns. Their total cost is linear in the numbers of base and actual ports. -/
theorem writeMates (m : Memory w) (base : BaseForward Y (targetsHead s h) (shiftsHead s h) m)
    (hB : Fintype.card Y.Base*2^a=baseArcs s) (hA : Fintype.card Y.Base*2^l*2^a=actualCount s)
    (hd : s.newDegree=2^a) (hl : s.lanes=2^l) (hdw : 2^a<2^w) (hlw : 2^l<2^w)
    (hfit : finish s h < 2^w) :
    ∃ r : MateReports w, r.Native s h m ∧ r.Cursors s ∧ Mates Y s h (r.final m) ∧
      (∀ addr, addr < inverseBaseHead s h ∨ widthHead s h ≤ addr → r.final m addr=m addr) ∧
      RAMBuckets.cost Report.probes r.all = 3*baseArcs s+8*actualCount s := by
  let p := inverseBank s h w
  let q := actualBank s h false w
  let t := actualBank s h true w
  have h₀ : targetsHead s h+baseArcs s=shiftsHead s h := rfl
  have h₁ : shiftsHead s h+baseArcs s=inverseBaseHead s h := rfl
  have h₂ : inverseBaseHead s h+baseArcs s=outHead s h := rfl
  have h₃ : outHead s h+actualCount s=inHead s h := rfl
  have h₄ : inHead s h+actualCount s=widthHead s h := rfl
  have h₅ : widthHead s h+actualCount s=finish s h := rfl
  have p0 : (p 0).val=targetsHead s h := Nat.mod_eq_of_lt (by omega : targetsHead s h < 2^w)
  have p1 : (p 1).val=inverseBaseHead s h := Nat.mod_eq_of_lt (by omega : inverseBaseHead s h < 2^w)
  have q0 : (q 0).val=2^a := (Nat.mod_eq_of_lt (hd ▸ hdw)).trans hd
  have q1 : (q 1).val=2^l := (Nat.mod_eq_of_lt (hl ▸ hlw)).trans hl
  have q2 : (q 2).val=targetsHead s h := p0
  have q3 : (q 3).val=shiftsHead s h := Nat.mod_eq_of_lt (by omega : shiftsHead s h < 2^w)
  have q4 : (q 4).val=outHead s h := Nat.mod_eq_of_lt (by omega : outHead s h < 2^w)
  have t2 : (t 2).val=inverseBaseHead s h := p1
  have t4 : (t 4).val=inHead s h := Nat.mod_eq_of_lt (by omega : inHead s h < 2^w)
  have regions : SlotScatter.Regions p (Fintype.card Y.Base*2^a) (Fintype.card Y.Base*2^a) :=
    ⟨by rw [p0,hB]; omega,by rw [p1,hB]; omega,Or.inl (by rw [p0,p1,hB]; omega)⟩
  obtain ⟨bs,hbr,cb,base₁,bi,fb,costB⟩ := scatterBaseIn Y m p (shiftsHead s h) regions (p0 ▸ base)
    (Or.inl (by rw [p1,hB]; omega))
  let m₁ := after m (eventLog bs)
  have base₁' : BaseForward Y (targetsHead s h) (shiftsHead s h) m₁ := p0 ▸ base₁
  obtain ⟨os,hor,co,hout,fo,costO⟩ := SlotIncidencePass.run false Y q m₁ q0 q1
    (by rw [q2,q4,hB]; omega) (by rw [q3,q4,hB]; omega) (by rw [q4,hA]; omega)
    (fun e ↦ by rw [q2]; exact base₁'.mate e) (fun e ↦ by rw [q3]; exact base₁'.displacement e)
  let m₂ := after m₁ (eventLog os)
  have bv e : m₂ ((t 2).val+(baseOrder Y e).val) = Fin.ofNat _ (baseOrder Y (Y.slots.base.target.symm e)).val := by
    have hi : (baseOrder Y e).val < baseArcs s := (baseOrder Y e).isLt.trans_le hB.le
    rw [t2]
    exact (fo (inverseBaseHead s h+(baseOrder Y e).val) (Or.inl (by rw [q4]; omega))).trans (p1 ▸ bi e)
  have sv e : m₂ ((t 3).val+(baseOrder Y e).val) = Fin.ofNat _ (bitWordFinEquiv l (Y.slots.displacement e)).val := by
    have hi : (baseOrder Y e).val < baseArcs s := (baseOrder Y e).isLt.trans_le hB.le
    change m₂ ((q 3).val+_) = _
    rw [q3]
    exact (fo (shiftsHead s h+(baseOrder Y e).val) (Or.inl (by rw [q4]; omega))).trans (base₁'.displacement e)
  obtain ⟨is',hir,ci,hinc,fi,costI⟩ := SlotIncidencePass.run true Y t m₂ q0 q1
    (by rw [t2,t4,hB]; omega) (by change (q 3).val+_ ≤ _; rw [q3,t4,hB]; omega) (by rw [t4,hA]; omega) bv sv
  let r : MateReports w := ⟨bs,os,is'⟩
  have prev (addr : ℕ) (ha : addr < outHead s h ∨ widthHead s h ≤ addr) : r.final m addr=m₁ addr :=
    (fi addr (by rw [t4,hA]; omega)).trans (fo addr (by rw [q4,hA]; omega))
  have hfinal : BaseForward Y (targetsHead s h) (shiftsHead s h) (r.final m) := by
    constructor
    · intro e; have he := (baseOrder Y e).isLt
      exact (prev _ (.inl (by omega))).trans (base₁'.mate e)
    · intro e; have he := (baseOrder Y e).isLt
      exact (prev _ (.inl (by omega))).trans (base₁'.displacement e)
  refine ⟨r, ⟨hB ▸ hbr,hA ▸ hor,hA ▸ hir⟩, ⟨hB ▸ cb,hA ▸ co,hA ▸ ci⟩, ⟨hfinal,?_,?_,?_⟩, ?_, ?_⟩
  · intro e; have he := (baseOrder Y e).isLt
    exact (prev _ (.inl (by omega))).trans (p1 ▸ bi e)
  · intro e; have he := (actualOrder Y e).isLt
    exact (fi _ (.inl (by rw [t4]; omega))).trans (q4 ▸ hout e)
  · intro e; exact t4 ▸ hinc e
  · intro addr ha
    exact (prev addr (by omega)).trans (fb addr (by rw [p1,hB]; omega))
  · change RAMBuckets.cost Report.probes ((bs++os)++is') = _
    rw [RAMBuckets.cost_append,RAMBuckets.cost_append,costB,costO,costI,hA,hB]; ring

end CompressorRecords.ShrinkSlots

end VPVNP
end Computability
end OAI
