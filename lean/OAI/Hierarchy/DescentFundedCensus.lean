import OAI.Hierarchy.DescentFundedCensusLayout
import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentPackedColumnBatch

namespace OAI
/-! # Physical charged-record columns for the pre-compaction reset actors -/
namespace Hierarchy.DescentFundedCensus
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

structure Operation (bits : ℕ) where
  left : ℕ
  right : ℕ
  apply : Cell left → Cell right → Cell bits
  empty : apply 0 0 = 0

def mask (b : ℕ) : Operation b :=
  ⟨1,b,fun has value => if has=0 then 0 else value,by simp⟩

structure Job (b : ℕ) extends Operation b where
  first : Expr
  second : Expr
  present : Expr

variable {s : Shape} (jobs : Fin s.jobs→Job s.bits)

def op (j : Fin (s.jobs+1)) : Operation s.bits :=
  Fin.lastCases (mask s.bits) (fun q => (jobs q).toOperation) j

@[simp] theorem op_cast (j : Fin s.jobs) : op jobs j.castSucc = (jobs j).toOperation := by simp [op]
@[simp] theorem op_mask : op jobs (Fin.last s.jobs) = mask s.bits := by simp [op]

def idx (j : Fin (s.jobs+1)) (v : Fin 2) : Fin s.pageCount := finProdFinEquiv (v,j)

def pages (i : Fin s.pageCount) : Page :=
  let p : Fin 2 × Fin (s.jobs+1) := finProdFinEquiv.symm i
  binary (op jobs p.2).apply s.lanes p.1

theorem page_at (j : Fin (s.jobs+1)) (v : Fin 2) :
    pages jobs (idx j v) = binary (op jobs j).apply s.lanes v := by
  let render (p : Fin 2 × Fin (s.jobs+1)) := binary (op jobs p.2).apply s.lanes p.1
  exact congrArg render (finProdFinEquiv.symm_apply_apply (v,j))

def tableAt (base : ℕ) (j : Fin (s.jobs+1)) : Tables := joined (pages jobs) s.width base (idx j)

def valueExpr (base : ℕ) (j : Fin s.jobs) : Expr :=
  (tableAt jobs base j.castSucc).read (jobs j).first (jobs j).second

def gated (base : ℕ) (j : Fin s.jobs) : Expr :=
  (tableAt jobs base (Fin.last s.jobs)).read (jobs j).present (valueExpr jobs base j)

def instruction (base i : ℕ) : Expr :=
  if h : i<s.jobs then gated jobs base ⟨i,h⟩ else .lit 0

def passes (base : ℕ) := DescentPackedFlowBatch.passes (s.out base) s.rows s.rows (instruction jobs base) 0 s.jobs
def program (w base : ℕ) := (mount (pages jobs) s.width w base).seq (ProtocolRAM.program w (passes jobs base))
def ticks (base : ℕ) := (4+10*(s.pageCount*2^s.width)) + clock (passes jobs base)
def memory {w : ℕ} (base : ℕ) (m : Memory w) := result (passes jobs base) (after (pages jobs) s.width base m)

structure Room (w base : ℕ) : Prop where
  role : ∀j,(jobs j).left + (jobs j).right ≤ s.broadcast
  maskWidth : 1+s.bits ≤ s.broadcast
  first : ∀j,(jobs j).first.Fits w base
  second : ∀j,(jobs j).second.Fits w base
  present : ∀j,(jobs j).present.Fits w base
  space : s.roof base < 2^w

namespace Room
variable {jobs} {w base : ℕ} (r : Room jobs w base)
include r
theorem size (j : Fin (s.jobs+1)) : (op jobs j).left+(op jobs j).right ≤ s.broadcast := by
  refine Fin.lastCases ?_ (fun q => ?_) j
  · simpa [mask] using r.maskWidth
  · simpa using r.role q

theorem page (p : Fin s.pageCount) : (pages jobs p).bits ≤ s.width := by
  let pair : Fin 2 × Fin (s.jobs+1) := finProdFinEquiv.symm p
  have eqn : p=idx pair.2 pair.1 := (finProdFinEquiv.apply_symm_apply p).symm
  rw [eqn,page_at]
  obtain ⟨h,y⟩:=pair
  fin_cases h
  · exact Nat.mul_le_mul_right _ ((Nat.le_add_right ..).trans (r.size y))
  · exact Nat.mul_le_mul_right _ (r.size y)

theorem fits (j : Fin (s.jobs+1)) {e f : Expr} (he : e.Fits w (s.out base)) (hf : f.Fits w (s.out base)) :
    Fits (tableAt jobs base j) e f (op jobs j).left (op jobs j).right s.lanes (s.out base) w := by
  have bound:=(s.output_room base).trans_lt r.space
  refine ⟨he,hf,bank_room _ _ _ _ _ (r.page _) le_rfl bound,bank_room _ _ _ _ _ (r.page _) le_rfl bound,?_,?_⟩
  · simp [tableAt,joined,bank,page_at,binary]
  · simp [tableAt,joined,bank,page_at,binary]

theorem valueFits (j : Fin s.jobs) : (valueExpr jobs base j).Fits w (s.out base) := by
  have pair:=r.fits j.castSucc (ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (r.first j))
    (ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (r.second j))
  exact ⟨pair.apply,pair.right,pair.shift,pair.left⟩

theorem gatedFits (j : Fin s.jobs) : (gated jobs base j).Fits w (s.out base) := by
  have pair:=r.fits (Fin.last s.jobs) (ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (r.present j)) (r.valueFits j)
  exact ⟨pair.apply,pair.right,pair.shift,pair.left⟩

end Room

theorem any {w base : ℕ} (r : Room jobs w base) (m : Memory w) :
    (program jobs w base).Exec m (memory jobs base m) (ticks jobs base) ∧ CheapCode (program jobs w base) ∧
      ∀a,a<base ∨ s.roof base≤a → memory jobs base m a=m a := by
  let dst:=after (pages jobs) s.width base m
  have bound:=(s.output_room base).trans_lt r.space
  have posted:=DescentOrdinaryAtomFieldRAM.ROM.run (pages jobs) s.width base m bound
  have fits (i : ℕ) (hi : i<s.jobs) : (instruction jobs base i).Fits w (s.out base) :=by
    simpa [instruction,hi] using r.gatedFits ⟨i,hi⟩
  obtain ⟨cpu,_,low⟩:=DescentPackedFlowBatch.execute (s.out base) s.rows s.rows s.jobs
    (instruction jobs base) dst fits ((s.padded base).trans_lt r.space) le_rfl
  refine ⟨?_,?_,?_⟩
  · intro P R K machine
    exact Procedure.Exec.then posted.1 (@cpu) machine
  · exact cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap (pages jobs) s.width w base)
      (ProtocolRAM.program_cheap w (passes jobs base))
  intro a l
  have stay:=DescentOrdinaryAtomFieldRAM.ROM.frame (pages jobs) s.width base m a
  rcases l with old|late
  · exact (low a (old.trans_le (Nat.le_add_right ..))).trans (stay (.inl old))
  · have tail:=DescentPackedFlowBatch.above (s.out base) s.rows s.rows (instruction jobs base) dst 0 s.jobs a le_rfl (by simpa [Shape.used] using (s.padded base).trans late)
    exact tail.trans (stay (.inr ((s.output_room base).trans late)))

structure Values where
  first (j : Fin s.jobs) : Fin s.hosts→Fin s.groups→Cell (jobs j).left
  second (j : Fin s.jobs) : Fin s.hosts→Fin s.groups→Cell (jobs j).right
  present (j : Fin s.jobs) : Fin s.hosts→Fin s.groups→Cell 1

def quantity (v : Values jobs) (j : Fin s.jobs) (h : Fin s.hosts) (g : Fin s.groups) : Cell s.bits :=
  (mask s.bits).apply (v.present j h g) ((jobs j).apply (v.first j h g) (v.second j h g))

structure Sources {w : ℕ} (v : Values jobs) (m : Memory w) : Prop where
  first : ∀j,Source (jobs j).first (v.first j) s.lanes m
  second : ∀j,Source (jobs j).second (v.second j) s.lanes m
  present : ∀j,Source (jobs j).present (v.present j) s.lanes m

/-- Every old-host and old-group chunk, including the final partial chunk, has its own physical
word in this atlas column. The preceding actor-presence chart gates all three funding rules. -/
theorem read {w base : ℕ} (r : Room jobs w base) (m : Memory w) (v : Values jobs) (src : Sources jobs v m)
    (j : Fin s.jobs) (p : Row s.hosts s.groups s.lanes) :
    memory jobs base m (s.column base j+(row _ _ _ p).val)=(data (quantity jobs v j) p).val := by
  let dst:=after (pages jobs) s.width base m
  have keep {k : ℕ} (e : Expr) (fit : e.Fits w base) (a : Fin s.hosts→Fin s.groups→Cell k)
      (earlier : Source e a s.lanes m) : Source e a s.lanes dst:=fun p=>
    (eval_below e _ m dst fit (fun i hi=>DescentOrdinaryAtomFieldRAM.ROM.frame _ _ _ _ _ (.inl hi))).trans (earlier p)
  have lookup (k : Fin (s.jobs+1)) {e f : Expr} (ef : e.Fits w (s.out base)) (ff : f.Fits w (s.out base))
      (a : Fin s.hosts→Fin s.groups→Cell (op jobs k).left) (b : Fin s.hosts→Fin s.groups→Cell (op jobs k).right)
      (ae : Source e a s.lanes dst) (bf : Source f b s.lanes dst) :
      Source ((tableAt jobs base k).read e f) (fun h g=>(op jobs k).apply (a h g) (b h g)) s.lanes dst :=
    read_data _ _ _ _ (r.fits k ef ff) _ (op jobs k).empty dst
      (binary_mounted _ _ _ _ _ _ r.page (idx k) (page_at jobs k)) _ _ ae bf
  have liftFit {e : Expr} (h : e.Fits w base) : e.Fits w (s.out base):=
    ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) h
  have step (k : Fin s.jobs) : Source (valueExpr jobs base k)
      (fun h g=>(jobs k).apply (v.first k h g) (v.second k h g)) s.lanes dst := by
    have use:=lookup k.castSucc (liftFit (r.first k)) (liftFit (r.second k))
    rw [op_cast] at use
    exact use _ _ (keep _ (r.first k) _ (src.first k)) (keep _ (r.second k) _ (src.second k))
  have gatedSource : Source (gated jobs base j) (quantity jobs v j) s.lanes dst := by
    have use:=lookup (Fin.last s.jobs) (liftFit (r.present j)) (r.valueFits j)
    rw [op_mask] at use
    exact use _ _ (keep _ (r.present j) _ (src.present j)) (step j)
  have fits (i : ℕ) (hi : i<s.jobs) : (instruction jobs base i).Fits w (s.out base):=by
    simpa [instruction,hi] using r.gatedFits ⟨i,hi⟩
  obtain ⟨_,rows,_⟩:=DescentPackedFlowBatch.execute (s.out base) s.rows s.rows s.jobs
    (instruction jobs base) dst fits ((s.padded base).trans_lt r.space) le_rfl
  exact (rows j (row _ _ _ p)).trans (by simpa [instruction,j.isLt] using gatedSource p)

end
end Hierarchy.DescentFundedCensus

end OAI
