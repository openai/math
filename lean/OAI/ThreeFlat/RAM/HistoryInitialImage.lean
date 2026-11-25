import OAI.ThreeFlat.RAM.HistoryInitialRetained
import OAI.ThreeFlat.RAM.HistoryNodeValue

namespace OAI
/-! # The seed's physical row, endpoint and six-word result readbacks -/

namespace ThreeFlat.RAM.HistoryInitialSeed
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalProcedure HistoryReadyTape
open scoped Fin.CommRing

noncomputable section
variable {W : ℕ}

/-- The private S12 row bank, following endpoint bank, S13 result slot, and
S18 seed are in increasing address order in the true tick workspace. -/
structure Separated (A : Layout) (z : Site) : Prop where
  rowEnds : z.stream A+4*z.rows A≤z.extBase A
  pairEnds : z.extBase A+z.extPins≤z.resultBase A
  nodeEnds : z.resultBase A+6≤A.ctrl

theorem Site.read_output (A : Layout) (z : Site) (record endpoint : ℕ→Word W)
    (src : Memory W) (small : A.ctrl<2^W) (sep : Separated A z) :
    let out := z.output A record endpoint src
    (∀ i : Fin (4*z.rows A),out (z.stream A+i.val)=record (z.stream A+i.val)) ∧
    (∀ i : Fin z.extPins,out (z.extBase A+i.val)=endpoint (z.extBase A+i.val)) ∧
    (∀ i : Fin 6,out (z.resultBase A+i.val)=((z.words A ⟨36+i.val,by omega⟩:ℕ):Word W)) := by
  have s1 := sep.rowEnds;have s2 := sep.pairEnds;have s3 := sep.nodeEnds
  dsimp only
  simp only [Site.output,jobs,HistoryReadyTape.after,HistoryJoinController.bumpMemory,writeMemory,fillSegment,
    Fin.val_cast_of_lt small]
  refine ⟨?_,?_,?_⟩
  · intro i
    have := i.isLt
    split_ifs <;> first | rfl | omega
  · intro i
    have := i.isLt
    split_ifs <;> first | rfl | omega
  · intro i
    have := i.isLt
    simp [show z.resultBase A+i.val≠A.ctrl by omega,show i.val<6 by omega]

/-- Readback at the exact physical root of the postorder forest, including
the six shape/operand fields that the next native stage actually reads. -/
theorem Site.read_result (A : Layout) (z : Site) (record endpoint : ℕ→Word W)
    (src : Memory W) (small : A.ctrl<2^W) (sep : Separated A z)
    (fits : ∀ j : Fin 6,z.words A ⟨36+j.val,by omega⟩<2^W) :
    HistoryStageRoot.atResult (fun k => ((z.output A record endpoint src) k).val) (z.resultBase A)=
      ⟨z.stream A,z.extPins+2*A.trace.bank,z.rows A,z.bits A,z.extBase A,z.extPins⟩ := by
  have r := (z.read_output A record endpoint src small sep).2.2
  have q (i : Fin 6) :
    ((z.output A record endpoint src) (z.resultBase A+i.val)).val=z.words A ⟨36+i.val,by omega⟩ := by
    rw [r,Fin.val_cast_of_lt (fits i)]
  have a := q (0:Fin 6);have b := q (1:Fin 6);have c := q (2:Fin 6)
  have d := q (3:Fin 6);have e := q (4:Fin 6);have f := q (5:Fin 6)
  simp only [Fin.val_zero,Nat.add_zero] at a
  unfold HistoryStageRoot.atResult
  congr 1

theorem Site.records_output {F : Type*} {p : ℕ} (A : Layout) (z : Site) (tag : ((Fin 3→Bool)→F)→ℕ)
    (N : BitNetwork F p) (record endpoint : ℕ→Word W) (src : Memory W)
    (small : A.ctrl<2^W) (sep : Separated A z) (dim : N.cells=z.rows A)
    (words : ∀ i : Fin N.cells,∀ j : Fin 4,
      record (z.stream A+(4*i.val+j.val))=(HistoryCompiledRows.metadata tag N i j:Word W)) :
    HistoryCompiledRows.Records tag N (z.stream A) (z.output A record endpoint src) := by
  intro i j
  let key : Fin (4*z.rows A) := ⟨4*i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩
  exact ((z.read_output A record endpoint src small sep).1 key).trans (words i j)


def recordAt {F : Type*} {p W : ℕ} (tag : ((Fin 3→Bool)→F)→ℕ) (N : BitNetwork F p)
    (start a : ℕ) : Word W :=
  let i:=(a-start)/4
  if hi:i<N.cells then (HistoryCompiledRows.metadata tag N ⟨i,hi⟩ ⟨(a-start)%4,Nat.mod_lt _ (by decide)⟩ : Word W)
  else 0

theorem recordAt_word {F : Type*} {p W : ℕ} (tag : ((Fin 3→Bool)→F)→ℕ) (N : BitNetwork F p)
    (start : ℕ) (i : Fin N.cells) (j : Fin 4) :
    recordAt (W:=W) tag N start (start+(4*i.val+j.val))=(HistoryCompiledRows.metadata tag N i j:Word W) := by
  have hq : (start+(4*i.val+j.val)-start)/4=i.val := by have:=j.isLt;omega
  have hr : (start+(4*i.val+j.val)-start)%4=j.val := by have:=j.isLt;omega
  simp only [recordAt,hq,i.isLt,dite_eq_left,hr]

/-- The complete leaf body preserves every other node, all input banks and
all other result rows outside its four explicit writes. -/
theorem Site.retains_output (z : Site) (A : Layout) (src : Memory W) (record endpoint : ℕ→Word W)
    (small : A.ctrl<2^W) : z.retains A (z.output A record endpoint src) src := by
  have first:=z.retains_next A _ src (z.stream A) (4*z.rows A) record small (z.retains_scratch A src)
    (fun _ h k=>Or.inr (Or.inl ⟨h,k⟩))
  have second:=z.retains_next A _ src (z.extBase A) z.extPins endpoint small first
    (fun _ h k=>Or.inr (Or.inr (Or.inl ⟨h,k⟩)))
  exact z.retains_next A _ src (z.resultBase A) 6 _ small second
    (fun _ h k=>Or.inr (Or.inr (Or.inr ⟨h,k⟩)))

/-- A contiguous source interval misses the four destinations that this leaf can write. -/
structure Protected (A : Layout) (z : Site) (start len : ℕ) : Prop where
  ctrl : start+len≤A.ctrl ∨ A.ctrl+42≤ start
  raw : start+len≤z.stream A ∨ z.stream A+4*z.rows A≤ start
  pairs : start+len≤z.extBase A ∨ z.extBase A+z.extPins≤ start
  result : start+len≤z.resultBase A ∨ z.resultBase A+6≤ start

theorem Protected.read {A : Layout} {z : Site} {start len : ℕ} (h : Protected A z start len)
    {m src : Memory W} (keep : z.retains A m src) (i : ℕ) (hi : i<len) :
    m (start+i)=src (start+i) := by
  apply keep
  obtain ⟨a,b,c,d⟩:=h
  unfold Site.writes
  omega

/-- Every selected write lies between this node's first S12 address and the end
of the S14 seed scratch. Thus either physical address ordering frames a source bank. -/
theorem Protected.of_span {A : Layout} {z : Site} {start len : ℕ} (sep : Separated A z)
    (outside : start+len≤z.stream A ∨ A.ctrl+42≤ start) : Protected A z start len := by
  have h₁:=sep.rowEnds
  have h₂:=sep.pairEnds
  have h₃:=sep.nodeEnds
  constructor <;> omega

end
end ThreeFlat.RAM.HistoryInitialSeed

end OAI
