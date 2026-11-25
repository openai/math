import OAI.Hierarchy.DescentGLInputRAM
import OAI.Hierarchy.DescentGLSpanRAM

namespace OAI
/-! # A complete physical mixing row, from the original weight columns to the next span -/

namespace Hierarchy.DescentGL.RowStageRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentIntegerScale DescentWalshTables
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section

/-- The span, difference weights, Walsh scores and selected index occupy successive intervals.
The next span begins immediately after that immutable index. -/
structure Shelf where
  mask : ℕ
  data : ℕ
  scores : ℕ
  row : ℕ
  nextMask : ℕ

def placed (k base h : ℕ) : Shelf :=
  let b := base+h*(3*2^k+1)
  ⟨b,b+2^k,b+2*2^k,b+3*2^k,b+(3*2^k+1)⟩

structure Shelf.Room (s : Shelf) (k w : ℕ) : Prop where
  old : s.mask+2^k≤ s.data
  input : s.data+2^k≤ s.scores
  scored : s.scores+2^k≤ s.row
  kept : s.row+1≤ s.nextMask
  limit : s.nextMask+2^k<2^w

theorem placed_room (k w base h : ℕ) (end_ : (placed k base h).nextMask+2^k<2^w) :
    (placed k base h).Room k w := by
  refine ⟨?_,?_,?_,?_,end_⟩ <;> dsimp [placed] <;> omega

@[simp] theorem placed_next (k base h : ℕ) : (placed k base (h+1)).mask=(placed k base h).nextMask := by
  simp [placed,Nat.add_mul,Nat.add_assoc]

variable {h r w : ℕ}

def writeScore (k : ℕ) (s : Shelf) (m : Memory w) := ProtocolRAM.image s.scores (2^k) (DescentGLScoreRAM.score k s.data) m

def writeChoice (k : ℕ) (s : Shelf) (m : Memory w) :=
  ProtocolRAM.image s.row 1 (RowRAM.term ⟨s.mask,k⟩ ⟨s.scores,k⟩ (2^k)) m

def writeMask (k : ℕ) (s : Shelf) (m : Memory w) :=
  ProtocolRAM.image s.nextMask (2^k) (SpanRAM.next k s.mask s.row) m

private theorem fitsBank {k addr dest : ℕ} (end₁ : addr+2^k≤dest) (size : 2^k<2^w) :
    (Bank.mk addr k).Fits w dest := ⟨Nat.two_pow_pos _,size,end₁⟩

private theorem prefix_le (h r : ℕ) : h ≤ h+1+r := by omega

local notation "k" => (h+1+r)
local notation "N" => (2^k)
local notation "prefixLE" => prefix_le h r

def writeInput (s : Shelf) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ) (m : Memory w) :=
  ProtocolRAM.image s.data N (DescentGLInputRAM.terms ptr bank) m

def after (s : Shelf) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ) (m : Memory w) :=
  writeMask k s (writeChoice k s (writeScore k s (writeInput s ptr bank m)))

def program (w : ℕ) (s : Shelf) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ) :=
  (DescentGLInputRAM.pass w s.data ptr bank).seq
    ((DescentGLScoreRAM.program w s.scores k s.data).seq
      ((RowRAM.procedure w s.row N ⟨s.mask,k⟩ ⟨s.scores,k⟩).seq
        (scan w s.nextMask N (SpanRAM.next k s.mask s.row))))

def ticks (s : Shelf) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ) :=
  (4+N*(2*(DescentGLInputRAM.terms ptr bank).work+4))+
    ((4+N*(2*(DescentGLScoreRAM.score k s.data).work+4))+
      ((4+1*(2*(RowRAM.term ⟨s.mask,k⟩ ⟨s.scores,k⟩ N).work+4))+
        (4+N*(2*(16+N*(9+5*N))+4))))

theorem execute (s : Shelf) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ) (m : Memory w)
    (space : s.Room k w) (prev : ∀i : Fin h,ptr (i.castLE prefixLE)<s.data)
    (inputs : ∀j,(Bank.mk (bank j) k).Fits w s.data) :
    (program w s ptr bank).Exec m (RowStageRAM.after s ptr bank m) (ticks s ptr bank) := by
  obtain ⟨om,di,sc,rc,last⟩ := space
  have positive := Nat.two_pow_pos k
  have size : N<2^w := by omega
  apply Procedure.Exec.then (DescentGLInputRAM.execute m ptr bank (by omega) prev inputs)
  apply Procedure.Exec.then (DescentGLScoreRAM.run (writeInput s ptr bank m) (fitsBank di size) (by omega))
  apply Procedure.Exec.then (RowRAM.execute s.row N ⟨s.mask,k⟩ ⟨s.scores,k⟩ _
    (fitsBank (by omega) size) (fitsBank sc size) (by omega))
  exact SpanRAM.extend_exec s.mask s.row s.nextMask _ (fitsBank (by omega) size) (by omega) last

theorem old_word (s : Shelf) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ) (m : Memory w)
    (space : s.Room k w) (x : ℕ) (below : x<s.data) : RowStageRAM.after s ptr bank m x=m x := by
  obtain ⟨_,di,sc,rc,_⟩ := space
  have p := Nat.two_pow_pos k
  unfold RowStageRAM.after writeMask writeChoice writeScore writeInput
  rw [SpanRAM.frame s.nextMask N _ _ x (.inl (by omega)),
    SpanRAM.frame s.row 1 _ _ x (.inl (by omega)),
    SpanRAM.frame s.scores N _ _ x (.inl (by omega)),SpanRAM.frame s.data N _ _ x (.inl below)]

/-- Both receipts concern the very same post-stage memory. Neither the selected
row nor the next exclusion bitmap is an advised input. -/
theorem publish (s : Shelf) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ) (m : Memory w)
    (space : s.Room k w) (L : Layout k) (W : Fin (r+1)→Bits k→ℕ) {q : ℕ} (hq : 0<q)
    (old : SpanRAM.bitmap s.mask (fun a : Fin h=>rowFunctional L (a.castLE prefixLE)) m)
    (rows : ∀i : Fin h,m (ptr (i.castLE prefixLE))=((rowIndex k (rowFunctional L (i.castLE prefixLE))).val:Word w))
    (loads : ∀j (z : Fin N),m (bank j+z.val)=(W j (DescentGLScoreRAM.vec z):Word w))
    (small : ∀i : Fin N,2*rowNumerator r W (surviving L ((rowIndex k).symm i))<2^w) :
    let objective := conditionalRowScore L (fun j d=>(W j d.val:ℝ)/(q:ℝ)^2)
    let a := chosenIndex (show h<k by omega) L objective
    let mem := RowStageRAM.after s ptr bank m
    mem s.row=(a.val:Word w) ∧
      SpanRAM.bitmap s.nextMask (Fin.snoc (fun j : Fin h=>rowFunctional L (j.castLE prefixLE))
        ((rowIndex k).symm a)) mem := by
  dsimp only
  obtain ⟨om,di,sc,rc,last⟩ := space
  have pos := Nat.two_pow_pos k
  have size : N<2^w := by omega
  have wide : 1<2^w := by omega
  let m₁ := writeInput s ptr bank m
  let m₂ := writeScore k s m₁
  let m₃ := writeChoice k s m₂
  let prev := fun j : Fin h=>rowFunctional L (j.castLE prefixLE)
  let f := conditionalRowScore L (fun j d=>(W j d.val:ℝ)/(q:ℝ)^2)
  let a := chosenIndex (show h<k by omega) L f
  have bank₂ : SpanRAM.bitmap s.mask prev m₂ := by
    intro i
    have hi := i.isLt
    change ProtocolRAM.image _ _ _ (ProtocolRAM.image _ _ _ m) _=_
    rw [SpanRAM.frame s.scores N _ _ (s.mask+i.val) (.inl (by omega)),
      SpanRAM.frame s.data N _ m (s.mask+i.val) (.inl (by omega))]
    exact old i
  have trueInput := DescentGLInputRAM.published m ptr bank L W (by omega : s.data+N<2^w) rows loads
  have scored (i : Fin N) : RowRAM.score ⟨s.scores,k⟩ m₂ i=2*rowNumerator r W (surviving L ((rowIndex k).symm i)) := by
    simpa [RowRAM.score,Bank.read,Bank.size,Fin.val_cast_of_lt (i.isLt.trans size),Nat.mod_eq_of_lt i.isLt,m₂,writeScore]
      using DescentGLScoreRAM.order_read m₁ L W (by omega : s.scores+N<2^w) trueInput small i
  have picked : m₃ s.row=(a.val:Word w) := by
    have hk : h<k := by omega
    apply RowRAM.physical_chosen hk L f ⟨s.mask,k⟩ ⟨s.scores,k⟩ m₂ s.row wide
      (SpanRAM.legal hk s.mask m₂ bank₂ size.le wide)
    intro i j
    rw [scored,scored]
    by_cases hr : 0<r
    · rw [show f ((rowIndex k).symm i) ≤ f ((rowIndex k).symm j) ↔ _ from
        compare_conditionalRows L _ _ hq hr W]
      omega
    · obtain rfl : r=0 := by omega
      simp [f,conditionalRowScore_eq_integer,rowNumerator_zero]
  have bank₃ : SpanRAM.bitmap s.mask prev m₃ := by
    intro i
    have hi := i.isLt
    exact (SpanRAM.frame s.row 1 _ m₂ (s.mask+i.val) (.inl (by omega))).trans (bank₂ i)
  refine ⟨(SpanRAM.frame s.nextMask N _ m₃ s.row (.inl (by omega))).trans picked,?_⟩
  apply SpanRAM.extend s.mask s.row s.nextMask m₃ prev ((rowIndex k).symm a) bank₃ _ size.le wide
  simpa using picked

end
end Hierarchy.DescentGL.RowStageRAM

end OAI
