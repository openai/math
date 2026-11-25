import OAI.Hierarchy.ProtocolRAMMarkResult
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Initialize the purchase workspace from the signed tile bank and run it -/

namespace Hierarchy.ProtocolRAM.MarkTape
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing

def loadTerm (tiles : ℕ) (marks : Bank) : Expr :=
  .branch .lt .row (.lit 4) (.lit 0)
    (.branch .lt .row (.lit (4+tiles)) (.lookup marks (.op .sub .row (.lit 4))) (.lit 0))

def load (w tiles work first candidates : ℕ) (marks : Bank) : Procedure w :=
  scan w work (4+tiles+first+candidates) (loadTerm tiles marks)

def loaded {w : ℕ} (tiles work first candidates : ℕ) (marks : Bank) (m : Memory w) :=
  image work (4+tiles+first+candidates) (loadTerm tiles marks) m

def loadClock (tiles first candidates : ℕ) (marks : Bank) :=
  4+(4+tiles+first+candidates)*(2*(loadTerm tiles marks).work+4)

theorem load_exec {w : ℕ} (tiles work first count : ℕ) (marks : Bank) (m : Memory w)
    (deps : marks.Fits w work) (fit : work+4+tiles+first+count<2^w) :
    (load w tiles work first count marks).Exec m (loaded tiles work first count marks m)
      (loadClock tiles first count marks) := by
  apply scan_exec
  · exact ⟨trivial,trivial,trivial,⟨trivial,trivial,⟨deps,trivial,trivial⟩,trivial⟩⟩
  · omega

theorem loaded_words {w : ℕ} (tiles work first count : ℕ) (marks : Bank) (m : Memory w)
    (left : Finset (Fin tiles)) (signed : ∀ i : Fin tiles,marks.read m (i.val:Word w)=encode w (decide (i∈left)))
    (room : work+4+tiles+first+count<2^w) :
    ∀ a,work≤a → a<work+4+tiles+first+count → loaded tiles work first count marks m a =
      encode w (initialBits tiles work left a) := by
  intro a lo hi
  let k := a-work
  have row : (a:Word w)-(work:Word w)=(k:Word w) := by simp [k,Nat.cast_sub lo]
  have fitK : k<2^w := by dsimp [k];omega
  have fitT : 4+tiles<2^w := by omega
  have fit4 : 4<2^w := by omega
  have inside : work≤a ∧ a<work+(4+tiles+first+count) := by omega
  simp only [loaded,image,fillSegment,ite_eq_left inside,row,loadTerm,Expr.eval,Comparison.test,
    decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt fitK,Fin.val_cast_of_lt fitT,Fin.val_cast_of_lt fit4]
  by_cases low : k<4
  · have empty : ¬∃i∈left,a=work+4+i.val := by rintro ⟨i,_,e⟩;dsimp [k] at low;omega
    simp [low,initialBits,empty,encode]
  · rw [ite_eq_right low]
    by_cases t : k<4+tiles
    · let v : Fin tiles := ⟨k-4,by omega⟩
      have index : RowOp.sub.opcode.eval (k:Word w) ((4:ℕ):Word w)=(v.val:Word w) := by
        simp [v,RowOp.opcode,BinaryOp.eval,Nat.cast_sub (by omega : 4≤k)]
      have bit : (∃i∈left,a=work+4+i.val) ↔ v∈left := by
        constructor
        · rintro ⟨i,h,e⟩
          have eq : v=i := Fin.ext (by dsimp [v,k];omega)
          simpa [eq] using h
        · intro hv
          exact ⟨v,hv,by dsimp [v,k];omega⟩
      simp only [ite_eq_left t,initialBits,bit]
      exact (congrArg (marks.read m) index).trans (signed v)
    · have empty : ¬∃i∈left,a=work+4+i.val := by rintro ⟨i,_,e⟩;have := i.isLt;dsimp [k] at t;omega
      simp [t,initialBits,empty,encode]

theorem loaded_below {w : ℕ} (tiles work first count : ℕ) (marks : Bank) (m : Memory w)
    (a : ℕ) (low : a<work) : loaded tiles work first count marks m a=m a := by
  simp [loaded,image,fillSegment,not_le.mpr low]

/-- The native machine first zeros the whole fresh workspace and installs exactly the
signed eligible tile words, then reads its physical address tape to run maximal selection. -/
theorem load_and_run {w : ℕ} (tiles work first base H : ℕ) (ps : List (List (Fin tiles)))
    (marks : Bank) (m : Memory w) (left : Finset (Fin tiles)) (fixed : ∀p∈ps,p.length=H)
    (signed : ∀i : Fin tiles,marks.read m (i.val:Word w)=encode w (decide (i∈left)))
    (deps : marks.Fits w work) (tape : Packed base (compilePaths tiles work first ps) m)
    (separate : base+3*(ps.length*(4*H+3))≤work)
    (room : work+4+tiles+first+ps.length<2^w) :
    let n := ps.length*(4*H+3)
    let out := eval (compilePaths tiles work first ps) (loaded tiles work first ps.length marks m)
    ((load w tiles work first ps.length marks).seq (procedure w base n)).Exec m out
      (loadClock tiles first ps.length marks+(3+17*n)) ∧
      (∀v : Fin tiles,out (work+4+v.val)=encode w (decide (v∈(AdaptiveProbe.scanPaths ps left).2))) ∧
      ∀(i : ℕ)(hi : i<ps.length),out (work+4+tiles+first+i)=
        encode w ((decisions ps left)[i]'(by simpa using hi)) := by
  have len := compilePaths_size tiles work first ps H fixed
  have keep : Packed base (compilePaths tiles work first ps) (loaded tiles work first ps.length marks m) := by
    intro i
    have hi := i.isLt
    obtain ⟨x,y,z⟩ := tape i
    simpa only [loaded_below _ _ _ _ _ _ _ (by omega : base+i.val<work),
      loaded_below _ _ _ _ _ _ _ (by omega : base+(compilePaths tiles work first ps).length+i.val<work),
      loaded_below _ _ _ _ _ _ _ (by omega : base+2*(compilePaths tiles work first ps).length+i.val<work)]
      using And.intro x (And.intro y z)
  obtain ⟨act,words,bits⟩ := mark_run tiles work first base H ps _ left fixed keep separate room
    (loaded_words tiles work first ps.length marks m left signed room)
  refine ⟨?_,words,bits⟩
  apply Procedure.Exec.then (load_exec tiles work first ps.length marks m deps room)
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact act M pc reg pub exit rom data cfg start entry same


end Hierarchy.ProtocolRAM.MarkTape

end OAI
