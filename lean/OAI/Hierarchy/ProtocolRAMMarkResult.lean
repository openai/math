import OAI.Hierarchy.ProtocolRAMMarkPaths

namespace OAI
/-! # Native purchase decisions and the unused marked tiles -/

namespace Hierarchy.ProtocolRAM.MarkTape
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

private theorem path_room (tiles work i : ℕ) (p : List (Fin tiles)) (g : Gate)
    (inPath : g∈compilePath tiles work i p) :
    work≤g.lhs ∧ g.lhs < work+4+tiles+i+1 ∧ work≤g.rhs ∧
      g.rhs < work+4+tiles+i+1 ∧ work≤g.dst ∧ g.dst < work+4+tiles+i+1 := by
  simp only [compilePath,List.mem_append,List.mem_singleton,List.mem_flatMap] at inPath
  rcases inPath with (((setFlag|⟨v,_,testGate⟩)|setNeg)|⟨v,_,clearGate⟩)|store
  · subst g; simp; omega
  · simp only [test,both,List.mem_cons,List.not_mem_nil,or_false] at testGate
    have := v.isLt
    rcases testGate with rfl|rfl <;> simp <;> omega
  · subst g; simp; omega
  · simp only [clear,both,List.mem_cons,List.not_mem_nil,or_false] at clearGate
    have := v.isLt
    rcases clearGate with rfl|rfl <;> simp <;> omega
  · subst g; simp; omega

theorem addresses (tiles work first : ℕ) (ps : List (List (Fin tiles))) (g : Gate)
    (occurs : g∈compilePaths tiles work first ps) :
    work≤g.lhs ∧ g.lhs < work+4+tiles+first+ps.length ∧ work≤g.rhs ∧
      g.rhs < work+4+tiles+first+ps.length ∧ work≤g.dst ∧ g.dst < work+4+tiles+first+ps.length := by
  induction ps generalizing first with
  | nil => simp [compilePaths] at occurs
  | cons p ps ih =>
    rcases List.mem_append.mp occurs with h|h
    · have r := path_room tiles work first p g h
      simp only [List.length_cons]
      omega
    · have r := ih (first+1) h
      simp only [List.length_cons]
      omega

/-- The input bank can hold data of unrestricted word size elsewhere. In the
fresh Boolean region install exactly the currently signed marked tiles. -/
def initialBits (tiles work : ℕ) (left : Finset (Fin tiles)) (a : ℕ) : Bool :=
  decide (∃ i∈left, a=work+4+i.val)

theorem mark_run {w : ℕ} (tiles work first base H : ℕ) (ps : List (List (Fin tiles)))
    (m : Memory w) (left : Finset (Fin tiles)) (fixed : ∀ p∈ps,p.length=H)
    (tape : Packed base (compilePaths tiles work first ps) m)
    (separate : base+3*(ps.length*(4*H+3))≤work)
    (room : work+4+tiles+first+ps.length<2^w)
    (loaded : ∀a,work≤a → a<work+4+tiles+first+ps.length →
      m a=encode w (initialBits tiles work left a)) :
    let out := eval (compilePaths tiles work first ps) m
    (procedure w base (ps.length*(4*H+3))).Exec m out (3+17*(ps.length*(4*H+3))) ∧
      (∀v : Fin tiles, out (work+4+v.val)=encode w (decide (v∈(AdaptiveProbe.scanPaths ps left).2))) ∧
      ∀ (i : ℕ) (hi : i<ps.length), out (work+4+tiles+first+i)=
        encode w ((decisions ps left)[i]'(by simpa using hi)) := by
  let gs := compilePaths tiles work first ps
  let bits := initialBits tiles work left
  let region := fun a => work≤a ∧ a<work+4+tiles+first+ps.length
  have len : gs.length=ps.length*(4*H+3) := compilePaths_size tiles work first ps H fixed
  have span (g) (hg : g∈gs) := addresses tiles work first ps g hg
  have executed : (procedure w base gs.length).Exec m (eval gs m) (3+17*gs.length) := run base gs m tape (by rw [len];omega) (fun g hg=>by
    have h := span g hg
    rw [len]
    omega)
  have same := eval_bits gs m bits region (fun a h=>loaded a h.1 h.2) (fun g h=>by
    have v := span g h
    exact ⟨⟨v.1,v.2.1⟩,⟨v.2.2.1,v.2.2.2.1⟩⟩)
  have zero : bits work=false := by
    simp only [bits,initialBits,decide_eq_false_iff_not]
    rintro ⟨v,_,h⟩
    omega
  have marks : Holds work bits left := by
    intro i
    have iff : (∃ j∈left, work+4+i.val=work+4+j.val) ↔ i∈left := by
      constructor
      · rintro ⟨j,hj,eqn⟩
        have e : i=j := Fin.ext (by omega)
        simpa [e] using hj
      · intro hi
        exact ⟨i,hi,rfl⟩
    simp only [bits,initialBits,iff]
  obtain ⟨remaining,picks⟩ := paths_semantics tiles work first ps bits left zero marks
  refine ⟨?_,?_,?_⟩
  · rw [←len]
    exact @executed
  · intro v
    have hv := v.isLt
    exact (same _ ⟨by omega,by omega⟩).trans (congrArg (encode w) (remaining v))
  · intro i hi
    exact (same _ ⟨by omega,by omega⟩).trans (congrArg (encode w) (picks i hi))

end Hierarchy.ProtocolRAM.MarkTape

end OAI
