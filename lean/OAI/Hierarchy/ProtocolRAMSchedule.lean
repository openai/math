import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Sequential execution of the advised protocol passes -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

/-- Inputs may come from any earlier pass, including its decisions about candidate balls. -/
structure Pass where
  out : ℕ
  rows : ℕ
  term : Expr

def Pass.Fits (w : ℕ) (p : Pass) : Prop := p.term.Fits w p.out ∧ p.out+p.rows < 2^w

/-- The compiler computes the end of every input bank from the fixed controller
description. Thus fresh contiguous output allocators can discharge all input checks. -/
def Expr.inputEnd : Expr → ℕ
  | .row | .lit _ => 0
  | .lookup b i => max (b.base+b.size) i.inputEnd
  | .op _ x y => max x.inputEnd y.inputEnd
  | .branch _ x y yes no => max (max x.inputEnd y.inputEnd) (max yes.inputEnd no.inputEnd)

theorem Expr.fits_of_inputEnd (e : Expr) {w out : ℕ} (before : e.inputEnd≤out) (fits : out<2^w) :
    e.Fits w out := by
  induction e with
  | row | lit => trivial
  | lookup b i ih =>
    obtain ⟨bank,index⟩ := max_le_iff.mp before
    exact ⟨⟨Nat.two_pow_pos _,by omega,bank⟩,ih index⟩
  | op _ x y hx hy =>
    obtain ⟨xlo,ylo⟩ := max_le_iff.mp before
    exact ⟨hx xlo,hy ylo⟩
  | branch _ x y a b hx hy ha hb =>
    obtain ⟨tests,branches⟩ := max_le_iff.mp before
    obtain ⟨xlo,ylo⟩ := max_le_iff.mp tests
    obtain ⟨alo,blo⟩ := max_le_iff.mp branches
    exact ⟨hx xlo,hy ylo,ha alo,hb blo⟩

theorem Pass.fits_of_span (p : Pass) {w : ℕ} (separate : p.term.inputEnd≤p.out)
    (endFits : p.out+p.rows<2^w) : p.Fits w :=
  ⟨p.term.fits_of_inputEnd separate (by omega),endFits⟩

def Pass.clock (p : Pass) := 4+p.rows*(2*p.term.work+4)

def Pass.procedure (w : ℕ) (p : Pass) := scan w p.out p.rows p.term

def Pass.apply {w : ℕ} (p : Pass) (m : Memory w) := image p.out p.rows p.term m

def program (w : ℕ) : List Pass → Procedure w
  | [] => scan w 0 0 (.lit 0)
  | p::ps => (p.procedure w).seq (program w ps)

def result {w : ℕ} : List Pass → Memory w → Memory w
  | [],m => m
  | p::ps,m => result ps (p.apply m)

def clock : List Pass → ℕ
  | [] => 4
  | p::ps => p.clock + clock ps

/-- No matter which selectors are supplied, the linked native program follows the same
bounded sequence of passes. Each later pass reads the actual memory left by its predecessors. -/
theorem program_exec {w : ℕ} (ps : List Pass) (m : Memory w)
    (fits : ∀ p ∈ ps, p.Fits w) : (program w ps).Exec m (result ps m) (clock ps) := by
  induction ps generalizing m with
  | nil =>
    intro P R K M pc reg pub exit rom params c mem entry same
    simpa [program,result,clock,image] using
      (scan_exec (w:=w) 0 0 (.lit 0) m trivial (by simp)
        M pc reg pub exit rom params c mem entry same)
  | cons p ps ih =>
    obtain ⟨safe,room⟩ := fits p (by simp)
    apply Procedure.Exec.then (scan_exec p.out p.rows p.term m safe room)
    intro P R K M pc reg pub exit rom pars c mem entry same
    exact ih (p.apply m) (fun q hq => fits q (by simp [hq])) M pc reg pub exit rom pars c mem entry same

theorem clock_le (ps : List Pass) (rows work : ℕ)
    (bounds : ∀ p∈ps, p.rows≤rows ∧ p.term.work≤work) :
    clock ps ≤ 4+ps.length*(4+rows*(2*work+4)) := by
  induction ps with
  | nil => simp [clock]
  | cons p ps ih =>
    obtain ⟨hr,hw⟩ := bounds p (by simp)
    have rest := ih (fun q hq => bounds q (by simp [hq]))
    have prod := Nat.mul_le_mul hr (show 2*p.term.work+4≤2*work+4 by omega)
    simp only [clock,Pass.clock,List.length_cons,Nat.succ_mul ps.length]
    omega

theorem scan_size (w out n : ℕ) (e : Expr) :
    (scan w out n e).labels = 7+3*e.work ∧ (scan w out n e).registers = 4+e.work ∧
    (scan w out n e).slots = 0 := by
  simp [scan,PhysicalInputPhases.writing,Term.labels_eq,compile_binds]
  omega

/-- Size of the linked ROM and register bank is independent of all scanned extents. -/
theorem program_size (w : ℕ) (ps : List Pass) :
    (program w ps).labels = 10+(ps.map (fun p=>7+3*p.term.work)).sum ∧
    (program w ps).registers = 5+(ps.map (fun p=>4+p.term.work)).sum ∧
    (program w ps).slots = 0 := by
  induction ps with
  | nil => simpa [program,Expr.work] using scan_size w 0 0 (.lit 0)
  | cons p ps ih =>
    obtain ⟨pc,regs,slots⟩:=scan_size w p.out p.rows p.term
    change (scan w p.out p.rows p.term).labels+(program w ps).labels=_ ∧
      (scan w p.out p.rows p.term).registers+(program w ps).registers=_ ∧
      (scan w p.out p.rows p.term).slots+(program w ps).slots=_
    simp only [List.map_cons,List.sum_cons]
    constructor
    · exact (congrArg₂ Nat.add pc ih.1).trans (Nat.add_left_comm _ _ _)
    · constructor
      · exact (congrArg₂ Nat.add regs ih.2.1).trans (Nat.add_left_comm _ _ _)
      · exact (congrArg₂ Nat.add slots ih.2.2).trans rfl

/-- A bounded mesh uses only the indicated number of rounds even on selectors
whose early stopping flag has already been set. Subsequent guarded writes copy
the corresponding inventory when the flag marks the interval as finished. -/
def mesh (intervals attempts : ℕ) (round : Fin intervals → Fin attempts → List Pass) : List Pass :=
  (List.finRange intervals).flatMap fun i => (List.finRange attempts).flatMap (round i)

theorem mesh_length (intervals attempts perRound : ℕ)
    (round : Fin intervals → Fin attempts → List Pass)
    (bound : ∀ i j, (round i j).length ≤ perRound) :
    (mesh intervals attempts round).length ≤ intervals*attempts*perRound := by
  have flatten {X : Type} (l : List X) (f : X → List Pass) (b : ℕ)
      (h : ∀ i ∈ l, (f i).length ≤ b) : (l.flatMap f).length ≤ l.length*b := by
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
      have h₁ := h x (by simp)
      have h₂ := ih (fun i hi => h i (by simp [hi]))
      omega
  rw [mesh,Nat.mul_assoc]
  simpa using flatten (List.finRange intervals)
    (fun i => (List.finRange attempts).flatMap (round i)) (attempts*perRound) (by
      intro i _
      simpa using flatten (List.finRange attempts) (round i) perRound (fun j _ => bound i j))

/-- Immutable advice remains readable throughout every pass whenever its address lies
below each chronological output. This applies uniformly to accepted and rejected words. -/
theorem result_below {w : ℕ} (ps : List Pass) (m : Memory w) (a : ℕ)
    (below : ∀ p ∈ ps, a<p.out) : result ps m a = m a := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    rw [result,ih (p.apply m) (fun v hv => below v (by simp [hv]))]
    have bound := below p (by simp)
    simp [Pass.apply,image,fillSegment,not_le.mpr bound]

theorem result_append {w : ℕ} (ps qs : List Pass) (m : Memory w) :
    result (ps++qs) m = result qs (result ps m) := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih => exact ih (p.apply m)


end Hierarchy.ProtocolRAM

end OAI
