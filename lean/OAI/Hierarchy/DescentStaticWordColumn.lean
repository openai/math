import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Mounting fixed integer tables with one private store per public literal -/

namespace Hierarchy.DescentStaticWordColumn
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing

def program (w at₀ : ℕ) (data : ℕ→ℕ) : ℕ→Procedure w
  | 0=>scan w at₀ 0 (.lit 0)
  | j+1=>(program w at₀ data j).seq (scan w (at₀+j) 1 (.lit (data j)))

def image {w : ℕ} (at₀ : ℕ) (data : ℕ→ℕ) (m : Memory w) : ℕ→Memory w
  | 0=>ProtocolRAM.image at₀ 0 (.lit 0) m
  | j+1=>ProtocolRAM.image (at₀+j) 1 (.lit (data j)) (image at₀ data m j)

theorem mount {w : ℕ} (at₀ n : ℕ) (data : ℕ→ℕ) (m : Memory w) (space : at₀+n<2^w) :
    (program w at₀ data n).Exec m (image at₀ data m n) (4+10*n) := by
  induction n with
  | zero=>exact ProtocolRAM.scan_exec at₀ 0 (.lit 0) m trivial (by omega)
  | succ j ih=>
    have step : (scan w (at₀+j) 1 (.lit (data j))).Exec (image at₀ data m j)
        (ProtocolRAM.image (at₀+j) 1 (.lit (data j)) (image at₀ data m j)) (4+1*(2*1+4)) :=
      ProtocolRAM.scan_exec (at₀+j) 1 (.lit (data j)) (image at₀ data m j) trivial (by omega)
    rw [program,image,show 4+10*(j+1)=(4+10*j)+(4+1*(2*1+4)) by omega]
    intro P R K machine
    exact Procedure.Exec.then (ih (by omega)) step machine

theorem read {w : ℕ} (at₀ n : ℕ) (data : ℕ→ℕ) (m : Memory w) {j : ℕ} (lt : j<n) :
    image at₀ data m n (at₀+j)=(data j:Word w) := by
  induction n with
  | zero=>omega
  | succ n ih=>
    by_cases last : n=j
    · subst j
      exact ProtocolRAMGeneratedWrite.read_image (at₀+n) 1 _ _ (0:Fin 1)
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans (ih (by omega))

theorem frame {w : ℕ} (at₀ n : ℕ) (data : ℕ→ℕ) (m : Memory w) (a : ℕ) (away : a<at₀ ∨ at₀+n≤a) :
    image at₀ data m n a=m a := by
  induction n with
  | zero=>exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)
  | succ j ih=>
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)).trans (ih (by omega))

def names {w : ℕ} (p : Procedure w) := p.labels+p.registers+p.slots

theorem names_scan (w lo n : ℕ) (e : Expr) :
    names (scan w lo n e)=11+4*e.work := by
  simp only [names,scan,PhysicalInputPhases.writing,DescriptorExpr.Term.labels_eq,compile_binds]
  omega

theorem names_seq {w : ℕ} (a b : Procedure w) : names (a.seq b)=names a+names b := by
  unfold names Procedure.seq
  dsimp only
  omega

theorem names_mount (w base : ℕ) (data : ℕ→ℕ) (n : ℕ) :
    names (program w base data n)=15*(n+1) := by
  induction n with
  | zero=>rw [program,names_scan];rfl
  | succ i ih=>
    rw [program,names_seq,ih,names_scan]
    change 15*(i+1)+(11+4*1)=15*(i+1+1)
    omega

end Hierarchy.DescentStaticWordColumn

end OAI
