import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Issuing a different fixed row expression at each position of a bounded output -/
namespace Hierarchy.DescentFixedRowProgram
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentStaticWordColumn (names names_scan names_seq)
open scoped Fin.CommRing

def program (w base : ℕ) (f : ℕ→Expr) : ℕ→Procedure w
  | 0=>scan w base 0 (.lit 0)
  | i+1=>(program w base f i).seq (scan w (base+i) 1 (f i))

def image {w : ℕ} (base : ℕ) (f : ℕ→Expr) (m : Memory w) : ℕ→Memory w
  | 0=>ProtocolRAM.image base 0 (.lit 0) m
  | i+1=>ProtocolRAM.image (base+i) 1 (f i) (image base f m i)

def clock (f : ℕ→Expr) : ℕ→ℕ
  | 0=>4
  | i+1=>clock f i + (4+1*(2*(f i).work+4))

theorem run {w : ℕ} (base n : ℕ) (f : ℕ→Expr) (m : Memory w)
    (fits : ∀i<n,(f i).Fits w base) (stop : base+n<2^w) :
    (program w base f n).Exec m (image base f m n) (clock f n) := by
  induction n with
  | zero=>exact scan_exec _ 0 (.lit 0) m trivial (by omega)
  | succ i ih=>
    have last : (scan w (base+i) 1 (f i)).Exec (image base f m i) (image base f m (i+1))
        (4+1*(2*(f i).work+4)) := scan_exec _ _ _ _ (ProtocolRAMGeneratedWrite.fits_mono _
          (Nat.le_add_right ..) (fits i (by omega))) (by omega)
    intro P R K machine
    exact Procedure.Exec.then (ih (fun j hj=>fits j (by omega)) (by omega)) last machine

theorem frame {w : ℕ} (base n : ℕ) (f : ℕ→Expr) (m : Memory w) (a : ℕ) (away : a<base ∨ base+n≤a) :
    image base f m n a=m a := by
  induction n with
  | zero=>exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)
  | succ i ih=>exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)).trans (ih (by omega))

theorem read {w : ℕ} (base n : ℕ) (f : ℕ→Expr) (m : Memory w) {j : ℕ}
    (inside : j<n) (fits : (f j).Fits w base) : image base f m n (base+j)=(f j).eval m 0 := by
  induction n with
  | zero=>omega
  | succ i ih=>
    by_cases same : i=j
    · subst i
      exact (ProtocolRAMGeneratedWrite.read_image _ 1 _ _ (0:Fin 1)).trans
        (eval_below (f j) 0 m _ fits (fun a h=>frame base j f m a (.inl h)))
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans (ih (by omega))

theorem cheap (w base n : ℕ) (f : ℕ→Expr) : CheapCode (program w base f n) := by
  induction n with
  | zero=>intro P R K pc reg pub exit i; exact scan_cheap w base 0 (.lit 0) pc reg pub exit i
  | succ i ih=>intro P R K pc reg pub exit j; exact cheap_seq ih (scan_cheap w (base+i) 1 (f i)) pc reg pub exit j

theorem bill (w base n : ℕ) (f : ℕ→Expr) (bound : ℕ) (small : ∀i<n,(f i).work≤bound) :
    clock f n+names (program w base f n) ≤ 19+n*(19+6*bound) := by
  induction n with
  | zero=>simp [clock,program,names_scan,Expr.work]
  | succ i ih=>
    have prev:=ih (fun j hj=>small j (by omega))
    have next:=small i (by omega)
    rw [clock,program,names_seq,names_scan,Nat.succ_mul i (19+6*bound)]
    omega

end Hierarchy.DescentFixedRowProgram

end OAI
