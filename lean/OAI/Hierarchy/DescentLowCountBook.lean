import OAI.Hierarchy.DescentPrivateHeaderCheap
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Publish retained ordinary pair counts to the selector verifier's low registers -/
namespace Hierarchy.DescentLowCountBook
open DescentPrivateHeader ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
variable {w : ℕ}

/-- `source i` is the retained ordinary matcher's absolute scalar address. The low
array starts beyond the checked seed and ends before the immutable prefix archive. -/
def program (w first : ℕ) (source : ℕ→ℕ) : ℕ→ Procedure w
  | 0 => scan w first 0 (.lit 0)
  | n+1 => (program w first source n).seq (commit w (first+n) (source n))

def output (first : ℕ) (source : ℕ→ℕ) (m : Memory w) : ℕ→ Memory w
  | 0 => m
  | n+1 => committed (first+n) (source n) (output first source m n)

theorem frame (first : ℕ) (source : ℕ→ℕ) (m : Memory w) (n x : ℕ)
    (away : x< first ∨ first+n≤ x) : output first source m n x=m x := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [output,committed_frame _ _ _ _ (by omega)]
    exact ih (by omega)

theorem read (first : ℕ) (source : ℕ→ℕ) (m : Memory w) (n : ℕ)
    (above : ∀i< n,first+n≤ source i) (i : Fin n) :
    output first source m n (first+i.val)=m (source i.val) := by
  induction n with
  | zero=>exact i.elim0
  | succ n ih=>
    obtain h|h:=Nat.lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt)
    · rw [output,committed_frame _ _ _ _ (by omega)]
      exact ih (fun t ht=>(Nat.le_succ _).trans (above t (ht.trans (Nat.lt_succ_self _)))) ⟨_,h⟩
    · rw [h,output,committed_read]
      exact frame _ _ _ _ _ (Or.inr ((Nat.le_succ _).trans (above n (Nat.lt_succ_self _))))

theorem run (first : ℕ) (source : ℕ→ℕ) (m : Memory w) (n : ℕ)
    (base : first<2^w) (above : ∀i< n,first+i≤ source i) (fits : ∀i< n,source i+1<2^w) :
    (program w first source n).Exec m (output first source m n) (4+11*n) :=by
  induction n with
  | zero=>
    have step : (scan w first 0 (.lit 0)).Exec m (image first 0 (.lit 0) m) (4+0*(2*(Expr.lit 0).work+4)):=
      @scan_exec w first 0 (.lit 0) m trivial (by simpa using base)
    have same : image first 0 (.lit 0) m=m:=by
      funext a
      simp [ProtocolRAM.image,fillSegment]
    rw [same] at step
    change (scan w first 0 (.lit 0)).Exec m m 4
    exact step
  | succ n ih=>
    have prev : (program w first source n).Exec m (output first source m n) (4+11*n):=ih (fun i hi=>above i (hi.trans (Nat.lt_succ_self _))) (fun i hi=>fits i (hi.trans (Nat.lt_succ_self _)))
    have install : (commit w (first+n) (source n)).Exec (output first source m n)
        (committed (first+n) (source n) (output first source m n)) 11:=commit_run (first+n) (source n) (output first source m n) (above n (Nat.lt_succ_self _))
      (fits n (Nat.lt_succ_self _))
    rw [show 4+11*(n+1)=(4+11*n)+11 by omega]
    intro P R K machine
    exact Procedure.Exec.then prev install machine

theorem hardware (w first : ℕ) (source : ℕ→ℕ) (n : ℕ) :
    CheapCode (program w first source n) ∧ DescentStaticWordColumn.names (program w first source n)=15+18*n :=by
  induction n with
  | zero=>exact ⟨@scan_cheap w first 0 (.lit 0),by rw [program,DescentStaticWordColumn.names_scan];rfl⟩
  | succ n ih=>
    refine ⟨cheap_seq ih.1 (@commit_cheap w (first+n) (source n)),?_⟩
    rw [program,DescentStaticWordColumn.names_seq,ih.2]
    change 15+18*n+18=15+18*(n+1)
    omega

end Hierarchy.DescentLowCountBook

end OAI
