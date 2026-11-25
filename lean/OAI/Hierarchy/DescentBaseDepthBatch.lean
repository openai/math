import OAI.Hierarchy.DescentBaseDepthKernels
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # A fixed sweep of scalar instructions at public addresses -/

namespace Hierarchy.DescentBaseProfile.DepthRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

structure Batch where
  out : ℕ
  expr : ℕ→Expr

namespace Batch
def text (b : Batch) (w : ℕ) : ℕ→Procedure w
  | 0=>scan w b.out 0 (.lit 0)
  | j+1=>(b.text w j).seq (scan w (b.out+j) 1 (b.expr j))

def ticks (b : Batch) : ℕ→ℕ
  | 0=>4
  | j+1=>b.ticks j+(4+1*(2*(b.expr j).work+4))

variable {w : ℕ}

def memory (b : Batch) (m : Memory w) : ℕ→Memory w
  | 0=>m
  | j+1=>image (b.out+j) 1 (b.expr j) (b.memory m j)

theorem cheap (b : Batch) (w n : ℕ) : CheapCode (b.text w n) := by
  induction n with
  | zero=>exact @scan_cheap _ _ _ _
  | succ n ih=>exact cheap_seq ih (@scan_cheap _ _ _ _)

theorem run (b : Batch) (m : Memory w) (n : ℕ)
    (readOnly : ∀i<n,(b.expr i).inputEnd≤b.out) (room : b.out+n<2^w) :
    (b.text w n).Exec m (b.memory m n) (b.ticks n) := by
  induction n with
  | zero =>
    have empty : image b.out 0 (.lit 0) m=m := by
      funext a
      exact ProtocolRAMGeneratedWrite.frame_image b.out 0 (.lit 0) m a (by omega)
    intro P R K M p r a t h v c m₀ pc e
    simpa only [text,ticks,memory,empty,Nat.zero_mul,Nat.add_zero] using
      (@scan_exec w b.out 0 (.lit 0) m trivial room P R K M p r a t h v c m₀ pc e)
  | succ n ih =>
    have earlier : (b.text w n).Exec m (b.memory m n) (b.ticks n) :=
      @ih (fun j hj=>readOnly j (Nat.lt_succ_of_lt hj)) (by omega)
    have operands : (b.expr n).Fits w (b.out+n) :=
      (b.expr n).fits_of_inputEnd ((readOnly n (Nat.lt_succ_self n)).trans
        (Nat.le_add_right b.out n)) (by omega)
    exact @Procedure.Exec.then w (b.text w n) (scan w (b.out+n) 1 (b.expr n))
      m (b.memory m n) (b.memory m (n+1)) (b.ticks n) (4+1*(2*(b.expr n).work+4))
      (@earlier) (@scan_exec w (b.out+n) 1 (b.expr n) (b.memory m n) operands (by omega))

theorem before (b : Batch) (m : Memory w) (n a : ℕ) (prior : a<b.out) : b.memory m n a=m a := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    exact (ProtocolRAMGeneratedWrite.frame_image (b.out+n) 1 (b.expr n) (b.memory m n) a
      (.inl (by omega))).trans ih

theorem after (b : Batch) (m : Memory w) (n a : ℕ) (late : b.out+n≤a) : b.memory m n a=m a := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    exact (ProtocolRAMGeneratedWrite.frame_image (b.out+n) 1 (b.expr n) (b.memory m n) a
      (.inr late)).trans (ih (by omega))

theorem read (b : Batch) (m : Memory w) (n i : ℕ) (live : i<n) (fit : (b.expr i).Fits w b.out) :
    b.memory m n (b.out+i)=(b.expr i).eval m 0 := by
  induction n with
  | zero=>omega
  | succ n ih=>
    by_cases last : i=n
    · subst n
      exact (ProtocolRAMGeneratedWrite.read_image (b.out+i) 1 (b.expr i) (b.memory m i) (0:Fin 1)).trans
        (eval_below (b.expr i) 0 m (b.memory m i) fit (b.before m i))
    · exact (ProtocolRAMGeneratedWrite.frame_image (b.out+n) 1 (b.expr n) (b.memory m n) (b.out+i)
        (.inl (by omega))).trans (ih (by omega))

theorem time (b : Batch) (n C : ℕ) (cost : ∀j<n,(b.expr j).work≤C) :
    b.ticks n≤4+n*(8+2*C) := by
  induction n with
  | zero=>simp [ticks]
  | succ n ih=>
    have prior:=ih (fun j h=>cost j (by omega))
    have last:=cost n (by omega)
    calc
      b.ticks (n+1) = b.ticks n + (4+1*(2*(b.expr n).work+4)) := rfl
      _ ≤ (4+n*(8+2*C))+(8+2*C) := Nat.add_le_add prior (by omega)
      _ = 4+(n+1)*(8+2*C) := by rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
end Batch
end Hierarchy.DescentBaseProfile.DepthRAM

end OAI
