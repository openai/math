import OAI.Hierarchy.DescentExteriorMismatch

namespace OAI
/-! # One physical program for the three grouped exterior passes and both witness checks -/
namespace Hierarchy.DescentExteriorFetch
open DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- A disagreement sets the low bit of one zero-scalar bin. The expensive
word comparison is a single allowed comparison instruction on the native trace. -/
def compare (g : Banks) (guess : Bank) : Expr :=
  .branch .eq (gather g) (.lookup guess .row) (.lit 0) (.lit 1)

def columns (g : Fin 3→Banks) (guess : Fin 2→Bank) : Fin 3→Expr :=
  ![compare (g 0) (guess 0),compare (g 1) (guess 1),gather (g 2)]

theorem compare_work (g : Banks) (b : Bank) : (compare g b).work=53 := rfl

def flight (w keyAt start n : ℕ) (kb : KeyBanks) (g : Fin 3→Banks) (guess : Fin 2→Bank) : Procedure w :=
  (((scan w keyAt n (joinKey kb)).seq (scan w start n (columns g guess 0))).seq
    (scan w (start+n) n (columns g guess 1))).seq (scan w (start+2*n) n (columns g guess 2))

def finalMem {w : ℕ} (keyAt start n : ℕ) (kb : KeyBanks) (g : Fin 3→Banks) (guess : Fin 2→Bank)
    (m : Memory w) :=
  ProtocolRAM.image (start+2*n) n (columns g guess 2) (ProtocolRAM.image (start+n) n (columns g guess 1)
    (ProtocolRAM.image start n (columns g guess 0) (ProtocolRAM.image keyAt n (joinKey kb) m)))

theorem cheap (w keyAt start n : ℕ) (kb : KeyBanks) (g : Fin 3→Banks) (guess : Fin 2→Bank) :
    CheapCode (flight w keyAt start n kb g guess) := by
  let a := scan w keyAt n (joinKey kb)
  let b := scan w start n (columns g guess 0)
  let c := scan w (start+n) n (columns g guess 1)
  let d := scan w (start+2*n) n (columns g guess 2)
  exact @cheap_seq w ((a.seq b).seq c) d
    (@cheap_seq w (a.seq b) c
      (@cheap_seq w a b (@scan_cheap w keyAt n (joinKey kb)) (@scan_cheap w start n (columns g guess 0)))
      (@scan_cheap w (start+n) n (columns g guess 1)))
    (@scan_cheap w (start+2*n) n (columns g guess 2))

private theorem monoFit {w start stop : ℕ} (e : Expr) (h : start≤ stop) (ok : e.Fits w start) : e.Fits w stop := by
  induction e with
  | row | lit => trivial
  | lookup b e ih=>exact ⟨⟨ok.1.1,ok.1.2.1,ok.1.2.2.trans h⟩,ih ok.2⟩
  | op _ _ _ l r=>exact ⟨l ok.1,r ok.2⟩
  | branch _ _ _ _ _ a b y n=>exact ⟨a ok.1,b ok.2.1,y ok.2.2.1,n ok.2.2.2⟩

private theorem four_scans {w : ℕ} (A B C D : Procedure w) {s₀ s₁ s₂ s₃ s₄ : Memory w}
    {a b c d total : ℕ} (ra : A.Exec s₀ s₁ a) (rb : B.Exec s₁ s₂ b)
    (rc : C.Exec s₂ s₃ c) (rd : D.Exec s₃ s₄ d) (price : a+b+c+d=total) :
    (((A.seq B).seq C).seq D).Exec s₀ s₄ total := by
  subst total
  have ab : (A.seq B).Exec s₀ s₂ (a+b) :=
    @Procedure.Exec.then w A B s₀ s₁ s₂ a b (@ra) (@rb)
  have abc : ((A.seq B).seq C).Exec s₀ s₃ (a+b+c) :=
    @Procedure.Exec.then w (A.seq B) C s₀ s₂ s₃ (a+b) c (@ab) (@rc)
  exact @Procedure.Exec.then w ((A.seq B).seq C) D s₀ s₃ s₄ (a+b+c) d (@abc) (@rd)

theorem run {w : ℕ} (keyAt start n : ℕ) (kb : KeyBanks) (g : Fin 3→Banks) (guess : Fin 2→Bank)
    (keyFit : (joinKey kb).Fits w keyAt) (below : keyAt+n≤ start)
    (ready : ∀s,(columns g guess s).Fits w start) (room : start+3*n<2^w) (m : Memory w) :
    (flight w keyAt start n kb g guess).Exec m (finalMem keyAt start n kb g guess m) (16+364*n) := by
  let keyM:=ProtocolRAM.image keyAt n (joinKey kb) m
  let first:=ProtocolRAM.image start n (columns g guess 0) keyM
  let second:=ProtocolRAM.image (start+n) n (columns g guess 1) first
  have a := @scan_exec w keyAt n (joinKey kb) m keyFit (by omega)
  have b := @scan_exec w start n (columns g guess 0) keyM (ready 0) (by omega)
  have c := @scan_exec w (start+n) n (columns g guess 1) first (monoFit _ (by omega) (ready 1)) (by omega)
  have d := @scan_exec w (start+2*n) n (columns g guess 2) second (monoFit _ (by omega) (ready 2)) (by omega)
  have hb : (columns g guess 0).work=53 := rfl
  have hc : (columns g guess 1).work=53 := rfl
  have hd : (columns g guess 2).work=43 := rfl
  refine @four_scans w (scan w keyAt n (joinKey kb)) (scan w start n (columns g guess 0))
    (scan w (start+n) n (columns g guess 1)) (scan w (start+2*n) n (columns g guess 2))
    m keyM first second (finalMem keyAt start n kb g guess m) _ _ _ _ _ (@a) (@b) (@c) (@d) ?_
  rw [joinKey_work,hb,hc,hd]
  omega

private theorem image_low {w : ℕ} (e : Expr) (m : Memory w) {out n a : ℕ} (low : a<out) :
    image out n e m a=m a := by simp [ProtocolRAM.image,fillSegment,not_le.mpr low]

private theorem image_high {w : ℕ} (e : Expr) (m : Memory w) {out n a : ℕ} (high : out+n≤a) :
    image out n e m a=m a := by simp [ProtocolRAM.image,fillSegment,not_lt.mpr high]

private theorem image_row {w : ℕ} (e : Expr) (m : Memory w) {out n : ℕ} (i : Fin n) :
    image out n e m (out+i.val)=e.eval m (i.val:Word w) := by
  simp [ProtocolRAM.image,fillSegment,show out+i.val<out+n by have:=i.isLt;omega,Nat.cast_add]

/-- All three real output columns refer back to the same primed RAM image.
The first two are failed-comparison flags. The third contains the reassembled row. -/
theorem read_column {w : ℕ} (keyAt start n : ℕ) (kb : KeyBanks) (g : Fin 3→Banks) (guess : Fin 2→Bank)
    (ready : ∀s,(columns g guess s).Fits w start) (m : Memory w) (s : Fin 3) (i : Fin n) :
    finalMem keyAt start n kb g guess m (start+s.val*n+i.val)=
      (columns g guess s).eval (image keyAt n (joinKey kb) m) (i.val:Word w) := by
  let keyM:=image keyAt n (joinKey kb) m
  let first:=image start n (columns g guess 0) keyM
  let second:=image (start+n) n (columns g guess 1) first
  have left (a : ℕ) (h : a<start) : first a=keyM a := image_low _ _ h
  have right (a : ℕ) (h : a<start) : second a=keyM a := (image_low _ _ (by omega)).trans (left a h)
  have hi:=i.isLt
  fin_cases s
  · change finalMem _ _ _ _ _ _ _ (start+0*n+i.val)=_
    rw [Nat.zero_mul,Nat.add_zero]
    unfold finalMem
    rw [image_low _ _ (by omega),image_low _ _ (by omega),image_row]
    rfl
  · change finalMem _ _ _ _ _ _ _ (start+1*n+i.val)=_
    rw [Nat.one_mul]
    unfold finalMem
    rw [image_low _ _ (by omega),image_row]
    exact eval_below _ _ keyM first (ready 1) left
  · change finalMem _ _ _ _ _ _ _ (start+2*n+i.val)=_
    unfold finalMem
    rw [image_row]
    exact eval_below _ _ keyM second (ready 2) right

end
end Hierarchy.DescentExteriorFetch

end OAI
