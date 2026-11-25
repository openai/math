import OAI.Hierarchy.ProbeStageCompactWindow
import OAI.Hierarchy.ProbeStageProgramSize
import OAI.Hierarchy.ProbeStageCheap

namespace OAI
/-! # Fixed-size row transfers for the compact allocator loop -/

namespace Hierarchy.ProbeStage.Native.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr PhysicalPinsExpr
open private text_put from OAI.Hierarchy.ProbeStageProgramSize
open private basic put_good store_good from OAI.Hierarchy.ProbeStageCheap
open scoped Fin.CommRing
noncomputable section

def countSeq {w : ℕ} (p : ℕ → Procedure w) : ℕ → Procedure w
  | 0 => p 0
  | n+1 => (countSeq p n).seq (p (n+1))

theorem countSeq_exec {w : ℕ} (p : ℕ → Procedure w) (s : ℕ → Memory w) (t n : ℕ)
    (run : ∀ k≤ n,(p k).Exec (s k) (s (k+1)) t) :
    (countSeq p n).Exec (s 0) (s (n+1)) ((n+1)*t) := by
  induction n with
  | zero =>
    change (p 0).Exec (s 0) (s 1) (1*t)
    rw [Nat.one_mul]
    intro P R K M
    exact run 0 le_rfl M
  | succ n ih =>
    rw [Nat.succ_mul (n+1) t]
    intro P R K M
    exact Procedure.Exec.then (ih fun k hk=>run k (by omega)) (run _ le_rfl) M

theorem countSeq_cheap {w : ℕ} (p : ℕ → Procedure w) (n : ℕ) (hp : ∀ i≤ n,CheapCode (p i)) :
    CheapCode (countSeq p n) := by
  induction n with
  | zero => exact hp 0 le_rfl
  | succ n ih => exact cheap_seq (ih fun k hk=> hp k (by omega)) (hp _ le_rfl)

theorem countSeq_text {w : ℕ} (p : ℕ → Procedure w) (n C : ℕ) (hp : ∀ i≤ n,text (p i)=C) :
    text (countSeq p n)=(n+1)*C := by
  induction n with
  | zero => simpa only [countSeq,zero_add,one_mul] using hp 0 le_rfl
  | succ n ih =>
    rw [countSeq,text_seq,ih (fun k hk=> hp k (by omega)),hp _ le_rfl]
    exact (Nat.succ_mul _ _).symm

def pointer (b addr : ℕ) : Formula 1 := .op .add (.lit addr) (.load (.lit (b+6)))

theorem pointer_value {w : ℕ} (b addr dst i : ℕ) (m : Memory w)
    (room : b+6<2^w) (cur : m (b+6)=(i:Word w)) :
    WordStore.value dst (pointer b addr) m=((addr+i:ℕ):Word w) := by
  change (addr:Word w)+m ((b+6:ℕ):Word w).val=_
  rw [Fin.val_cast_of_lt room,cur,Nat.cast_add]

theorem pointer_put_cheap (w b a dst : ℕ) : CheapCode (WordStore.put w dst (pointer b a)) :=
  put_good (by simp [pointer,basic,allowed])

theorem pointer_put_text (w b a dst : ℕ) : text (WordStore.put w dst (pointer b a))=27 := by
  rw [text_put]; rfl

theorem load_put_cheap (w b a dst : ℕ) : CheapCode (WordStore.put w dst (.load (pointer b a))) :=
  put_good (by simp [pointer,basic,allowed])

theorem load_put_text (w b a dst : ℕ) : text (WordStore.put w dst (.load (pointer b a)))=31 := by
  rw [text_put]; rfl

theorem zero_put_cheap (w dst : ℕ) : CheapCode (WordStore.put w dst (.lit 0)) := put_good (f:=.lit 0) trivial
theorem zero_put_text (w dst : ℕ) : text (WordStore.put w dst (.lit 0))=15 := by rw [text_put]; rfl
theorem dynamic_cheap (w ptr src : ℕ) : CheapCode (RankUpdate.store w ptr src) := store_good w ptr src

variable {h d : ℕ}

private theorem window_bank (large : 4≤ h) (j k : ℕ) : base h+8≤ bankBase h d copies j k := by
  exact (window_before (d:=d) large j).trans (Nat.le_add_right ..)

theorem window_rank (large : 4≤ h) (j : Fin (rounds d)) (i : Fin (2^h)) (q : Fin 3) :
    base h+8 ≤ rankAddr h d j q i := (window_bank large j q).trans (Nat.le_add_right ..)

theorem window_room (hd : 1≤ d) (large : 4≤ h) (j : Fin (rounds d)) (i : Fin (2^h)) :
    base h+8<2^ramWidth h d := (window_rank large j i 0).trans_lt (by have := rank_room hd j 0 i;omega)

def srcBase {h : ℕ} (j : Fin (rounds d)) (q : Fin 6) : ℕ :=
  Fin.addCases (m:=3) (n:=3) (motive:=fun _=>ℕ)
    (fun k=>(blockBank h d copies j k).base) (fun k=>bankBase h d copies j k.val) q

def srcAddr (j : Fin (rounds d)) (i : Fin (2^h)) (q : Fin 6) := srcBase (h:=h) j q + i.val

@[simp] theorem srcAddr_arg (j : Fin (rounds d)) (i : Fin (2^h)) (q : Fin 3) :
    srcAddr j i (q.castAdd 3)=argumentAddr j i q := by simp [srcAddr,srcBase,argumentAddr]

@[simp] theorem srcAddr_rank (j : Fin (rounds d)) (i : Fin (2^h)) (q : Fin 3) :
    srcAddr j i (Fin.natAdd 3 q)=rankAddr h d j q i := by simp only [srcAddr,srcBase,rankAddr,Fin.addCases_right]

theorem source_facts (hd : 1≤ d) (large : 4≤ h) (j : Fin (rounds d)) (i : Fin (2^h)) (q : Fin 6) :
    base h+8≤ srcAddr j i q ∧ srcAddr j i q<2^ramWidth h d := by
  refine Fin.addCases (m:=3) (n:=3) (fun k=>?_) (fun k=>?_) q
  · rw [srcAddr_arg]
    refine ⟨?_,(argument_low j i k 0).trans (scratch_fits j 0)⟩
    have := window_bank (d:=d) large j 11
    change base h+8≤ bankBase h d copies j 11+k.val*2^h+i.val
    omega
  · rw [srcAddr_rank]
    exact ⟨window_rank large j i k,by have := rank_room hd j k i;omega⟩

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
