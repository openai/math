import OAI.Hierarchy.FactorCounterClear

namespace OAI
/-! # Fixed native compilation of the four-pass factor assignment -/

namespace Hierarchy.FactorBucketRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w : ℕ}

/-- Deterministic procedures can be composed while recording their exact
memory function at the boundary. -/
abbrev Computes (p : Procedure w) (f : Memory w → Memory w) (steps : ℕ) : Prop :=
  p.Spec (fun _=>True) (fun m m' => m'=f m) steps

theorem computes_seq {p q : Procedure w} {f g : Memory w → Memory w} {s t : ℕ}
    (a : Computes p f s) (b : Computes q g t) : Computes (p.seq q) (g ∘ f) (s+t) := by
  intro P R K M pc reg pub exit installed data c m entry pre
  obtain ⟨n,hn,out,mem,run,atExit,mid,h₁,h₂⟩ :=
    Procedure.Spec.seq (A:=p) (B:=q) a b (fun _ _ _=>trivial)
      M pc reg pub exit installed data c m entry pre
  exact ⟨n,hn,out,mem,run,atExit,h₂.trans (congrArg g h₁)⟩

theorem computes_rows (ops : List (Op 14 12))
    (step : Parameters w → Word w → Memory w → Memory w) (v : Parameters w)
    (n : ℕ) (fit : n<2^w) (count : v 0=(n:Word w))
    (rows : ∀ {R K : ℕ} (reg : Fin 14 ↪ Fin R) (pub : Fin 12 → Fin K) (V : Fin K → Word w)
      (state : Word w) (rs : Regs w R) (m : Memory w), Executes ops step reg pub V state rs m) :
    Computes (procedure ops v) (fun m=>iterRows step v m n) (3+n*(1+ops.length)) := by
  dsimp only [Computes,procedure,Procedure.Spec]
  intro P R K M pc reg pub exit installed data c m entry _
  have params : M.publicData ∘ pub = v := funext data
  have count' : M.publicData (pub 0)=(n:Word w) := (data 0).trans count
  obtain ⟨out,run,atExit⟩ := advance_rows ops step M pc reg pub exit installed n fit count'
    (rows reg pub M.publicData) c entry m
  refine ⟨_,le_rfl,out,_,run,atExit,?_⟩
  rw [params]

structure Banks where
  resources : ℕ
  thresholds : ℕ
  digits : ℕ
  keys : ℕ
  counts : ℕ
  output : ℕ

def passWords (width limit steps d radix ticks : ℕ) (b : Banks) := parameters width
  limit steps d radix ticks b.resources b.thresholds b.digits b.keys b.counts b.output

def compiler (width w N d T : ℕ) (b : Banks) : Procedure width :=
  let s := 20*(w+1)+1
  let v n := passWords width n s d (s+1) T b
  (((procedure digitOps (v (N*d*s))).seq (procedure keyOps (v (N*d)))).seq
    (procedure clearOps (v ((s+1)^d)))).seq (procedure ownerOps (v N))

def compiledMemory (width w N d T : ℕ) (b : Banks) (m : Memory width) : Memory width :=
  let s := 20*(w+1)+1
  let v n := passWords width n s d (s+1) T b
  let digits := iterRows digitStep (v (N*d*s)) m (N*d*s)
  let keys := iterRows keyStep (v (N*d)) digits (N*d)
  let cleared := iterRows clearStep (v ((s+1)^d)) keys ((s+1)^d)
  iterRows ownerStep (v N) cleared N

/-- A fixed ROM, with no program read from the resource rows. Exact instruction
counts include clearing all potential bucket counters. -/
theorem compiler_computes (width w N d T : ℕ) (b : Banks)
    (h₁ : N*d*(20*(w+1)+1)<2^width) (h₂ : N*d<2^width)
    (h₃ : (20*(w+1)+2)^d<2^width) (h₄ : N<2^width) :
    Computes (compiler width w N d T b) (compiledMemory width w N d T b)
      (3+N*d*(20*(w+1)+1)*24 + (3+N*d*22) + (3+(20*(w+1)+2)^d*7) + (3+N*16)) := by
  let s := 20*(w+1)+1
  let v n := passWords width n s d (s+1) T b
  intro P R K M pc reg pub exit installed data c m entry pre
  exact computes_seq (computes_seq (computes_seq
    (computes_rows digitOps digitStep (v _) _ h₁ rfl digit_trace)
    (computes_rows keyOps keyStep (v _) _ h₂ rfl key_trace))
    (computes_rows clearOps clearStep (v _) _ h₃ rfl clear_trace))
    (computes_rows ownerOps ownerStep (v _) _ h₄ rfl owner_trace)
    M pc reg pub exit installed data c m entry pre

end Hierarchy.FactorBucketRAM

end OAI
