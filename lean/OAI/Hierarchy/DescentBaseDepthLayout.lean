import OAI.Hierarchy.DescentBaseDepthBatch

namespace OAI
/-! # Public address layout of the native smoothed-depth computation -/
namespace Hierarchy.DescentBaseProfile.DepthRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators
structure Layout where
  H : ℕ
  N : ℕ
  Δ : ℕ
  hostBits : ℕ
  degreeBits : ℕ
  weights : ℕ
  edges : ℕ
  start : ℕ
  S : ℕ
  g : ℕ
  lo : ℕ
  M : ℕ

namespace Layout
variable (L : Layout) {w cut : ℕ}

def base (j : ℕ) := L.start+j*2^L.hostBits
def sums : Batch := ⟨L.base 0,fun v=>rowSum (L.weights+v*L.N) L.N⟩
def seed (w : ℕ) : Batch := ⟨L.base 1,fun v=>probe w (L.base 0+v) L.lo L.M 0 L.S⟩
def peer (s v q : ℕ) : Expr := if q<L.Δ then
  neighbor L.H (L.base (s+1)) L.hostBits (L.edges+v*L.Δ+q) L.g else .lit 0
def step (s : ℕ) : Batch := ⟨L.base (s+2),fun v=>
  maximum (cell (L.base 1+v)) (tournament (L.peer s v) L.degreeBits 0)⟩

structure Fits (w : ℕ) : Prop where
  sites : L.H≤2^L.hostBits
  degree : L.Δ≤2^L.degreeBits
  weights : L.weights+L.H*L.N≤L.start
  edges : L.edges+L.H*L.Δ≤L.start
  space : L.base (L.M+2)<2^w
  propagation : L.g<2^w
  depths : max L.lo L.M<2^w

theorem base_succ (j : ℕ) : L.base (j+1)=L.base j+2^L.hostBits := by simp [base,Nat.succ_mul,Nat.add_assoc]
theorem base_mono {i j : ℕ} (h : i≤j) : L.base i≤L.base j := Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
theorem sum_span (safe : L.Fits w) {v : ℕ} (site : v<L.H) : (L.sums.expr v).inputEnd≤L.sums.out := by
  have h:=Nat.mul_le_mul_right L.N (show v+1≤L.H from site)
  simp only [Nat.succ_mul] at h
  exact (rowSum_bounds _ _).2.trans (by dsimp [sums,base];have:=safe.weights;omega)
theorem seed_span (safe : L.Fits w) {v : ℕ} (site : v<L.H) : ((L.seed w).expr v).inputEnd≤(L.seed w).out := by
  have u := site.trans_le safe.sites
  exact (probe_bounds _ _ _ _ _ _).2.trans (by simp [seed,base];omega)

theorem tournament_end (f : ℕ→Expr) (h : ∀i,(f i).inputEnd≤cut) (s i : ℕ) :
    (tournament f s i).inputEnd≤cut := by
  induction s generalizing i with
  | zero=>exact h i
  | succ s ih=>simp [tournament,maximum,Expr.inputEnd,ih]

theorem step_span (safe : L.Fits w) {v : ℕ} (site : v<L.H) (s : ℕ) :
    ((L.step s).expr v).inputEnd≤(L.step s).out := by
  have s1:=L.base_mono (show 1≤ s+1 by omega)
  have start:=L.base_mono (Nat.zero_le (s+2))
  have st : L.start≤L.base (s+2) := by simp [base]
  have later := L.base_succ (s+1)
  have next : L.base (s+1)+2^L.hostBits=L.base (s+2) := later.symm
  have h0 : (cell (L.base 1+v)).inputEnd≤L.base (s+2) := by
    rw [cell_end];have := site.trans_le safe.sites;omega
  have hf (q : ℕ) : (L.peer s v q).inputEnd≤L.base (s+2) := by
    have h:=Nat.mul_le_mul_right L.Δ (show v+1≤L.H from site)
    simp only [Nat.succ_mul] at h
    unfold peer
    split
    · next hq =>
        have ep : L.edges+v*L.Δ+q+1≤L.base (s+2) := by have:=safe.edges;omega
        simp [neighbor,decrease,Expr.inputEnd,cell_end,Bank.size,ep,next]
    · exact Nat.zero_le _
  have ht:=tournament_end (L.peer s v) hf L.degreeBits 0
  simp only [step,maximum,Expr.inputEnd,max_le_iff]
  exact ⟨⟨h0,ht⟩,⟨ht,h0⟩⟩

def cpu (L : Layout) (w : ℕ) : ℕ→Procedure w
  | 0=>(L.sums.text w L.H).seq ((L.seed w).text w L.H)
  | s+1=>(L.cpu w s).seq ((L.step s).text w L.H)

def clocks (L : Layout) (w : ℕ) : ℕ→ℕ
  | 0=>L.sums.ticks L.H+(L.seed w).ticks L.H
  | s+1=>L.clocks w s+(L.step s).ticks L.H

def output (L : Layout) {w : ℕ} (m : Memory w) : ℕ→Memory w
  | 0=>(L.seed w).memory (L.sums.memory m L.H) L.H
  | s+1=>(L.step s).memory (L.output m s) L.H

theorem end_room (safe : L.Fits w) {j : ℕ} (span : j<L.M+2) : L.base j+L.H<2^w := by
  calc
    L.base j + L.H ≤ L.base j + 2^L.hostBits := Nat.add_le_add_left safe.sites _
    _ = L.base (j+1) := (L.base_succ j).symm
    _ ≤ L.base (L.M+2) := L.base_mono span
    _ < 2^w := safe.space

theorem execute (m : Memory w) (safe : L.Fits w) (s : ℕ) (hs : s≤L.M) :
    (L.cpu w s).Exec m (L.output m s) (L.clocks w s) := by
  induction s with
  | zero =>
    exact Procedure.Exec.then (L.sums.run m _ (fun _ h=>L.sum_span safe h) (L.end_room safe (by omega)))
      ((L.seed w).run _ _ (fun _ h=>L.seed_span safe h) (L.end_room safe (by omega)))
  | succ s ih =>
    exact Procedure.Exec.then (ih (by omega)) ((L.step s).run _ _
      (fun _ h=>L.step_span safe h s) (L.end_room safe (by omega)))

theorem cheap (w s : ℕ) : CheapCode (L.cpu w s) := by
  induction s with
  | zero => exact cheap_seq (@Batch.cheap L.sums w L.H) (@Batch.cheap (L.seed w) w L.H)
  | succ s ih => exact cheap_seq ih (@Batch.cheap (L.step s) w L.H)

theorem static (m : Memory w) (s a : ℕ) (src : a<L.start) : L.output m s a=m a := by
  have prior (j : ℕ) : a<L.base j := src.trans_le (Nat.le_add_right ..)
  induction s with
  | zero=>exact ((L.seed w).before _ _ _ (prior 1)).trans (L.sums.before _ _ _ (prior 0))
  | succ s ih=>exact ((L.step s).before _ _ _ (prior _)).trans ih

end Layout
end Hierarchy.DescentBaseProfile.DepthRAM

end OAI
