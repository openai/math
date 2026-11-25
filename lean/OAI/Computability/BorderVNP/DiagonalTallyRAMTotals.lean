import OAI.Computability.BorderVNP.DiagonalTallyRAMSum

/-! # Writing every global parameter and gadget total

The common broadcast stores teams in increasing order and the coordinates of each team
contiguously. This deterministic outer loop runs the strided scan once per coordinate.
Its output is an ordinary word array at distinct addresses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Select the current column and zero the accumulator and team counter. -/
def startColumn : Code := .block [.binary .add 48 59 56, .constant 51 0, .constant 52 0]

/-- Write the completed global sum at its own coordinate. -/
def finishColumn : Code := .block [.binary .add 54 58 56, .store 54 52, .binary .add 56 56 63]

/-- Scan one complete team column, store it and advance the coordinate index. -/
def columnBody : Code := .seq startColumn (.seq sumColumn finishColumn)

/-- Collect all parameter exponents and gadget multiplicities. -/
def aggregate : Code := .whileLt 56 49 columnBody

/-- Addresses and dimensions for a common broadcast and its totals. -/
structure TotalsFrame where
  /-- Number of parameter and gadget coordinates combined. -/
  dim : ℕ
  /-- Number of teams. -/
  teams : ℕ
  /-- Word address of the first decoded subtotal. -/
  claims : ℕ
  /-- Word address of the first global total. -/
  totals : ℕ

/-- The invariant registers for the aggregation loop. -/
def TotalsFrame.loaded (f : TotalsFrame) (s : Bank w) : Prop :=
  s 49 = word w f.dim ∧ s 50 = word w f.teams ∧ s 58 = word w f.totals ∧
    s 59 = word w f.claims ∧ s 63 = 1

/-- Addresses, counters, and post-loop pointer values fit in one machine word. -/
def TotalsFrame.fits (f : TotalsFrame) (w : ℕ) : Prop :=
  f.claims+f.dim*f.teams+f.dim < 2^w ∧ f.totals+f.dim < 2^w ∧ f.teams < 2^w

/-- The decoded broadcast in shared word memory. -/
def TotalsFrame.contains (f : TotalsFrame) (a : ℕ → ℕ → Word w) (m : Memory w) : Prop :=
  ∀ i < f.teams, ∀ j < f.dim, m (f.claims+j+f.dim*i) = a i j

private theorem startColumn_effect (f : TotalsFrame) (s : Bank w) (m : Memory w)
    (h : f.loaded s) {j : ℕ} (hj : s 56 = word w j) :
    let e := effect false s m startColumn
    f.loaded e.bank ∧ e.bank 56 = word w j ∧ e.bank 48 = word w (f.claims+j) ∧
    e.bank 51 = 0 ∧ e.bank 52 = 0 ∧ e.mem = m ∧ TraceOK e.trace [] 3 := by
  obtain ⟨h49,h50,h58,h59,h63⟩ := h
  simp [startColumn, Code.block, effect, BinaryOp.eval, TotalsFrame.loaded, Function.update,
    TraceOK, tick, h49,h50,h58,h59,h63,hj]

private theorem finishColumn_effect (f : TotalsFrame) (s : Bank w) (m : Memory w)
    (h : f.loaded s) {j : ℕ} (hj : s 56 = word w j) (haddr : f.totals+j < 2^w) :
    let e := effect false s m finishColumn
    f.loaded e.bank ∧ e.bank 56 = word w (j+1) ∧
    e.mem = Function.update m (f.totals+j) (s 52) ∧ TraceOK e.trace [] 3 := by
  obtain ⟨h49,h50,h58,h59,h63⟩ := h
  have hx : (word w f.totals+word w j).val = f.totals+j := by
    rw [← word_add,word_val _ _ haddr]
  simp [finishColumn, Code.block, effect, BinaryOp.eval, TotalsFrame.loaded, Function.update,
    TraceOK, tick,h49,h50,h58,h59,h63,hj,hx]

private theorem columnBody_runs (f : TotalsFrame) (hfit : f.fits w)
    (s : Bank w) (m : Memory w) (h : f.loaded s) {j : ℕ} (hj : s 56 = word w j) (hd : j < f.dim) :
    ∃ es t, Runs pub macros columnBody s m es t
      (Function.update m (f.totals+j) (stridedSum m f.dim (f.claims+j) f.teams)) ∧
      TraceOK es [] (5*f.teams+7) ∧ f.loaded t ∧ t 56 = word w (j+1) := by
  obtain ⟨hf₁,hf₂,hf₃⟩ := hfit
  let e := effect false s m startColumn
  obtain ⟨hl,hj',hptr,hctr,hacc,hm,hTrace⟩ := startColumn_effect f s m h hj
  have hs := effect_runs pub macros false s m startColumn (by decide)
  change Runs pub macros startColumn s m e.trace e.bank e.mem at hs
  change e.mem = m at hm
  rw [hm] at hs
  obtain ⟨fs,t,run,ft,_,_,h52,frame⟩ :=
    sumColumn_runs (pub := pub) (macros := macros) f.teams 0 (f.claims+j) f.dim e.bank m
      (by omega) (by simpa using hf₃) hptr hl.1 (by simpa using hl.2.1)
      (by simpa using hctr) hl.2.2.2.2
  have stable : f.loaded t :=
    ⟨(frame 49 (by decide) (by decide) (by decide) (by decide)).trans hl.1,
    (frame 50 (by decide) (by decide) (by decide) (by decide)).trans hl.2.1,
    (frame 58 (by decide) (by decide) (by decide) (by decide)).trans hl.2.2.1,
    (frame 59 (by decide) (by decide) (by decide) (by decide)).trans hl.2.2.2.1,
    (frame 63 (by decide) (by decide) (by decide) (by decide)).trans hl.2.2.2.2⟩
  have hjt := (frame 56 (by decide) (by decide) (by decide) (by decide)).trans hj'
  let z := effect false t m finishColumn
  obtain ⟨hz,hzj,hzm,hzt⟩ := finishColumn_effect f t m stable hjt (by omega)
  have hr := effect_runs pub macros false t m finishColumn (by decide)
  change Runs pub macros finishColumn t m z.trace z.bank z.mem at hr
  change z.mem = _ at hzm
  rw [hzm, h52,hacc,zero_add] at hr
  refine ⟨_,_,.seq hs (.seq run hr), ?_, hz, hzj⟩
  rw [show 5*f.teams+7 = 3+((5*f.teams+1)+3) by omega]
  exact hTrace.append (ft.append hzt)

/-- Memory obtained by writing the indicated slice of the sum array. -/
def writeTotals (f : TotalsFrame) (a : ℕ → Word w) (m : Memory w) (j : ℕ) : ℕ → Memory w
  | 0 => m
  | len+1 => writeTotals f a (Function.update m (f.totals+j) (a j)) (j+1) len

/-- The complete aggregation has one actual returning run with a fixed linear tick bound
in the number of broadcast subtotals. It materializes their word sums coordinatewise. -/
theorem aggregate_runs (f : TotalsFrame) (hfit : f.fits w)
    (hsep : f.claims+f.dim*f.teams ≤ f.totals)
    (data : ℕ → ℕ → Word w) (j len : ℕ) (hjl : j+len = f.dim)
    (s : Bank w) (m : Memory w) (h : f.loaded s) (hj : s 56 = word w j)
    (ha : f.contains data m) :
    ∃ es t, Runs pub macros aggregate s m es t
      (writeTotals f (fun c => ∑ i : Fin f.teams, data i.val c) m j len) ∧
      TraceOK es [] ((5*f.teams+8)*len+1) ∧ f.loaded t ∧ t 56 = word w f.dim := by
  induction len generalizing j s m with
  | zero =>
    have hjd : j = f.dim := by omega
    refine ⟨_,_,.whileDone (by rw [hj,h.1,hjd]; simp), ?_, h, hjd ▸ hj⟩
    simp [TraceOK, tick]
  | succ len ih =>
    have hd : j < f.dim := by omega
    have hg : s 56 < s 49 := by
      change (s 56).val < (s 49).val
      rw [hj,h.1,word_val _ _ (by have := hfit.2.1; omega),
        word_val _ _ (by have := hfit.2.1; omega)]
      exact hd
    obtain ⟨es,t,hr,ht,hl,htj⟩ := columnBody_runs (pub := pub) (macros := macros) f hfit s m h hj hd
    have he : stridedSum m f.dim (f.claims+j) f.teams = ∑ i : Fin f.teams, data i.val j := by
      rw [stridedSum_eq]
      exact Finset.sum_congr rfl fun i _ => ha i i.isLt j hd
    rw [he] at hr
    let m' := Function.update m (f.totals+j) (∑ i : Fin f.teams, data i.val j)
    have ha' : f.contains data m' := by
      intro i hi c hc
      have hlt : f.claims+c+f.dim*i < f.totals+j := by
        have hh := Nat.mul_le_mul_left f.dim (Nat.succ_le_of_lt hi)
        rw [Nat.mul_succ] at hh
        omega
      exact (Function.update_of_ne hlt.ne ..).trans (ha i hi c hc)
    obtain ⟨fs,u,loop,ft,hu,uj⟩ := ih (j+1) (by omega) t m' hl htj ha'
    refine ⟨_,_, .whileStep hg hr loop, ?_, hu, uj⟩
    rw [show (5*f.teams+8)*(len+1)+1 =
      (5*f.teams+7+((5*f.teams+8)*len+1))+1 by ring]
    exact (ht.append ft).cons_tick

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
