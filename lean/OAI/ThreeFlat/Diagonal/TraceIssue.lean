import OAI.ThreeFlat.Diagonal.TraceIssueCore

namespace OAI
/-! # Correctness and gate counts for the instruction-local checks -/

namespace ThreeFlat.Diagonal.TraceIssue

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TraceBanks TraceWords

variable {w p r k : ℕ}

private theorem bits_narrow (x : Word (w+1)) (j : Fin w) :
    bits (narrow x) j = bits x j.castSucc := by simp [bits, narrow, j.isLt]

private theorem snoc_word (x : Word w) (b : Bool) :
    Fin.snoc (bits x) b = bits (if b then privateAddress x else wide x) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    cases b <;> simp [bits, wide, privateAddress, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow x.isLt]
  | cast j =>
    cases b <;> simp [bits, wide, privateAddress, Nat.testBit_two_pow_add_gt j.isLt]

variable (M : Machine w p r k) (s : Snapshot w p r) (q : Proposal (w+1) (Snapshot w p r))

private theorem go_true (pc : E w p r) (es : Fin r → Fin w → E w p r)
    (n : Fin p) (regs : Fin r → Word w)
    (hc : pc.eval (valuation M s q) = true ↔ (q.after s).pc = n)
    (he : ∀ i j, (es i j).eval (valuation M s q) = bits (regs i) j) :
    (go pc es).eval (valuation M s q) = true ↔
      q.after s = ⟨n,s.persistent,regs⟩ := by
  have hs := sameWord_at (fun j => .input (.nextState j)) (vst (p:=p) (r:=r))
    (valuation M s q) (fun _ => rfl) (fun _ => rfl)
  have hr (i : Fin r) := sameWord_at (fun j => .input (.nextReg i j)) (es i)
    (valuation M s q) (fun _ => rfl) (he i)
  simp only [go, Expr.eval, Bool.and_eq_true, stateOk, hc, hs, regOk, allBits_true, hr]
  obtain ⟨pc',st',regs'⟩ := q.after s
  simp [funext_iff]

private theorem put_true (n : Fin p) (dst : Fin r) (v : Fin w → E w p r)
    (a : Word w) (h : ∀ j, (v j).eval (valuation M s q) = bits a j) :
    (put n dst v).eval (valuation M s q) = true ↔ q.after s = s.put n dst a := by
  apply go_true M s q _ _ n (Function.update s.reg dst a)
  · simp [vpc, Expr.eval, valuation]
  · intro i j
    by_cases e : i = dst
    · subst i
      simpa using h j
    · simp [Function.update_of_ne e, vr, Expr.eval, valuation]

private theorem go_keep_true (pc : E w p r) (n : Fin p)
    (hc : pc.eval (valuation M s q) = true ↔ (q.after s).pc = n) :
    (go pc vr).eval (valuation M s q) = true ↔ q.after s = {s with pc := n} :=
  go_true M s q _ _ _ _ hc (fun _ _ => rfl)

private theorem addrOk_true (bank : Bool) (addr : Fin r) :
    (addrOk bank addr).eval (valuation M s q) = true ↔
      q.address = if bank then privateAddress (s.reg addr) else wide (s.reg addr) := by
  apply sameWord_at
  · intro j; rfl
  · intro j
    rw [← snoc_word]
    induction j using Fin.lastCases <;> simp [vr, Expr.eval, valuation]

private theorem dataOk_true (src : Fin r) :
    (dataOk src).eval (valuation M s q) = true ↔ q.data = wide (s.reg src) := by
  apply sameWord_at
  · intro j; rfl
  · intro j
    have h := congrFun (snoc_word (s.reg src) false) j
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [← h]
    induction j using Fin.lastCases <;> simp [vr, Expr.eval, valuation]

private theorem tag_true (t : Tag) :
    (tag t).eval (valuation M s q) = true ↔ q.tag = t := by simp [tag, Expr.eval, valuation]

private theorem vpc_true (i : Fin p) :
    (vpc i).eval (valuation M s q) = true ↔ (q.after s).pc = i := by simp [vpc, Expr.eval, valuation]

private theorem tick_true (n : Fin p) (dst : Fin r) (v : Fin w → E w p r)
    (a : Word w) (h : ∀ j, (v j).eval (valuation M s q) = bits a j) :
    (tick n dst v).eval (valuation M s q) = true ↔ q = .move .tick (s.put n dst a) := by
  simp only [tick, Expr.eval, Bool.and_eq_true, tag_true, put_true M s q n dst v a h]
  cases q with
  | halt res => cases res <;> simp [Proposal.tag]
  | move e after => cases e <;> simp [Proposal.tag, Proposal.after]; split <;> simp_all

private theorem load_true (bank : Bool) (dst addr : Fin r) (n : Fin p) :
    (load bank dst addr n).eval (valuation M s q) = true ↔
      ∃ v, q = .move (.read (if bank then privateAddress (s.reg addr) else wide (s.reg addr)) v)
        (s.put n dst (narrow v)) := by
  simp only [load, Expr.eval, Bool.and_eq_true, tag_true, addrOk_true,
    put_true M s q n dst (fun j => .input (.data j.castSucc)) (narrow q.data) (fun j => (bits_narrow q.data j).symm)]
  cases q with
  | halt res => cases res <;> simp [Proposal.tag]
  | move e after => cases e <;> simp [Proposal.tag, Proposal.address, Proposal.data, Proposal.after]; split <;> simp_all

private theorem store_true (bank : Bool) (addr src : Fin r) (n : Fin p) :
    (store bank addr src n).eval (valuation M s q) = true ↔
      q = .move (.write (if bank then privateAddress (s.reg addr) else wide (s.reg addr)) (wide (s.reg src)))
        {s with pc := n} := by
  simp only [store, Expr.eval, Bool.and_eq_true, tag_true, addrOk_true, dataOk_true,
    go_keep_true M s q _ n (vpc_true ..)]
  cases q with
  | halt res => cases res <;> simp [Proposal.tag]
  | move e after =>
    cases e <;> simp [Proposal.tag, Proposal.address, Proposal.data, Proposal.after, and_assoc]; split <;> simp_all

private theorem tick_keep (n : Fin p) (pc : E w p r)
    (hc : pc.eval (valuation M s q) = true ↔ (q.after s).pc = n) :
    ((tag .tick).and (go pc vr)).eval (valuation M s q) = true ↔ q = .move .tick {s with pc := n} := by
  simp only [Expr.eval, Bool.and_eq_true, tag_true, go_keep_true M s q _ _ hc]
  cases q with
  | halt res => cases res <;> simp [Proposal.tag]
  | move e after => cases e <;> simp [Proposal.tag, Proposal.after]; split <;> simp_all

theorem instruction_true (i : Fin p) :
    (instruction M.publicData i (M.code i)).eval (valuation M s q) = true ↔
      Follows (step M.publicData s (M.code i)) q := by
  cases h : M.code i with
  | constant dst v n => exact tick_true M s q n dst _ v fun _ => by simp [Expr.eval, valuation, h, aluWord]
  | publicWord dst c n => exact tick_true M s q n dst _ (M.publicData c) fun _ => by simp [Expr.eval, valuation, h, aluWord]
  | stateWord dst n => exact tick_true M s q n dst _ s.persistent fun _ => rfl
  | copy dst src n => exact tick_true M s q n dst _ (s.reg src) fun _ => rfl
  | binary op dst x y n =>
    exact tick_true M s q n dst (fun j => .input (.alu i j)) (op.eval (s.reg x) (s.reg y))
      fun j => by simp [Expr.eval, valuation, h, aluWord]
  | loadPrivate dst addr n => exact load_true M s q true dst addr n
  | storePrivate addr src n => exact store_true M s q true addr src n
  | readExternal dst addr n => exact load_true M s q false dst addr n
  | writeExternal addr src n => exact store_true M s q false addr src n
  | jumpEq x y yes no =>
    apply tick_keep
    by_cases hh : s.reg x = s.reg y <;> simp [valuation, h, compareBit, hh, Expr.eval, vpc]
  | jumpLt x y yes no =>
    apply tick_keep
    by_cases hh : s.reg x < s.reg y <;> simp [valuation, h, compareBit, hh, Expr.eval, vpc]
  | choose yes no =>
    simp only [instruction, Expr.eval, Bool.or_eq_true, Bool.and_eq_true, tag_true,
      go_keep_true M s q _ no (vpc_true ..), go_keep_true M s q _ yes (vpc_true ..),
      step, Follows, Bool.exists_bool]
    cases q with
    | halt out => cases out <;> simp [Proposal.tag]
    | move e aft =>
      cases e <;> simp [Proposal.tag, Proposal.after]; split <;> simp_all
  | returnState src =>
    simp only [instruction, Expr.eval, Bool.and_eq_true, tag_true, dataOk_true, step, Follows]
    cases q with
    | halt out => cases out <;> simp [Proposal.tag, Proposal.data]
    | move e aft => cases e <;> simp [Proposal.tag]; split <;> simp_all
  | accept =>
    simp only [instruction, tag_true, step, Follows]
    cases q with
    | halt out => cases out <;> simp [Proposal.tag]
    | move e aft => cases e <;> simp [Proposal.tag]; split <;> simp_all
  | reject => simp [instruction, Expr.eval, step, Follows]

/-- A local test is satisfied precisely by a legal row of the exposed machine. -/
theorem issue_true :
    (issue M).eval (valuation M s q) = true ↔ Follows ((exposed M).step s) q := by
  unfold issue
  rw [TraceFetch.fetch_eval _ _ _ s.pc (fun _ => rfl)]
  exact instruction_true M s q s.pc

/-- One BooleanTranscript circuit accepts exactly the fetched step on its local ports. -/
noncomputable def issueFrame (M : Machine w p r k) : Computability.VPVNP.VerifierNetwork.Frame (Port w p r) Unit :=
  (Computability.VPVNP.VerifierNetwork.Frame.initial id).step fun _ => issue M

theorem circuit_true :
    ((issueFrame M).circuit ()).eval (valuation M s q) = true ↔ Follows ((exposed M).step s) q := by
  have he : (Computability.VPVNP.VerifierNetwork.Frame.initial id).eval (valuation M s q) = valuation M s q :=
    funext fun _ => by simp
  simpa [issueFrame, he] using issue_true M s q

private def wordBudget (w : ℕ) := w * 10 + 1
private def goBudget (w r : ℕ) := 8 + wordBudget w + (r * (wordBudget w + 1) + 1) + 2

private theorem wordBudget_le {n : ℕ} (a b : Fin n → E w p r)
    (ha : ∀ i, (a i).size ≤ 1) (hb : ∀ i, (b i).size ≤ 1) :
    (sameWord a b).size ≤ wordBudget n := sameWord_size_le _ _ ha hb

private theorem go_size_le (pc : E w p r) (regs : Fin r → Fin w → E w p r)
    (hc : pc.size ≤ 8) (hr : ∀ i j, (regs i j).size ≤ 1) :
    (go pc regs).size ≤ goBudget w r := by
  have hs : (stateOk (w:=w) (p:=p) (r:=r)).size ≤ wordBudget w := wordBudget_le _ _ (fun _ => le_rfl) (fun _ => le_rfl)
  have hg : (regOk regs).size ≤ r * (wordBudget w + 1) + 1 :=
    allBits_size_le _ (fun i => wordBudget_le _ _ (fun _ => le_rfl) (hr i))
  simp only [go, Expr.size, goBudget]
  omega

private theorem put_size_le (n : Fin p) (dst : Fin r) (v : Fin w → E w p r)
    (hv : ∀ j, (v j).size ≤ 1) : (put n dst v).size ≤ goBudget w r := by
  apply go_size_le _ _ (by change 1 ≤ 8; decide)
  intro i j
  by_cases h : i = dst
  · subst i; simpa using hv j
  · simp [Function.update_of_ne h, vr, Expr.size]

private theorem tick_size_le (n : Fin p) (dst : Fin r) (v : Fin w → E w p r)
    (hv : ∀ j, (v j).size ≤ 1) : (tick n dst v).size ≤ goBudget w r + 2 := by
  have := put_size_le n dst v hv
  simp only [tick, tag, Expr.size]
  omega

private theorem snoc_vr_size_le (src : Fin r) (b : Bool) (j : Fin (w+1)) :
    ((Fin.snoc (α := fun _ => E w p r) (vr (w:=w) (p:=p) src) (.const b)) j).size ≤ 1 := by
  induction j using Fin.lastCases <;> simp [vr, Expr.size]

private theorem addrOk_size_le (b : Bool) (a : Fin r) :
    (addrOk (p:=p) (w:=w) b a).size ≤ wordBudget (w+1) :=
  wordBudget_le _ _ (fun _ => le_rfl) (snoc_vr_size_le a b)

private theorem dataOk_size_le (a : Fin r) :
    (dataOk (p:=p) (w:=w) a).size ≤ wordBudget (w+1) :=
  wordBudget_le _ _ (fun _ => le_rfl) (snoc_vr_size_le a false)

private theorem load_size_le (bank : Bool) (dst addr : Fin r) (n : Fin p) :
    (load (w:=w) bank dst addr n).size ≤ goBudget w r + wordBudget (w+1) + 3 := by
  have h := put_size_le n dst (fun j : Fin w => .input (.data j.castSucc)) (fun _ => le_rfl)
  have ha := addrOk_size_le (p:=p) (w:=w) bank addr
  simp only [load, tag, Expr.size]
  omega

private theorem store_size_le (bank : Bool) (addr src : Fin r) (n : Fin p) :
    (store (w:=w) bank addr src n).size ≤ goBudget w r + 2 * wordBudget (w+1) + 4 := by
  have hg := go_size_le (w:=w) (r:=r) (vpc n) vr (by change 1 ≤ 8; decide) (fun _ _ => le_rfl)
  have ha := addrOk_size_le (p:=p) (w:=w) bank addr
  have hd := dataOk_size_le (p:=p) (w:=w) src
  simp only [store, tag, Expr.size]
  omega

/-- Each instruction uses a number of formula gates linear in the register-file width,
in addition to the arithmetic and comparison gates supplying that instruction's ports. -/
def instructionBudget (w r : ℕ) := 2 * goBudget w r + 2 * wordBudget (w+1) + 10

theorem instruction_size_le (pub : Fin k → Word w) (i : Fin p) (op : Instr w p r k) :
    (instruction pub i op).size ≤ instructionBudget w r := by
  unfold instructionBudget
  have h₁ := fun (n : Fin p) (dst : Fin r) (v : Fin w → E w p r) (hv : ∀ j, (v j).size ≤ 1) =>
    tick_size_le n dst v hv
  have hg (n : Fin p) := go_size_le (w:=w) (r:=r) (vpc n) vr (by change 1 ≤ 8; decide) (fun _ _ => le_rfl)
  have hj (yes no : Fin p) := go_size_le (w:=w) (r:=r) (Expr.mux (.input (.cmp i)) (vpc yes) (vpc no)) vr
    (by change 8 ≤ 8; exact le_rfl) (fun _ _ => le_rfl)
  cases op with
  | constant dst v n | publicWord dst v n | stateWord dst n | copy dst v n | binary _ dst _ _ n =>
    apply (h₁ n dst _ (fun _ => le_rfl)).trans
    omega
  | loadPrivate dst addr n | readExternal dst addr n =>
    apply (load_size_le _ dst addr n).trans
    omega
  | storePrivate addr src n | writeExternal addr src n =>
    apply (store_size_le _ addr src n).trans
    omega
  | jumpEq x y yes no | jumpLt x y yes no =>
    simp only [instruction, tag, Expr.size]
    have := hj yes no
    omega
  | choose yes no =>
    simp only [instruction, tag, Expr.size]
    have := hg yes
    have := hg no
    omega
  | returnState src =>
    simp only [instruction, tag, Expr.size]
    have := dataOk_size_le (p:=p) (w:=w) src
    omega
  | accept | reject => simp [instruction, tag, Expr.size]

theorem issue_size_le :
    (issue M).size ≤ p * (instructionBudget w r + 3) + 1 := by
  calc
    (issue M).size ≤ p * (1 + instructionBudget w r + 2) + 1 :=
      TraceFetch.fetch_size_le (fun i => Expr.input (Port.pc (w:=w) (r:=r) i))
        (fun i => instruction M.publicData i (M.code i)) (c:=1) (fun _ => le_rfl)
        (fun i => instruction_size_le _ _ _)
    _ = _ := by ring

theorem circuitSize_le :
    (issueFrame M).circuitSize () ≤ 4 * (p * (instructionBudget w r + 3) + 1) := by
  apply ((issueFrame M).circuitSize_le ()).trans
  apply Nat.mul_le_mul_left
  simpa [issueFrame] using
    (Computability.VPVNP.VerifierNetwork.Frame.step_size_le
      (Computability.VPVNP.VerifierNetwork.Frame.initial (id : Port w p r → Port w p r))
      (fun _ : Unit => issue M) _ (fun _ => issue_size_le M))

end ThreeFlat.Diagonal.TraceIssue

end OAI
