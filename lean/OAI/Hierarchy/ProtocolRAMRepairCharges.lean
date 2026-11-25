import OAI.Hierarchy.ProtocolRAMRepairCommit

namespace OAI
/-! # Signed event words for physical repair, restore, broadcast, and acquisition bills -/

namespace Hierarchy.ProtocolRAM.RepairHistogram
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {w n rows goods paths : ℕ}

/-- Two nonnegative words with opposite price coefficients, so negative external
catalyst cost is represented exactly at the same finite word width. -/
def ordinaryTerm (p : Columns) (s : CommitPlan) (goods : ℕ) (amount : Expr) :=
  Expr.branch .eq p.destination (.lit (s.bank.base+goods)) amount (.lit 0)

def directColumns (out n goods : ℕ) (s : CommitPlan) (p : Columns) : List Pass :=
  [⟨out,n,ordinaryTerm p s goods p.credit⟩,⟨out+n,n,ordinaryTerm p s goods p.charge⟩]

theorem direct_run (out n goods : ℕ) (s : CommitPlan) (p : Columns) (m : Memory w)
    (credit : (ordinaryTerm p s goods p.credit).Fits w out) (charge : (ordinaryTerm p s goods p.charge).Fits w out)
    (room : out+n+n<2^w) : (program w (directColumns out n goods s p)).Exec m
      (ProtocolRAM.result (directColumns out n goods s p) m) (clock (directColumns out n goods s p)) := by
  apply program_exec
  intro a ha
  simp only [directColumns,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl
  · exact ⟨credit,lt_of_le_of_lt (Nat.le_add_right (out+n) n) room⟩
  · exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right out n) charge,room⟩

theorem ordinaryTerm_eval (p : Columns) (s : CommitPlan) (e : Fin n) (goods : ℕ) (v : Expr) (m : Memory w)
    (physical : s.bank.base≤address p m e ∧ address p m e≤ s.bank.base+goods) (bound : s.bank.base+goods<2^w) :
    (ordinaryTerm p s goods v).eval m (e.val:Word w)=if kind (goods:=goods) s.bank p m e=none then
      v.eval m (e.val:Word w) else 0 := by
  have eq : p.destination.eval m (e.val:Word w)=((s.bank.base+goods:ℕ):Word w) ↔
      address p m e=s.bank.base+goods := by rw [Fin.ext_iff,Fin.val_cast_of_lt bound];rfl
  simp only [ordinaryTerm,Expr.eval,Comparison.test,beq_iff_eq,eq]
  by_cases hit : address p m e=s.bank.base+goods
  · simp [kind,hit]
  · have inside : s.bank.base≤address p m e ∧ address p m e<s.bank.base+goods := by omega
    simp [kind,inside,hit]

theorem direct_read (out n goods : ℕ) (s : CommitPlan) (p : Columns) (m : Memory w) (e : Fin n)
    (charge : (ordinaryTerm p s goods p.charge).Fits w out)
    (physical : s.bank.base≤address p m e ∧ address p m e≤ s.bank.base+goods) (bound : s.bank.base+goods<2^w) :
    let saved := ProtocolRAM.result (directColumns out n goods s p) m
    (saved (out+e.val)).val=(if kind (goods:=goods) s.bank p m e=none then installedBits p m e else 0) ∧
    (saved (out+n+e.val)).val=(if kind (goods:=goods) s.bank p m e=none then consumedBits p m e else 0) := by
  let one := image out n (ordinaryTerm p s goods p.credit) m
  let two := image (out+n) n (ordinaryTerm p s goods p.charge) one
  have h := e.isLt
  have c : two (out+e.val)=(ordinaryTerm p s goods p.credit).eval m (e.val:Word w) :=
    (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans
      (ProtocolRAMGeneratedWrite.read_image _ _ _ _ e)
  have d : two (out+n+e.val)=(ordinaryTerm p s goods p.charge).eval m (e.val:Word w) :=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ e).trans (eval_below _ _ m one charge
      (fun _ l => ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl l)))
  change (two _).val=_ ∧ (two _).val=_
  rw [c,d,ordinaryTerm_eval p s e goods _ m physical bound,ordinaryTerm_eval p s e goods _ m physical bound]
  split_ifs <;> exact ⟨rfl,rfl⟩

/-- The five rows may be reindexed into a single list for the public calendar. Public
price functions may depend on a measured finite menu word. -/
abbrev CashEvent (edges balls goods paths : ℕ) :=
  Fin edges ⊕ (Fin edges ⊕ (Fin balls ⊕ (Fin goods ⊕ Fin paths)))

theorem cashEvent_card (n rows goods paths : ℕ) : Fintype.card (CashEvent n rows goods paths)=2*n+rows+goods+paths := by
  simp [CashEvent]
 ; omega

structure CashColumns where
  direct : ℕ
  broadcast : ℕ
  excess : ℕ
  buy : ℕ

def CashColumns.addr (b : CashColumns) : CashEvent n rows goods paths → ℕ
  | .inl e => b.direct+e.val
  | .inr (.inl e) => b.direct+n+e.val
  | .inr (.inr (.inl r)) => b.broadcast+r.val
  | .inr (.inr (.inr (.inl i))) => b.excess+i.val
  | .inr (.inr (.inr (.inr j))) => b.buy+j.val

def eventPrice (payload copies : ℕ) (price : Fin n → ℝ) (tree : Fin rows → ℝ)
    (route : Fin goods → ℝ) (fee : Fin paths → ℝ) : CashEvent n rows goods paths → ℝ
  | .inl e => price e
  | .inr (.inl e) => -(price e)
  | .inr (.inr (.inl r)) => copies*tree r
  | .inr (.inr (.inr (.inl i))) => route i
  | .inr (.inr (.inr (.inr j))) => payload*fee j

def eventBill (b : CashColumns) (m : Memory w) (payload copies : ℕ) (price : Fin n → ℝ) (tree : Fin rows → ℝ)
    (route : Fin goods → ℝ) (fee : Fin paths → ℝ) :=
  ∑ e : CashEvent n rows goods paths,(m (b.addr e)).val*(eventPrice payload copies price tree route fee e)/payload

structure CashKeys (n rows goods paths : ℕ) where
  link : Fin n → ℕ
  broadcast : Fin rows → ℕ
  core : Fin goods → ℕ
  buy : Fin paths → ℕ

def CashKeys.atRow (k : CashKeys n rows goods paths) : CashEvent n rows goods paths → ℕ
  | .inl e => k.link e
  | .inr (.inl e) => k.link e
  | .inr (.inr (.inl r)) => k.broadcast r
  | .inr (.inr (.inr (.inl i))) => k.core i
  | .inr (.inr (.inr (.inr j))) => k.buy j

def keyedPrice (payload copies : ℕ) (link : Fin n → ℕ → ℝ) (tree : Fin rows → ℕ → ℝ)
    (core : Fin goods → ℕ → ℝ) (fee : Fin paths → ℕ → ℝ) (e : CashEvent n rows goods paths) (tag : ℕ) :=
  eventPrice payload copies (fun i => link i tag) (fun i => tree i tag) (fun i => core i tag) (fun i => fee i tag) e

/-- The archive reads an actual key for every signed price. Both appearances of a link
share its measured key, even when different edges select different price classes. -/
theorem keyed_bill (b : CashColumns) (k : CashKeys n rows goods paths) (m : Memory w) (payload copies : ℕ)
    (link : Fin n → ℕ → ℝ) (tree : Fin rows → ℕ → ℝ) (core : Fin goods → ℕ → ℝ) (fee : Fin paths → ℕ → ℝ) :
    (∑ e : CashEvent n rows goods paths, ((m (b.addr e)).val:ℝ)*
      keyedPrice payload copies link tree core fee e (m (k.atRow e)).val/payload) =
      eventBill b m payload copies (fun i => link i (m (k.link i)).val)
        (fun r => tree r (m (k.broadcast r)).val) (fun i => core i (m (k.core i)).val) (fun j => fee j (m (k.buy j)).val) := by
  apply Finset.sum_congr rfl
  intro e _
  rcases e with e | (e | (r | (i | j))) <;> rfl

theorem eventBill_eq (b : CashColumns) (m : Memory w) (p : Columns) (bank : Bank) (start : Memory w)
    (payload copies : ℕ) (positive : 0<payload) (price : Fin n → ℝ) (tree : Fin rows → ℝ)
    (route : Fin goods → ℝ) (fee : Fin paths → ℝ)
    (stored : ∀ e : Fin n,(m (b.direct+e.val)).val=(if kind (goods:=goods) bank p start e=none then installedBits p start e else 0) ∧
      (m (b.direct+n+e.val)).val=(if kind (goods:=goods) bank p start e=none then consumedBits p start e else 0)) :
    eventBill b m payload copies price tree route fee = linkBill (goods:=goods) p bank start payload price +
      (∑ r : Fin rows,(copies:ℝ)*(tree r*(m (b.broadcast+r.val)).val))/payload+
      (∑ i : Fin goods,((m (b.excess+i.val)).val:ℝ)/payload*route i)+
      ∑ j : Fin paths,(m (b.buy+j.val)).val*fee j := by
  have nonzero : (payload:ℝ)≠0 := by exact_mod_cast positive.ne'
  have pair (e : Fin n) : ((m (b.direct+e.val)).val:ℝ)*price e/payload+
      ((m (b.direct+n+e.val)).val:ℝ)*(-price e)/payload =
      (if kind (goods:=goods) bank p start e=none then
        ((installedBits p start e:ℝ)*price e-(consumedBits p start e:ℝ)*price e) else 0)/payload := by
    rw [(stored e).1,(stored e).2]
    split_ifs <;> simp; ring
  have buy (j : Fin paths) : ((m (b.buy+j.val)).val:ℝ)*((payload:ℝ)*fee j)/payload=
      ((m (b.buy+j.val)).val:ℝ)*fee j := by field_simp
  have broadcast (r : Fin rows) : ((m (b.broadcast+r.val)).val:ℝ)*((copies:ℝ)*tree r)/payload=
      (copies:ℝ)*(tree r*(m (b.broadcast+r.val)).val)/payload := by ring
  have excess (i : Fin goods) : ((m (b.excess+i.val)).val:ℝ)*route i/payload=
      ((m (b.excess+i.val)).val:ℝ)/payload*route i := by ring
  simp only [eventBill,Fintype.sum_sum_type,CashColumns.addr,eventPrice,buy,broadcast,excess,linkBill,Finset.sum_div]
  have sum := Finset.sum_congr (s₁:=Finset.univ) rfl (fun e _ => pair e)
  rw [Finset.sum_add_distrib] at sum
  linarith only [sum]

end
end Hierarchy.ProtocolRAM.RepairHistogram

end OAI
