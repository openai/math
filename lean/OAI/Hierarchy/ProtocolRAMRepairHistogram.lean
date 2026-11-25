import OAI.Hierarchy.ProtocolRAMRepairScatter
import OAI.Hierarchy.ProbeRepairHistogramAccount
import OAI.Hierarchy.ProtocolRAMStockAccounts
import OAI.Hierarchy.ProtocolRAMWeightedScatter
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMPacked
import OAI.Hierarchy.ProtocolConflictPack
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Updating one genuinely shared commodity bank from all local histogram occurrences -/

namespace Hierarchy.ProtocolRAM.RepairHistogram
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Diagonal.MotifOuterTerms LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {w n goods q d : ℕ}

/-- Unselected and invalid records make no debit. -/
def debit (b : Batch q d) (i : Fin d) :=
  b.ifSelected (b.ifPacket (b.need i) (.lit 0)) (.lit 0)

def committed (b : Batch q d) (m : Memory w) (r : Word w) :=
  b.selected m r ∧ b.withinPacket m r ∧ (∑ j,((b.field j).eval m r).val)=b.copies

theorem debit_eval (b : Batch q d) (i : Fin d) (m : Memory w) (r : Word w)
    (qFit : q≤2^w) (copyFit : b.copies<2^w) (sumFit : q*b.copies<2^w) :
    (debit b i).eval m r = if committed b m r then (b.need i).eval m r else 0 := by
  rw [debit,b.eval_ifSelected,b.eval_ifPacket m r _ _ qFit copyFit sumFit]
  by_cases hs : b.selected m r <;> simp [hs,committed,Expr.eval]

theorem credit_eval (b : Batch q d) (tab : Fin q → Expr) (m : Memory w) (r : Word w)
    (qFit : q≤2^w) (copyFit : b.copies<2^w) (sumFit : q*b.copies<2^w) :
    (b.wire tab).eval m r = if committed b m r then
      (installed q b.maxWidth b.field tab).eval m r else 0 := by
  rw [Batch.wire,b.eval_ifSelected,b.eval_ifPacket m r _ _ qFit copyFit sumFit]
  by_cases hs : b.selected m r <;> simp [hs,committed,Expr.eval]

theorem debit_funded (b : Batch q d) (i : Fin d) (m : Memory w) (r : Word w)
    (qFit : q≤2^w) (copyFit : b.copies<2^w) (sumFit : q*b.copies<2^w) :
    ((debit b i).eval m r).val≤((b.stock i).eval m r).val := by
  rw [debit_eval b i m r qFit copyFit sumFit]
  split_ifs with h
  · exact h.1.2.2 i
  · exact Nat.zero_le _

theorem committed_of_debit (b : Batch q d) (i : Fin d) (m : Memory w) (r : Word w)
    (qFit : q≤2^w) (copyFit : b.copies<2^w) (sumFit : q*b.copies<2^w)
    (pos : 0<((debit b i).eval m r).val) : committed b m r := by
  by_contra h
  simp [debit_eval b i m r qFit copyFit sumFit,h] at pos

theorem inactive (b : Batch q d) (i : Fin d) (m : Memory w) (r : Word w) (tab : Fin q → Expr)
    (qFit : q≤2^w) (copyFit : b.copies<2^w) (sumFit : q*b.copies<2^w)
    (skip : ¬committed b m r) : (b.wire tab).eval m r=0 ∧ (debit b i).eval m r=0 := by
  rw [credit_eval b tab m r qFit copyFit sumFit,debit_eval b i m r qFit copyFit sumFit]
  simp [skip]

/-- The finite local batch is read at its genuine ball row and resource port. This
also handles padded options and arbitrary shared pointers to the same commodity. -/
def fromBatch (owner data : Bank) (dest ball port : Expr) (b : Batch q d)
    (tabs : Fin d → Fin q → Expr) : Columns :=
  ⟨owner,data,dest,
   chooseField d 0 (fun i => (b.wire (tabs i)).atRow ball) port,
   chooseField d 0 (fun i => (debit b i).atRow ball) port⟩

theorem fromBatch_read (owner data : Bank) (dest ball port : Expr) (b : Batch q d)
    (tabs : Fin d → Fin q → Expr) (m : Memory w) (e : Word w) (i : Fin d) (fits : d≤2^w)
    (index : (port.eval m e).val=i.val) :
    ((fromBatch owner data dest ball port b tabs).credit.eval m e)=(b.wire (tabs i)).eval m (ball.eval m e) ∧
    ((fromBatch owner data dest ball port b tabs).charge.eval m e)=(debit b i).eval m (ball.eval m e) := by
  constructor <;> simp only [fromBatch,eval_chooseField d 0 _ _ _ _ i (by simpa using fits)
    (by simpa using index),eval_atRow]

theorem delta_inactive (owner data : Bank) (dest ball port : Expr) (b : Batch q d)
    (tabs : Fin d → Fin q → Expr) (m : Memory w) (e : Fin n) (i : Fin d) (dFit : d≤2^w)
    (qFit : q≤2^w) (copyFit : b.copies<2^w) (sumFit : q*b.copies<2^w)
    (index : (port.eval m (e.val:Word w)).val=i.val)
    (skip : ¬committed b m (ball.eval m (e.val:Word w))) :
    delta (fromBatch owner data dest ball port b tabs) m e=0 := by
  obtain ⟨credit,charge⟩ := fromBatch_read owner data dest ball port b tabs m (e.val:Word w) i dFit index
  obtain ⟨off,none⟩ := inactive b i m (ball.eval m (e.val:Word w)) (tabs i) qFit copyFit sumFit skip
  simp [delta,credit,charge,off,none]

/-- The option-valued economic kind is read from the physical destination. Addresses
outside the measured commodity bank represent ordinary priced links. -/
def kind (bank : Bank) (p : Columns) (m : Memory w) (i : Fin n) : Option (Fin goods) :=
  if h : bank.base≤address p m i ∧ address p m i<bank.base+goods then
    some ⟨address p m i-bank.base,by omega⟩ else none

theorem kind_iff (bank : Bank) (p : Columns) (m : Memory w) (i : Fin n) (j : Fin goods) :
    kind bank p m i=some j ↔ address p m i=bank.base+j.val := by
  unfold kind
  split_ifs with h
  · simp only [Option.some.injEq,Fin.ext_iff]
    omega
  · simp only [false_iff]
    intro eq
    have := j.isLt
    omega

theorem sumAt_resource (bank : Bank) (p : Columns) (m : Memory w) (v : Fin n → ℕ) (i : Fin goods) :
    ProtocolRAMWeightedScatter.sumAt (address p m) v (bank.base+i.val) =
      OuterBank.resourceBits (kind bank p m) v i := by
  simp [ProtocolRAMWeightedScatter.sumAt,OuterBank.resourceBits,kind_iff]

def raw (bank : Bank) (p : Columns) (src n : ℕ) (m : Memory w) (i : Fin goods) :=
  (result p src n m (bank.base+i.val)).val

/-- This is `OuterBank.FailedRows.stock`, on the literal output of the repeated-address
scatter. Every occurrence contributes its actual native credit and actual native debit. -/
theorem balance (bank : Bank) (p : Columns) (src n : ℕ) (m : Memory w) (i : Fin goods)
    (sep : bank.base+goods≤ src)
    (funded : OuterBank.resourceBits (kind bank p m) (consumedBits (n:=n) p m) i≤(m (bank.base+i.val)).val)
    (room : (m (bank.base+i.val)).val+OuterBank.resourceBits (kind bank p m) (installedBits (n:=n) p m) i<2^w) :
    (m (bank.base+i.val)).val+OuterBank.resourceBits (kind bank p m) (installedBits (n:=n) p m) i =
      raw bank p src n m i+OuterBank.resourceBits (kind bank p m) (consumedBits (n:=n) p m) i := by
  have seed := ProtocolRAMGeneratedWrite.frame_image src (2*n) (pair p) m (bank.base+i.val)
    (.inl (by have := i.isLt; omega))
  have diff : ProtocolRAMWeightedScatter.delta w (installedBits (n:=n) p m) (consumedBits p m)=delta p m := by
    funext x
    simp [ProtocolRAMWeightedScatter.delta,installedBits,consumedBits,delta]
  symm
  simpa only [diff,seed,sumAt_resource,raw,result] using
    ProtocolRAMWeightedScatter.read_balance (address p m) (installedBits (n:=n) p m) (consumedBits p m)
      (image src (2*n) (pair p) m) (bank.base+i.val)
      (by simpa only [seed,sumAt_resource] using funded) (by simpa only [seed,sumAt_resource] using room)

def cappedCode (w src n capOut goods limit : ℕ) (p : Columns) (bank : Bank) : Procedure w :=
  (code w src n p).seq (program w (StockAccounts.columns capOut goods limit (.lookup bank .row)))

def capped (p : Columns) (bank : Bank) (src n capOut goods limit : ℕ) (m : Memory w) :=
  ProtocolRAM.result (StockAccounts.columns capOut goods limit (.lookup bank .row)) (result p src n m)

theorem capped_exec (p : Columns) (bank : Bank) (src n capOut goods limit : ℕ) (m : Memory w)
    (directory : PairDirectory p m n) (before : (pair p).Fits w src) (room : src+2*n<2^w)
    (safe : ∀ i : Fin n,address p m i<src) (covered : (Expr.lookup bank .row).inputEnd≤ capOut)
    (endFit : capOut+goods+goods<2^w) :
    (cappedCode w src n capOut goods limit p bank).Exec m (capped p bank src n capOut goods limit m)
      (ticks n p+clock (StockAccounts.columns capOut goods limit (.lookup bank .row))) := by
  have commit : (code w src n p).Exec m (result p src n m) (ticks n p) :=
    run p src n m directory before room safe
  apply commit.then
  exact StockAccounts.columns_exec capOut goods limit (.lookup bank .row) (result p src n m) covered endFit

theorem capped_read (p : Columns) (bank : Bank) (src n capOut cap payload : ℕ) (m : Memory w) (i : Fin goods)
    (covered : (Expr.lookup bank .row).inputEnd≤ capOut) (endFit : capOut+goods+goods<2^w)
    (size : goods≤bank.size) (bound : cap*payload<2^w) :
    let out := capped p bank src n capOut goods (cap*payload) m
    (out (capOut+i.val)).val=min (raw bank p src n m i) (cap*payload) ∧
    (out (capOut+goods+i.val)).val=spillBits cap payload (raw bank p src n m) i := by
  have bits := StockAccounts.columns_read capOut goods (cap*payload) (.lookup bank .row)
    (result p src n m) i covered endFit bound
  have fits : i.val<2^w := by have := i.isLt; omega
  simpa only [capped,Expr.eval,Bank.read,Fin.val_cast_of_lt fits,Nat.mod_eq_of_lt (i.isLt.trans_le size),
    raw,spillBits,clipBits] using And.intro bits.1 bits.2.1

/-- The packet ID and the selector field determine the paid broadcast width in this
ball. Inactive and rejected histograms transmit no broadcast. -/
def broadcastTerm (b : Batch q d) (sizeTable : Bank) : Expr :=
  b.ifSelected (b.ifPacket (.lookup sizeTable b.packet) (.lit 0)) (.lit 0)

theorem broadcastTerm_eval (b : Batch q d) (table : Bank) (m : Memory w) (r : Word w)
    (qFit : q≤2^w) (copyFit : b.copies<2^w) (sumFit : q*b.copies<2^w) :
    (broadcastTerm b table).eval m r=if committed b m r then table.read m (b.packet.eval m r) else 0 := by
  rw [broadcastTerm,b.eval_ifSelected,b.eval_ifPacket m r _ _ qFit copyFit sumFit]
  by_cases hs : b.selected m r <;> simp [hs,committed,Expr.eval]

theorem broadcastRun (b : Batch q d) (table : Bank) (out rows : ℕ) (m : Memory w)
    (fits : (broadcastTerm b table).Fits w out) (room : out+rows<2^w) :
    (scan w out rows (broadcastTerm b table)).Exec m (image out rows (broadcastTerm b table) m)
      (4+rows*(2*(broadcastTerm b table).work+4)) := scan_exec out rows (broadcastTerm b table) m fits room

theorem broadcastRead (b : Batch q d) (table : Bank) (out rows : ℕ) (m : Memory w) (i : Fin rows)
    (qFit : q≤2^w) (copyFit : b.copies<2^w) (sumFit : q*b.copies<2^w) :
    image out rows (broadcastTerm b table) m (out+i.val) = if committed b m (i.val:Word w)
      then table.read m (b.packet.eval m (i.val:Word w)) else 0 :=
  (ProtocolRAMGeneratedWrite.read_image out rows (broadcastTerm b table) m i).trans
    (broadcastTerm_eval b table m _ qFit copyFit sumFit)

/-- Broadcast size is looked up by the selected menu word in the actual snapshot; the
counter is zero on a skipped row. The public routing tree determines its wire cost. -/
def broadcast {rows : ℕ} (word : Bank) (m : Memory w) (copies : ℕ) (tree : Fin rows → ℝ)
    (i : Fin rows) : ℝ := (copies:ℝ)*(tree i*(word.read m (i.val:Word w)).val)

/-- A single paid root is quoted using precisely the fields projected from the source
of the sparse commit and the actual broadcast word. The packet decoder identifies its
histogram and repeated input requests independently of the physical wire ordering. -/
theorem physical_quote {F E A : Type*} [Field F] [Fintype E] [Fintype A] {k t rows : ℕ}
    [Nonempty (Fin k)] {edge : E → Chord k} {req : A → E} (P : Probe.Packet F edge req)
    (hist : Histogram (Fin P.terms) t) (p : Columns) (m : Memory w) (select : E → Fin n)
    (bits : Bank) (menus : Memory w) (i : Fin rows) (tree : Fin rows → ℝ)
    (creditRead : ∀ e,installedBits p m (select e)=histWidth P.count hist e)
    (debitRead : ∀ e,consumedBits p m (select e)=debited req (t*P.width) e)
    (word : (bits.read menus (i.val:Word w)).val=P.selectorBits)
    (bound : ℕ) (bounded : ∀ j e,P.count j e≤bound) (price quoted : E → ℝ) (err γ : ℝ)
    (nonneg : 0≤err) (accuracy : ∀ e,quoted e≤price e ∧ price e≤quoted e+err)
    (catalogue : (∑ e,(histWidth P.count hist e:ℝ)*quoted e)+t*(tree i*P.selectorBits)≤
      t*((P.width:ℝ)*((∑ a,quoted (req a))-γ))) (resolution : (Fintype.card E:ℝ)*bound*err≤P.width*γ/2) :
    (∑e,(installedBits p m (select e):ℝ)*price e)+broadcast bits menus t tree i+t*(P.width*γ/2) ≤
      ∑e,(consumedBits p m (select e):ℝ)*price e := by
  simp only [broadcast,word,debitRead]
  exact rounded_charge P hist _ creditRead bound bounded price quoted err γ (tree i) nonneg accuracy catalogue resolution

def linkBill (p : Columns) (bank : Bank) (m : Memory w) (payload : ℕ) (price : Fin n → ℝ) : ℝ :=
  (∑ e : Fin n,if kind (goods:=goods) bank p m e=none then
    ((installedBits p m e:ℝ)*price e-(consumedBits p m e:ℝ)*price e) else 0)/payload

theorem linkBill_eq (p : Columns) (bank : Bank) (m : Memory w) (payload : ℕ) (price : Fin n → ℝ)
    (bc : ℝ) : linkBill (goods:=goods) p bank m payload price+bc =
      cashChange (kind (goods:=goods) bank p m) (netUnits payload (installedBits p m) (consumedBits p m)) price bc := by
  rw [linkBill,cashChange,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases k : kind (goods:=goods) bank p m e=none
  · simp only [k,ite_true,netUnits]
    ring
  · simp [k]

/-- The cash charge posts the emitted and removed lane widths, broadcast bits, and the
real overflow words on their prescribed walks. This definition works at arbitrary real
length and scale without requiring real registers in the CPU. -/
def postedCash {rows : ℕ} {E : Type*} (p : Columns) (bank : Bank) (src n capOut cap payload : ℕ)
    (m : Memory w) (cash : ℝ) (price : Fin n → ℝ) (bc : Fin rows → ℝ)
    (walk : Fin goods → List E) (len : E → ℝ) : ℝ :=
  let after := capped p bank src n capOut goods (cap*payload) m
  cash + linkBill (goods:=goods) p bank m payload price + (∑ r,bc r)/payload +
    ∑ i : Fin goods,((after (capOut+goods+i.val)).val:ℝ)/payload*((walk i).map len).sum

/-- Prices the observed excess at its true route cost and uses the commodity box only
as an upper bound. This supplies the `paid` field with the chronological cash posting. -/
theorem paid {rows : ℕ} {E : Type*} (p : Columns) (bank : Bank) (src n capOut cap payload : ℕ)
    (m : Memory w) (cash : ℝ) (price : Fin n → ℝ) (bc : Fin rows → ℝ)
    (walk : Fin goods → List E) (len : E → ℝ) (box : Fin goods → ℝ)
    (ordinary : ∀ i,((walk i).map len).sum≤box i) (covered : (Expr.lookup bank .row).inputEnd≤ capOut)
    (endFit : capOut+goods+goods<2^w) (size : goods≤bank.size) (bound : cap*payload<2^w) :
    postedCash p bank src n capOut cap payload m cash price bc walk len ≤ cash +
      cashChange (kind (goods:=goods) bank p m) (netUnits payload (installedBits p m) (consumedBits p m))
        price ((∑ r,bc r)/payload) + pairing (bitStock payload (spillBits cap payload (raw bank p src n m))) box := by
  unfold postedCash
  rw [add_assoc cash,linkBill_eq]
  dsimp only
  apply add_le_add_right
  unfold pairing bitStock
  apply Finset.sum_le_sum
  intro i _
  rw [(capped_read p bank src n capOut cap payload m i covered endFit size bound).2]
  exact mul_le_mul_of_nonneg_left (ordinary i) (by positivity)

/-- Reorder native flat slots by actual selected root and local resource port, as
required by the nonlinear ledger and the wire telescope. -/
theorem resourceBits_reindex {E I : Type*} [Fintype E] (enum : E ≃ Fin n) (k : Fin n → Option I)
    (bits : Fin n → ℕ) (i : I) :
    OuterBank.resourceBits (fun e => k (enum e)) (fun e => bits (enum e)) i = OuterBank.resourceBits k bits i :=
  enum.sum_comp (fun e => if k e=some i then bits e else 0)

theorem balance_reindex {rows : ℕ} {ports : Fin rows → ℕ} (bank : Bank) (p : Columns) (src n : ℕ) (m : Memory w)
    (enum : (Σ r : Fin rows,Fin (ports r)) ≃ Fin n) (space : bank.base+goods≤ src)
    (funded : ∀ i : Fin goods,OuterBank.resourceBits (kind bank p m) (consumedBits (n:=n) p m) i≤(m (bank.base+i.val)).val)
    (room : ∀ i : Fin goods,(m (bank.base+i.val)).val+OuterBank.resourceBits (kind bank p m) (installedBits (n:=n) p m) i<2^w)
    (i : Fin goods) : (m (bank.base+i.val)).val+
        OuterBank.resourceBits (fun e => kind bank p m (enum e)) (fun e => installedBits p m (enum e)) i =
      raw bank p src n m i+
        OuterBank.resourceBits (fun e => kind bank p m (enum e)) (fun e => consumedBits p m (enum e)) i := by
  simpa only [resourceBits_reindex] using balance bank p src n m i space (funded i) (room i)

/-- Inactive and padded slots do not appear as paid failed roots. Keeping every slot
in memory and removing zero widths in the economic ledger yields the same total. -/
theorem resourceBits_active {E I : Type*} [Fintype E] (use : E ↪ Fin n) (k : Fin n → Option I)
    (bits : Fin n → ℕ) (unused : ∀ j, (∀ e,use e≠j) → bits j=0) (i : I) :
    OuterBank.resourceBits (fun e => k (use e)) (fun e => bits (use e)) i=OuterBank.resourceBits k bits i := by
  classical
  let f := fun j => if k j=some i then bits j else 0
  have h : (∑ j ∈ Finset.univ.map use,f j)=∑ j : Fin n,f j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ outside
    have away : ∀ e,use e≠j := by
      intro e hit
      exact outside (Finset.mem_map.mpr ⟨e,Finset.mem_univ _,hit⟩)
    simp [f,unused j away]
  simpa [f,OuterBank.resourceBits] using h

theorem balance_active {E : Type*} [Fintype E] (use : E ↪ Fin n) (p : Columns) (bank : Bank) (src : ℕ)
    (m : Memory w) (space : bank.base+goods≤ src) (i : Fin goods)
    (off : ∀ j,(∀ e,use e≠j) → installedBits p m j=0 ∧ consumedBits p m j=0)
    (funded : OuterBank.resourceBits (kind bank p m) (consumedBits (n:=n) p m) i≤(m (bank.base+i.val)).val)
    (room : (m (bank.base+i.val)).val+OuterBank.resourceBits (kind bank p m) (installedBits (n:=n) p m) i<2^w) :
    (m (bank.base+i.val)).val+OuterBank.resourceBits (fun e => kind bank p m (use e)) (fun e => installedBits p m (use e)) i =
      raw bank p src n m i+OuterBank.resourceBits (fun e => kind bank p m (use e)) (fun e => consumedBits p m (use e)) i := by
  rw [resourceBits_active use _ _ (fun j h => (off j h).1),resourceBits_active use _ _ (fun j h => (off j h).2)]
  exact balance bank p src n m i space funded room

theorem cashChange_active {E I : Type*} [Fintype E] (use : E ↪ Fin n) (k : Fin n → Option I)
    (payload : ℕ) (put take : Fin n → ℕ) (price : Fin n → ℝ) (bc : ℝ)
    (unused : ∀ j,(∀ e,use e≠j) → put j=0 ∧ take j=0) :
    cashChange (fun e => k (use e)) (netUnits payload (fun e => put (use e)) (fun e => take (use e)))
        (fun e => price (use e)) bc = cashChange k (netUnits payload put take) price bc := by
  classical
  let f := fun j => if k j=none then netUnits payload put take j*price j else 0
  have h : (∑ j ∈ Finset.univ.map use,f j)=∑ j : Fin n,f j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ outside
    obtain ⟨off,inert⟩ := unused j (fun e hit => outside (Finset.mem_map.mpr ⟨e,Finset.mem_univ _,hit⟩))
    simp [f,netUnits,off,inert]
  simpa [f,cashChange,netUnits] using congrArg (fun z : ℝ => z+bc) h

private theorem sparse_cheap (w src n : ℕ) (p : Columns) : CheapCode (code w src n p) :=
  @cheap_seq w (scan w src (2*n) (pair p)) (ProtocolRAMWeightedScatter.program w src n)
    (fun {_P _R _K} pc reg pub exit i=>scan_cheap w src (2*n) (pair p) pc reg pub exit i)
    (fun {_P _R _K} pc reg pub exit i=>ProtocolRAMWeightedScatter.cheap w src n pc reg pub exit i)

attribute [local irreducible] CheapCode in
theorem capped_cheap (w src n capOut goods limit : ℕ) (p : Columns) (bank : Bank) :
    CheapCode (cappedCode w src n capOut goods limit p bank) := by
  unfold cappedCode
  exact @cheap_seq w (code w src n p) (program w (StockAccounts.columns capOut goods limit (.lookup bank .row)))
    (sparse_cheap w src n p) (program_cheap w (StockAccounts.columns capOut goods limit (.lookup bank .row)))

/-- Funding is enforced by the actual failed-ball MIS whenever different active
resource ports mapped to the same commodity would have overlapping footprints. -/
theorem funded_of_unique {I E : Type*} [Fintype E] (kind : E → Option I) (used : E → ℕ)
    (old : I → ℕ) (i : I) (one : ∀ e,kind e=some i → used e≤old i)
    (distinct : ∀ a b,kind a=some i → kind b=some i → 0<used a → 0<used b → a=b) :
    OuterBank.resourceBits kind used i≤old i := by
  classical
  by_cases h : ∃ e,kind e=some i ∧ 0<used e
  · obtain ⟨a,ha,pa⟩ := h
    unfold OuterBank.resourceBits
    rw [Finset.sum_eq_single a]
    · simpa [ha] using one a ha
    · intro b _ ne
      by_cases hb : kind b=some i
      · have eq : used b=0 := by by_contra nz; exact ne (distinct b a hb ha (Nat.pos_of_ne_zero nz) pa)
        simp [hb,eq]
      · simp [hb]
    · simp
  · have zero (e : E) : (if kind e=some i then used e else 0)=0 := by
      by_cases hit : kind e=some i
      · have eq : used e=0 := by by_contra ne; exact h ⟨e,hit,Nat.pos_of_ne_zero ne⟩
        simp [hit,eq]
      · simp [hit]
    simp [OuterBank.resourceBits,zero]

/-- Repeated requirements internal to one packet already belong to the same paid
resource port. Distinct repairs cannot reuse a commodity carried by their footprints. -/
theorem funded_mis {goods roots ranks : ℕ} (ports : Fin roots → ℕ)
    (kind : (Σ r,Fin (ports r)) → Option (Fin goods)) (used : (Σ r,Fin (ports r)) → ℕ)
    (old : Fin goods → ℕ) (fail : Fin roots → Bool) (adj : Fin roots → Fin ranks → Fin roots)
    (sites : Fin roots → Finset (Fin goods)) (symm : ∀ v j,∃ k,adj (adj v j) k=v)
    (listed : ∀ u v,u≠v → ¬Disjoint (sites u) (sites v) → ∃ j,adj u j=v)
    (selected : ∀ e,0<used e → ProtocolConflictPack.Chosen fail adj e.1)
    (near : ∀ e i,kind e=some i → 0<used e → i∈sites e.1)
    (distinctLocal : ∀ r (p q : Fin (ports r)) i, kind ⟨r,p⟩=some i → kind ⟨r,q⟩=some i →
      0<used ⟨r,p⟩ → 0<used ⟨r,q⟩ → p=q)
    (per : ∀ e i,kind e=some i → used e≤old i) (i : Fin goods) :
    OuterBank.resourceBits kind used i≤old i := by
  apply funded_of_unique kind used old i (fun e he => per e i he)
  rintro ⟨r,p⟩ ⟨s,q⟩ hp hq pp pq
  by_cases same : r=s
  · subst s
    have := distinctLocal r p q i hp hq pp pq
    subst q
    rfl
  · have disjoint := ProtocolConflictPack.disjoint_picked fail adj sites symm listed
      (selected ⟨r,p⟩ pp) (selected ⟨s,q⟩ pq) same
    exact False.elim (Finset.disjoint_left.mp disjoint (near ⟨r,p⟩ i hp pp) (near ⟨s,q⟩ i hq pq))

end
end Hierarchy.ProtocolRAM.RepairHistogram

end OAI
