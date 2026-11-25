import OAI.Hierarchy.ProtocolRAMWeightedScatter
import OAI.Hierarchy.ProtocolRAMStockAccounts
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Committing bought and consumed stock and publishing both cap columns -/

namespace Hierarchy.ProtocolRAMSignedStock

open Computability.VPVNP.BurstRAM
open ThreeFlat.RAM.PhysicalProcedure
open ProtocolRAM ProtocolRAMWeightedScatter
open scoped Fin.CommRing

variable {w n : ℕ}

def total (bank : Bank) : Expr := .lookup bank .row

def code (w src n out rows cap : ℕ) (bank : Bank) : Procedure w :=
  (ProtocolRAMWeightedScatter.program w src n).seq
    (ProtocolRAM.program w (StockAccounts.columns out rows cap (total bank)))

def output (address installed consumed : Fin n→ℕ) (m : Memory w)
    (out rows cap : ℕ) (bank : Bank) : Memory w :=
  result (StockAccounts.columns out rows cap (total bank))
    (ProtocolRAMWeightedScatter.image address (delta w installed consumed) m n)

private theorem input_end (bank : Bank) : (total bank).inputEnd=bank.base+bank.size := by
  simp [total,Expr.inputEnd]

theorem clock_cap (out rows cap : ℕ) (bank : Bank) :
    clock (StockAccounts.columns out rows cap (total bank))=12+92*rows := by
  simp [StockAccounts.columns,StockAccounts.clipped,StockAccounts.overflow,total,
    clock,Pass.clock,Expr.work]
  omega

attribute [local irreducible] Procedure.Exec CheapCode

/-- Both words of each occurrence come from the physical input tape. The two
post-commit columns use the genuinely updated stock bank as their source. -/
theorem run (src out rows cap : ℕ) (bank : Bank) (address installed consumed : Fin n→ℕ) (m : Memory w)
    (tape : src+2*n≤2^w) (bounded : ∀ i,address i<2^w)
    (disjoint : ∀ i,address i<src ∨ src+2*n≤address i)
    (loaded : ∀ i,m (src+2*i.val)=(address i:Word w) ∧
      m (src+2*i.val+1)=(installed i:Word w)-(consumed i:Word w))
    (before : bank.base+bank.size≤out) (finite : out+rows+rows<2^w) :
    (code w src n out rows cap bank).Exec m (output address installed consumed m out rows cap bank)
      (15+12*n+92*rows) := by
  let mid:=ProtocolRAMWeightedScatter.image address (delta w installed consumed) m n
  have commit : (ProtocolRAMWeightedScatter.program w src n).Exec m mid (3+12*n) :=
    ProtocolRAMWeightedScatter.run src address (delta w installed consumed) m tape bounded disjoint
    (fun i=>⟨(loaded i).1,by simpa [delta] using (loaded i).2⟩)
  let ps:=StockAccounts.columns out rows cap (total bank)
  have cost : 15+12*n+92*rows=(3+12*n)+clock ps := by
    rw [show clock ps=12+92*rows from clock_cap ..]
    omega
  rw [cost]
  apply Procedure.Exec.then commit
  exact StockAccounts.columns_exec out rows cap (total bank) mid (by rwa [input_end]) finite

theorem cheap (w src n out rows cap : ℕ) (bank : Bank) : ProtocolRAM.CheapCode (code w src n out rows cap bank) := by
  apply cheap_seq _ (program_cheap w (StockAccounts.columns out rows cap (total bank)))
  unfold CheapCode
  intro P R K pc reg pub exit i
  exact ProtocolRAMWeightedScatter.cheap w src n pc reg pub exit i

/-- Exact capacities and overflow for an original measured edge, even when
an arbitrary number of signed occurrences share its cell. -/
theorem read (out rows cap : ℕ) (bank : Bank) (address installed consumed : Fin n→ℕ) (m : Memory w)
    (j : Fin rows) (covers : rows≤bank.size) (before : bank.base+bank.size≤out)
    (finite : out+rows+rows<2^w) (capFit : cap<2^w)
    (funded : sumAt address consumed (bank.base+j.val)≤(m (bank.base+j.val)).val)
    (room : (m (bank.base+j.val)).val+sumAt address installed (bank.base+j.val)<2^w) :
    let a:=bank.base+j.val
    let raw:=(m a).val+sumAt address installed a-sumAt address consumed a
    let final:=output address installed consumed m out rows cap bank
    (final (out+j.val)).val=min raw cap ∧
    (final (out+rows+j.val)).val=raw-min raw cap ∧
    (final (out+j.val)).val+(final (out+rows+j.val)).val+sumAt address consumed a =
      (m a).val+sumAt address installed a := by
  intro a raw final
  let mid:=ProtocolRAMWeightedScatter.image address (delta w installed consumed) m n
  have balance:=read_balance address installed consumed m a funded room
  change (mid a).val+sumAt address consumed a=(m a).val+sumAt address installed a at balance
  have net : (mid a).val=raw := by dsimp [raw];omega
  have jfit : j.val<2^w := by have := j.isLt;omega
  have fetched : (total bank).eval mid (j.val:Word w)=mid a := by
    simp only [total,Expr.eval,Bank.read,Fin.val_cast_of_lt jfit,
      Nat.mod_eq_of_lt (j.isLt.trans_le covers),a]
  have h:=StockAccounts.columns_read out rows cap (total bank) mid j (by rwa [input_end]) finite capFit
  change (final (out+j.val)).val=min ((total bank).eval mid (j.val:Word w)).val cap ∧
      (final (out+rows+j.val)).val=((total bank).eval mid (j.val:Word w)).val-
        min ((total bank).eval mid (j.val:Word w)).val cap ∧
      (final (out+j.val)).val+(final (out+rows+j.val)).val=((total bank).eval mid (j.val:Word w)).val at h
  rw [fetched] at h
  exact ⟨net ▸ h.1,net ▸ h.2.1,by omega⟩

end Hierarchy.ProtocolRAMSignedStock

end OAI
