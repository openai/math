import OAI.Hierarchy.ProtocolRAMRouteSettlement
import OAI.Hierarchy.ProbeCatalystProvision

namespace OAI
/-! # Cumulative native catalyst debits at the terminal site/axis banks -/

noncomputable section
namespace Hierarchy.ProtocolRAM.ReserveUse
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open AdaptiveProbe
open scoped Fin.CommRing BigOperators Classical

variable {W n count : ℕ}

/-- Both words of each historical occurrence are read through the same archive
directory. The first is the physical column/axis ordinal; the second is the
guarded number of consumed bits. Entries may point to different event slabs. -/
structure Archive where
  kind : Bank
  pointer : Bank
  history : Bank
  scratch : ℕ

def word (a : Archive) (b : RouteSettlement.Banks) : Expr :=
  let data := Expr.lookup a.history (.lookup a.pointer .row)
  .branch .eq (.lookup a.kind .row) (.lit 0) (.op .add (.lit b.used.base) data) data

def seed (b : RouteSettlement.Banks) (count reserve : ℕ) : List Pass :=
  [⟨b.reserved.base,count,.lit reserve⟩,⟨b.used.base,count,.lit 0⟩]

def columns (a : Archive) (b : RouteSettlement.Banks) (count n reserve : ℕ) : List Pass :=
  seed b count reserve ++ [⟨a.scratch,2*n,word a b⟩]

def native (W : ℕ) (a : Archive) (b : RouteSettlement.Banks) (count n reserve : ℕ) :=
  (program W (columns a b count n reserve)).seq (ProtocolRAMWeightedScatter.program W a.scratch n)

def clock (a : Archive) (b : RouteSettlement.Banks) (count n reserve : ℕ) :=
  ProtocolRAM.clock (columns a b count n reserve)+(3+12*n)

theorem clock_eq (a : Archive) (b : RouteSettlement.Banks) (count n reserve : ℕ) :
    clock a b count n reserve=19+12*count+160*n := by
  simp [clock,columns,seed,ProtocolRAM.clock,Pass.clock,word,Expr.work]
 ; ring

def address (b : RouteSettlement.Banks) (site : Fin n→Fin count) (i : Fin n) := b.used.base+(site i).val

def output (a : Archive) (b : RouteSettlement.Banks) (reserve : ℕ) (site : Fin n→Fin count)
    (debit : Fin n→ℕ) (m : Memory W) :=
  ProtocolRAMWeightedScatter.image (address b site) debit (result (columns a b count n reserve) m) n

structure Mounted (a : Archive) (b : RouteSettlement.Banks) (reserve : ℕ) (site : Fin n→Fin count)
    (debit : Fin n→ℕ) (m : Memory W) : Prop where
  reserved : b.reserved.base+count≤b.used.base
  used : b.used.base+count≤a.scratch
  room : a.scratch+2*n<2^W
  history : (word a b).Fits W b.reserved.base
  loaded : ∀i,(word a b).eval m ((2*i.val:ℕ):Word W)=(address b site i:Word W) ∧
    (word a b).eval m ((2*i.val+1:ℕ):Word W)=(debit i:Word W)

theorem loaded_of_archive (a : Archive) (b : RouteSettlement.Banks) (site : Fin n→Fin count)
    (debit : Fin n→ℕ) (m : Memory W)
    (kind : ∀i : Fin n,a.kind.read m ((2*i.val:ℕ):Word W)=0 ∧
      a.kind.read m ((2*i.val+1:ℕ):Word W)≠0)
    (owner : ∀i : Fin n,a.history.read m (a.pointer.read m ((2*i.val:ℕ):Word W))=((site i).val:Word W))
    (amount : ∀i : Fin n,a.history.read m (a.pointer.read m ((2*i.val+1:ℕ):Word W))=(debit i:Word W)) :
    ∀i,(word a b).eval m ((2*i.val:ℕ):Word W)=(address b site i:Word W) ∧
      (word a b).eval m ((2*i.val+1:ℕ):Word W)=(debit i:Word W) := by
  intro i
  have even:=(kind i).1
  have odd:=(kind i).2
  have who:=owner i
  have howMuch:=amount i
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at even odd who howMuch
  simp [word,address,Expr.eval,DescriptorExpr.Comparison.test,RowOp.opcode,BinaryOp.eval,
    even,odd,who,howMuch]

theorem cheap (W : ℕ) (a : Archive) (b : RouteSettlement.Banks) (count n reserve : ℕ) :
    CheapCode (native W a b count n reserve) := by
  unfold native
  exact @cheap_seq W (program W (columns a b count n reserve)) (ProtocolRAMWeightedScatter.program W a.scratch n)
    (@program_cheap W (columns a b count n reserve)) (@ProtocolRAMWeightedScatter.cheap W a.scratch n)

theorem exec (a : Archive) (b : RouteSettlement.Banks) (reserve : ℕ) (site : Fin n→Fin count)
    (debit : Fin n→ℕ) (m : Memory W) (ok : Mounted a b reserve site debit m) :
    (native W a b count n reserve).Exec m (output a b reserve site debit m) (clock a b count n reserve) := by
  obtain ⟨reserveEnds,usedEnds,room,inputs,loaded⟩ := ok
  have seeds (p) (hp : p∈seed b count reserve) : p.Fits W := by
    simp only [seed,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> apply Pass.fits_of_span <;> simp [Expr.inputEnd] <;> omega
  have fits : ∀p∈columns a b count n reserve,p.Fits W := by
    intro p hp
    rcases List.mem_append.mp hp with earlier|last
    · exact seeds p earlier
    · obtain rfl := List.mem_singleton.mp last
      exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (show b.reserved.base≤a.scratch by omega) inputs,room⟩
  apply Procedure.Exec.then (program_exec _ _ fits)
  apply ProtocolRAMWeightedScatter.run
  · omega
  · intro i; have := (site i).isLt; unfold address; omega
  · intro i; left; have := (site i).isLt; unfold address; omega
  · intro i
    let old := result (seed b count reserve) m
    have prior (x : ℕ) (hx : x<b.reserved.base) : old x=m x := by
      apply result_below
      intro p hp
      simp only [seed,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> simp only <;> omega
    have read (j : Fin (2*n)) : result (columns a b count n reserve) m (a.scratch+j.val)=
        (word a b).eval m (j.val:Word W) :=
      (ProtocolRAMGeneratedWrite.read_image _ _ _ old j).trans (eval_below _ _ m old inputs prior)
    have h := i.isLt
    exact ⟨(read ⟨2*i.val,by omega⟩).trans (loaded i).1,by
      simpa only [Nat.add_assoc] using (read ⟨2*i.val+1,by omega⟩).trans (loaded i).2⟩

theorem frame (a : Archive) (b : RouteSettlement.Banks) (reserve : ℕ) (site : Fin n→Fin count)
    (debit : Fin n→ℕ) (m : Memory W) (x : ℕ)
    (offReserved : x<b.reserved.base ∨ b.reserved.base+count≤x)
    (offUsed : x<b.used.base ∨ b.used.base+count≤x)
    (offScratch : x<a.scratch ∨ a.scratch+2*n≤x) : output a b reserve site debit m x=m x := by
  rw [output,ProtocolRAMWeightedScatter.frame _ _ _ _ _ (fun i=>by
    have := (site i).isLt; unfold address; omega)]
  exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ offScratch).trans
    ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ offUsed).trans
     (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ offReserved))

/-- Both actual bank reads, including repeated physical IDs and zero rows,
from the deterministic output of the native seeding and scattered additions. -/
theorem reported (a : Archive) (b : RouteSettlement.Banks) (reserve : ℕ) (site : Fin n→Fin count)
    (debit : Fin n→ℕ) (m : Memory W) (ok : Mounted a b reserve site debit m) (i : Fin count)
    (sizeUsed : count≤b.used.size) (sizeReserved : count≤b.reserved.size)
    (bound : (∑ j,if site j=i then debit j else 0)≤reserve) (wide : reserve<2^W) :
    RouteSettlement.actual b.used (output a b reserve site debit m) i.val =
      (∑ j,if site j=i then debit j else 0) ∧
    RouteSettlement.actual b.reserved (output a b reserve site debit m) i.val=reserve := by
  obtain ⟨reserveEnds,usedEnds,room,_,_⟩ := ok
  have hi := i.isLt
  have fits : i.val<2^W := by omega
  simp only [RouteSettlement.actual,Bank.read,Fin.val_cast_of_lt fits,
    Nat.mod_eq_of_lt (hi.trans_le sizeUsed),Nat.mod_eq_of_lt (hi.trans_le sizeReserved)]
  let u := result (columns a b count n reserve) m
  have zero : u (b.used.base+i.val)=0 :=
    (ProtocolRAMGeneratedWrite.frame_image a.scratch (2*n) (word a b) _ (b.used.base+i.val) (Or.inl (by omega))).trans
      (ProtocolRAMGeneratedWrite.read_image b.used.base count (.lit 0) _ i)
  have allocated : u (b.reserved.base+i.val)=(reserve:Word W) :=
    (ProtocolRAMGeneratedWrite.frame_image a.scratch (2*n) (word a b) _ (b.reserved.base+i.val) (Or.inl (by omega))).trans
      ((ProtocolRAMGeneratedWrite.frame_image b.used.base count (.lit 0) _ (b.reserved.base+i.val) (Or.inl (by omega))).trans
        (ProtocolRAMGeneratedWrite.read_image b.reserved.base count (.lit reserve) _ i))
  have mass : (∑ j,if address b site j=b.used.base+i.val then debit j else 0) =
      ∑ j,if site j=i then debit j else 0 := by simp only [address,Nat.add_right_inj,Fin.val_inj]
  constructor
  · have result := ProtocolRAMWeightedScatter.read_nat (address b site) debit u (b.used.base+i.val)
      (by rw [zero,mass]; simpa using bound.trans_lt wide)
    change (ProtocolRAMWeightedScatter.image (address b site) debit u n (b.used.base+i.val)).val=_
    simpa only [zero,Fin.val_zero,Nat.zero_add,mass] using result
  · have before := ProtocolRAMWeightedScatter.frame (address b site) debit u n (b.reserved.base+i.val)
      (fun j=>by unfold address; omega)
    exact (congrArg Fin.val (before.trans allocated)).trans (Fin.val_cast_of_lt wide)

/-- Flatten all actual event occurrences in the same native archive order.
The injected row-to-column map can change after every previous choice. -/
theorem funded_history {r fuel payload : ℕ} (rows : Fin r→Type*) [∀t,Fintype (rows t)]
    (slots : ∀t,rows t↪Fin count) (bits : ∀t,rows t→ℕ)
    (index : (Σ t,rows t) ≃ Fin n) (time : r≤fuel) (bounded : ∀ t v,bits t v≤payload)
    (i : Fin count) :
    let site := fun j : Fin n=>slots (index.symm j).1 (index.symm j).2
    let debit := fun j : Fin n=>bits (index.symm j).1 (index.symm j).2
    (∑ j,if site j=i then debit j else 0)≤fuel*payload := by
  intro site debit
  have price := (catalyst_funded rows slots bits Finset.univ
    (fuel:=fuel) (w:=payload) (by simpa) (fun t _ v=>bounded t v)).1 i
  let cost : (Σ t,rows t)→ℕ := fun x=>if slots x.1 x.2=i then bits x.1 x.2 else 0
  have moved : (∑ j,if site j=i then debit j else 0)=∑ x,cost x := index.symm.sum_comp cost
  rw [moved,Fintype.sum_sigma]
  apply le_trans _ price
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro x _
  by_cases hit : slots t x=i <;> simp [cost,hit]

/-- Dormant and zero-width cells of the fixed native archive may reuse a
dummy physical ordinal. Only positive debits require the MIS site injection. -/
theorem funded_padded {r fuel payload : ℕ} (rows : Fin r→Type*) [∀t,Fintype (rows t)]
    (site : ∀t,rows t→Fin count) (bits : ∀t,rows t→ℕ) (index : (Σt,rows t)≃Fin n)
    (time : r≤fuel) (bounded : ∀t v,bits t v≤payload)
    (separate : ∀t a b,0<bits t a → 0<bits t b → site t a=site t b → a=b) (i : Fin count) :
    (∑ j : Fin n,if site (index.symm j).1 (index.symm j).2=i then
      bits (index.symm j).1 (index.symm j).2 else 0)≤fuel*payload := by
  have atTime (t : Fin r) : (∑v,if site t v=i then bits t v else 0)≤payload := by
    by_cases active : ∃v,site t v=i ∧ 0<bits t v
    · obtain ⟨v,atSite,pos⟩ := active
      rw [Finset.sum_eq_single v]
      · simpa [atSite] using bounded t v
      · intro u _ different
        by_cases equal : site t u=i
        · have zero : bits t u=0 := by
            by_contra nonzero
            exact different (separate t u v (Nat.pos_of_ne_zero nonzero) pos (equal.trans atSite.symm))
          simp [equal,zero]
        · simp [equal]
      · simp
    · have empty (v : rows t) : (if site t v=i then bits t v else 0)=0 := by
        split_ifs with atSite
        · exact Nat.eq_zero_of_not_pos (fun pos=>active ⟨v,atSite,pos⟩)
        · rfl
      simp [empty]
  let cost : (Σ t,rows t)→ℕ := fun x=>if site x.1 x.2=i then bits x.1 x.2 else 0
  have moved : (∑ j,if site (index.symm j).1 (index.symm j).2=i then
    bits (index.symm j).1 (index.symm j).2 else 0)=∑ x,cost x := index.symm.sum_comp cost
  rw [moved,Fintype.sum_sigma]
  exact (Finset.sum_le_sum (fun t _=>atTime t)).trans (by
    simpa using Nat.mul_le_mul_right payload time)

end Hierarchy.ProtocolRAM.ReserveUse

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical
variable {w n count : ℕ}

/-- The global negative debit bit count is invariant under the native
owner-addressed scatter, even with repeated owners and zero archived widths. -/
theorem sum_reported_debits (a : ReserveUse.Archive) (b : RouteSettlement.Banks)
    (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ) (m : Memory w)
    (ok : ReserveUse.Mounted a b reserve site debit m)
    (sizeUsed : count≤b.used.size) (sizeReserved : count≤b.reserved.size)
    (bound : ∀i,(∑j,if site j=i then debit j else 0)≤reserve) (wide : reserve<2^w) :
    ∑i : Fin count,RouteSettlement.actual b.used (ReserveUse.output a b reserve site debit m) i.val=
      ∑j,debit j := by
  have read (i : Fin count) := (ReserveUse.reported a b reserve site debit m ok i sizeUsed sizeReserved (bound i) wide).1
  simp only [read]
  rw [Finset.sum_comm]
  simp

end Hierarchy.ProtocolRAM.Calendar

end
end OAI
