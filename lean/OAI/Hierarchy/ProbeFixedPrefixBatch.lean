import OAI.Hierarchy.ProtocolRAMRepairHistogram

namespace OAI
/-! # Public input endpoints for finite packet and repair expressions -/
namespace Hierarchy.ProtocolRAM
noncomputable section
variable {q d cut : ℕ}

namespace InputEnd

theorem atRow (x index : Expr) (hx : x.inputEnd≤cut) (hi : index.inputEnd≤cut) :
    (x.atRow index).inputEnd≤cut := by
  induction x <;> simp_all [Expr.atRow,Expr.inputEnd]

theorem choose (n start : ℕ) (xs : Fin n→Expr) (which : Expr)
    (xsFit : ∀i,(xs i).inputEnd≤cut) (index : which.inputEnd≤cut) :
    (chooseField n start xs which).inputEnd≤cut := by
  induction n generalizing start with
  | zero=>exact Nat.zero_le _
  | succ n ih=>
    exact max_le (max_le index (Nat.zero_le _))
      (max_le (xsFit 0) (ih (start+1) (fun i=>xs i.succ) (fun i=>xsFit i.succ)))

theorem scale (n : ℕ) (x : Expr) (small : x.inputEnd≤cut) :
    (ProtocolRAM.scale n x).inputEnd≤cut := by
  induction n with
  | zero=>exact Nat.zero_le _
  | succ n ih=>exact max_le small ih

theorem menuKey (radix : ℕ) (xs : List Expr) (small : ∀e∈xs,e.inputEnd≤cut) :
    (ProtocolRAM.menuKey radix xs).inputEnd≤cut := by
  induction xs with
  | nil=>exact Nat.zero_le _
  | cons x xs ih=>
    exact max_le (small x (List.mem_cons_self ..))
      (scale _ _ (ih (fun e he=>small e (List.mem_cons_of_mem x he))))

theorem boundedMul (n : ℕ) (x value : Expr) (small : x.inputEnd≤cut) (val : value.inputEnd≤cut) :
    (ProtocolRAM.boundedMul n x value).inputEnd≤cut := by
  induction n with
  | zero=>exact Nat.zero_le _
  | succ n ih=>exact max_le (max_le val (Nat.zero_le _)) (max_le (scale (n+1) _ small) ih)

theorem totals (n : ℕ) (xs : Fin n→Expr) (small : ∀i,(xs i).inputEnd≤cut) :
    (ProtocolRAM.totals n xs).inputEnd≤cut := by
  induction n with
  | zero=>exact Nat.zero_le _
  | succ n ih=>exact max_le (small 0) (ih (fun i=>xs i.succ) (fun i=>small i.succ))

theorem ifEnough (n : ℕ) (need stock : Fin n→Expr) (yes no : Expr)
    (needs : ∀i,(need i).inputEnd≤cut) (stocks : ∀i,(stock i).inputEnd≤cut)
    (yesFit : yes.inputEnd≤cut) (noFit : no.inputEnd≤cut) :
    (ProtocolRAM.ifEnough n need stock yes no).inputEnd≤cut := by
  induction n with
  | zero=>exact yesFit
  | succ n ih=>exact max_le (max_le (stocks 0) (needs 0)) (max_le noFit
      (ih (fun i=>need i.succ) (fun i=>stock i.succ) (fun i=>needs i.succ) (fun i=>stocks i.succ)))

theorem ifHistogram (n t : ℕ) (field : Fin n→Expr) (yes no : Expr) (fields : ∀i,(field i).inputEnd≤cut)
    (yesFit : yes.inputEnd≤cut) (noFit : no.inputEnd≤cut) :
    (ProtocolRAM.ifHistogram n t field yes no).inputEnd≤cut :=
  ifEnough n field (fun _=>.lit t) _ no fields (fun _=>Nat.zero_le _)
    (max_le (max_le (totals _ _ fields) (Nat.zero_le _)) (max_le yesFit noFit)) noFit

end InputEnd

structure Batch.Before (b : Batch q d) (cut : ℕ) : Prop where
  menu : b.menu.base+b.menu.size≤cut
  termCount : b.termCount.base+b.termCount.size≤cut
  enabled : b.enabled.base+b.enabled.size≤cut
  owner : b.owner.inputEnd≤cut
  field : ∀i,(b.field i).inputEnd≤cut
  stock : ∀i,(b.stock i).inputEnd≤cut
  perCopy : ∀i,(b.perCopy i).inputEnd≤cut
  quotes : ∀x∈b.quotes,x.inputEnd≤cut

namespace Batch.Before
variable {b : Batch q d} (h : b.Before cut)
include h

theorem packet : b.packet.inputEnd≤cut :=
  max_le h.menu (InputEnd.menuKey _ _ h.quotes)

theorem need (i : Fin d) : (b.need i).inputEnd≤cut :=
  InputEnd.boundedMul _ _ _ (Nat.zero_le _) (h.perCopy i)

theorem ifSelected (yes no : Expr) (yesFit : yes.inputEnd≤cut) (noFit : no.inputEnd≤cut) :
    (b.ifSelected yes no).inputEnd≤cut :=
  max_le (max_le (max_le h.enabled h.owner) (Nat.zero_le _)) (max_le noFit
    (max_le (max_le h.packet (Nat.zero_le _)) (max_le noFit
      (InputEnd.ifEnough d b.need b.stock yes no h.need h.stock yesFit noFit))))

theorem ifPacket (yes no : Expr) (yesFit : yes.inputEnd≤cut) (noFit : no.inputEnd≤cut) :
    (b.ifPacket yes no).inputEnd≤cut := by
  apply InputEnd.ifEnough _ _ _ _ _ h.field _ (InputEnd.ifHistogram _ _ _ _ _ h.field yesFit noFit) noFit
  intro i
  exact max_le (max_le (Nat.zero_le _) (max_le h.termCount h.packet))
    (max_le (Nat.zero_le _) (Nat.zero_le _))

theorem wire (tab : Fin q→Expr) (tabs : ∀i,(tab i).inputEnd≤cut) : (b.wire tab).inputEnd≤cut :=
  h.ifSelected _ _ (h.ifPacket _ _ (InputEnd.totals q _ (fun i=>InputEnd.boundedMul b.maxWidth
    _ _ (h.field i) (tabs i))) (Nat.zero_le _)) (Nat.zero_le _)

theorem debit (i : Fin d) : (RepairHistogram.debit b i).inputEnd≤cut :=
  h.ifSelected _ _ (h.ifPacket _ _ (h.need i) (Nat.zero_le _)) (Nat.zero_le _)

theorem broadcast (table : Bank) (room : table.base+table.size≤cut) :
    (RepairHistogram.broadcastTerm b table).inputEnd≤cut :=
  h.ifSelected _ _ (h.ifPacket _ _ (max_le room h.packet) (Nat.zero_le _)) (Nat.zero_le _)

/-- The two actual sparse histogram operands after substitution at the selected
ball and dispatch by its physical input port. -/
theorem fromBatch (owner data : Bank) (dest ball port : Expr) (tabs : Fin d→Fin q→Expr)
    (ballFit : ball.inputEnd≤cut) (portFit : port.inputEnd≤cut) (tabFit : ∀i j,(tabs i j).inputEnd≤cut) :
    let col:=RepairHistogram.fromBatch owner data dest ball port b tabs
    col.credit.inputEnd≤cut ∧ col.charge.inputEnd≤cut :=
  ⟨InputEnd.choose d 0 _ port (fun i=>InputEnd.atRow _ ball (h.wire (tabs i) (tabFit i)) ballFit) portFit,
    InputEnd.choose d 0 _ port (fun i=>InputEnd.atRow _ ball (h.debit i) ballFit) portFit⟩

end Batch.Before
end
end Hierarchy.ProtocolRAM

end OAI
