import OAI.Hierarchy.DescentResetTrunkGather
import OAI.Hierarchy.DescentResetTrunkIssue
import OAI.Hierarchy.DescentResetTrunkScalar
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # The unconditional native programs for both parts of the trunk date -/
namespace Hierarchy.DescentResetTrunkScalar
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip DescentDyadicSpan ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentFallbackRankRAM DescentSortedRoster
open scoped Classical Fin.CommRing
noncomputable section

def phase (w H b base : ℕ) (peer : Fin 3→Expr) (left right core : Expr) : NativePhase w:=
  let e:=header b H peer left right core
  ⟨scan w base H e,4+H*(2*e.work+4),ProtocolRAM.image base H e,@scan_cheap _ _ _ _⟩

theorem any {w : ℕ} (H b base : ℕ) (peer : Fin 3→Expr) (left right core : Expr) (m : Memory w)
    (old : ∀i,(peer i).Fits w base) (l : left.Fits w base) (r : right.Fits w base)
    (c : core.Fits w base) (room : base+H<2^w) :
    let p:=phase w H b base peer left right core
    p.Runs m ∧ (∀x,x<base ∨ base+H≤x→p.image m x=m x) ∧
      DescentStaticWordColumn.names p.program=11+4*(header b H peer left right core).work:=by
  exact ⟨scan_exec _ _ _ _ (fits _ _ _ _ old l r c) room,
    ProtocolRAMGeneratedWrite.frame_image base H (header b H peer left right core) m,
    DescentStaticWordColumn.names_scan w base H (header b H peer left right core)⟩

/-- The stem neighbors, left/right and core are each one indexed header word. -/
def tableWork:=(header 0 0 (fun _=>.lookup ⟨0,0⟩ .row)
  (.lookup ⟨0,0⟩ .row) (.lookup ⟨0,0⟩ .row) (.lookup ⟨0,0⟩ .row)).work

private theorem unlessSeen_work_congr {α : Type*} (f g : α → Expr)
    (same : ∀ i, (f i).work = (g i).work)
    {x y a b : Expr} (xy : x.work = y.work) (ab : a.work = b.work)
    (xs : List α) :
    (unlessSeen x a (xs.map f)).work = (unlessSeen y b (xs.map g)).work := by
  induction xs with
  | nil => exact ab
  | cons i is ih =>
    change (f i).work + x.work + 1 + (unlessSeen x a (is.map f)).work + 1 =
      (g i).work + y.work + 1 + (unlessSeen y b (is.map g)).work + 1
    rw [same i, xy, ih]

private theorem foldSum_work_congr {α : Type*} (f g : α → Expr)
    (same : ∀ i, (f i).work = (g i).work) (xs : List α) :
    (foldSum (xs.map f)).work = (foldSum (xs.map g)).work := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    change (f i).work + (foldSum (is.map f)).work + 1 =
      (g i).work + (foldSum (is.map g)).work + 1
    rw [same i, ih]

private theorem calculate_work_congr {D : ℕ} (f g : Fin D → Expr)
    (same : ∀ i, (f i).work = (g i).work)
    {x y : Expr} (xy : x.work = y.work) :
    (calculate f x).work = (calculate g y).work := by
  unfold calculate
  apply foldSum_work_congr
  intro i
  unfold rankBit
  apply unlessSeen_work_congr f g same (same i)
  change (f i).work + x.work + 1 + 1 + 1 = (g i).work + y.work + 1 + 1 + 1
  rw [same i, xy]

private theorem shifted_work_congr (b b' : ℕ) (j : Fin 7) (e e' : Expr)
    (he : e.work = e'.work) : (shifted b j e).work = (shifted b' j e').work := by
  simp only [shifted, chooseField, Expr.work, he]

private theorem split_total_work_congr {α : Type*} (f g : α → Expr)
    (hf : ∀ i, (f i).work = (g i).work) (xs : List α) :
    (DescentColonies.SplitRAM.total f xs).work = (DescentColonies.SplitRAM.total g xs).work := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    change (f i).work + (DescentColonies.SplitRAM.total f is).work + 1 =
      (g i).work + (DescentColonies.SplitRAM.total g is).work + 1
    rw [hf i, ih]

theorem table_work (b H : ℕ) (peer : Fin 3→Bank) (left right core : Bank) :
    (header b H (fun i=>.lookup (peer i) .row) (.lookup left .row) (.lookup right .row) (.lookup core .row)).work = tableWork := by
  let src := fun i : Fin 3 => Expr.lookup (peer i) .row
  let ref := Expr.lookup ⟨0,0⟩ .row
  let baseSrc := fun _ : Fin 3 => ref
  let inputs := values src (.lookup left .row) (.lookup right .row) (.lookup core .row)
  let dummy := values baseSrc ref ref ref
  have sources (i : Fin 4) : (full src i).work = (full baseSrc i).work := by
    cases i using Fin.cases <;> rfl
  have rankCost (x y : Expr) (h : x.work = y.work) :
      (calculate (full src) x).work = (calculate (full baseSrc) y).work :=
    calculate_work_congr _ _ sources h
  have fields (j : Fin 7) : (inputs j).work = (dummy j).work := by
    fin_cases j
    · rfl
    · exact rankCost (.lookup left .row) ref rfl
    · exact rankCost (.lookup right .row) ref rfl
    · exact rankCost .row .row rfl
    · rfl
    · rfl
    · rfl
  have cost := split_total_work_congr (fun j => shifted b j (inputs j))
    (fun j => shifted 0 j (dummy j)) (fun j => shifted_work_congr _ _ j _ _ (fields j))
    (List.finRange 7)
  exact congrArg (fun q : ℕ => (Expr.lookup left .row).work + 1 + q + 1 + 1) cost

end
end Hierarchy.DescentResetTrunkScalar

namespace Hierarchy.DescentResetTrunkIssue
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip DescentDyadicSpan ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H w : ℕ}

def phase (w base b M : ℕ) : NativePhase w:=
  ⟨program base b M w,4+10*(3*2^(width b M)),memory base b M,
    DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _⟩

def suffix (w base b G M : ℕ) (alt : Fin H→Option (Fin H)) : NativePhase w:=
  (DescentResetTrunkGather.phase w base G M alt).seq (phase w (base+span (H*chunks G M)) b M)

theorem any (base b G M : ℕ) (alt : Fin H→Option (Fin H)) (m : Memory w)
    (room : endAddress (base+span (H*chunks G M)) b M<2^w) :
    let n:=H*chunks G M
    let latch:=base+span n
    let top:=endAddress latch b M
    let p:=suffix w base b G M alt
    p.Runs m ∧ (∀x,x<base ∨ top≤x→p.image m x=m x) ∧
      p.ticks=(4+10*n)+(4+10*(3*2^(width b M))) ∧
      DescentStaticWordColumn.names p.program=15*(n+1)+15*(3*2^(width b M)+1):=by
  intro n latch top p
  let gather:=DescentResetTrunkGather.phase w base G M alt
  let ready:=gather.image m
  have ll : latch≤top:=Nat.le_add_right ..
  have low : base≤latch:=Nat.le_add_right ..
  have whole:=DescentResetTrunkGather.run (b:=0) (G:=G) (M:=M) alt base m (ll.trans_lt room)
  have bill:=DescentOrdinaryAtomFieldRAM.ROM.run (pages b M) (width b M) latch ready room
  have frame:=DescentOrdinaryAtomFieldRAM.ROM.frame (pages b M) (width b M) latch ready
  refine ⟨NativePhase.seq_runs gather (phase w latch b M) m whole.1 bill.1,?_,rfl,?_⟩
  · intro x here
    rcases here with before|after
    · exact (frame x (.inl (before.trans_le low))).trans (whole.2.1 x (.inl before))
    · exact (frame x (.inr after)).trans (whole.2.1 x (.inr
        ((Nat.add_le_add_left (span_ge n) base).trans (ll.trans after))))
  · change DescentStaticWordColumn.names (gather.program.seq (program latch b M w))=_
    rw [DescentStaticWordColumn.names_seq]
    exact congrArg₂ (·+·) (DescentStaticWordColumn.names_mount w base (DescentResetTrunkGather.address alt G M) n) bill.2

end
end Hierarchy.DescentResetTrunkIssue

end OAI
