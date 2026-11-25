import OAI.Hierarchy.TaggedWideNativeSeries
import OAI.Hierarchy.ProtocolRAMFrozenWindowRun

namespace OAI
/-! # Common-memory readbacks for every frozen positive format -/

noncomputable section
namespace Hierarchy.ProtocolRAMFrozenWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing CallPool RAM RAM.DescriptorExpr PhysicalProcedure
open ProtocolRAM ProtocolRAMReportedPorts TaggedShorterGroups TaggedShorterReportedPublish
open TaggedShorterReportAdvice ProtocolRAMTranslatedKey
open scoped Classical Fin.CommRing BigOperators

variable {W : ℕ}

structure Format.Resident (f : Format) (W floor : ℕ) (a : Inputs) : Prop where
  owner : a.owner.Fits W floor
  inputs : ∀b∈[a.directory,a.offset,a.left,a.right,a.width,a.bias,a.classes,a.weights,a.origins],b.Fits W floor
  rom : ∀j : Fin 13,(bank f.rom f.bits j).Fits W floor

variable {f : Format} {floor r : ℕ} {a : Inputs} {m₀ m : Memory W}
    (live : f.Resident W floor a) (keep : ∀u<floor,m u=m₀ u)
    (old : Fin f.N → ProtocolRAMEmit.Row)

include keep in
private theorem read_bank {b : Bank} (h : b.Fits W floor) (x : Word W) : b.read m x=b.read m₀ x :=
  keep _ ((Nat.add_lt_add_left (Nat.mod_lt x.val h.1) _).trans_le h.2.2)

include live keep in
theorem Format.Resident.rows_eq : f.rows a m old=f.rows a m₀ old := by
  let same := fun i:Fin f.N=>ProtocolRAM.eval_below a.owner (i.val:Word W) m₀ m live.owner keep
  dsimp only [Format.rows]
  apply congrArg (ProtocolRAMPackedPlacement.translated old)
  funext i
  rw [same,read_bank keep (live.inputs a.directory (by simp))]

include live keep in
theorem Format.Resident.starts_eq : f.starts a m=f.starts a m₀ := by
  funext b i
  have same := ProtocolRAM.eval_below a.owner (i.val:Word W) m₀ m live.owner keep
  cases b <;> simp only [Format.starts,same,Bool.false_eq_true,ite_false,ite_true,
    read_bank keep (live.inputs a.offset (by simp)),read_bank keep (live.inputs a.right (by simp)),
    read_bank keep (live.inputs a.left (by simp))]

include live keep in
theorem Format.Resident.words (data : f.InputWords r a old m₀) : f.InputWords r a old m where
  width i := (read_bank keep (live.inputs _ (by simp)) _).trans (data.width i)
  bias i := (read_bank keep (live.inputs _ (by simp)) _).trans (data.bias i)
  classes i := (read_bank keep (live.inputs _ (by simp)) _).trans (data.classes i)
  copies i := (read_bank keep (live.inputs _ (by simp)) _).trans (data.copies i)
  tables j x hx := (read_bank keep (live.rom j) _).trans (data.tables j x hx)
  origins i := (read_bank keep (live.inputs _ (by simp)) _).trans (data.origins i)

abbrev Format.Cell (f : Format) := TaggedShorterSlotWidth.Slot f.groups f.D ⊕ TaggedShorterScatter.Field f.window.C f.D

def Format.address (f : Format) (r : ℕ) : f.Cell→ℕ :=
  Sum.elim (TaggedShorterSlotWidth.index (f.window.widthBase r))
    (fun x=>f.window.base r+(TaggedShorterScatter.fieldIndex f.window.C f.D x).val)

theorem Format.cell_bound (f : Format) (r : ℕ) (p : f.Cell) : f.address r p< r+f.window.stop 0 := by
  rw [←f.window.stop_add]
  cases p with
  | inl x=>
    have lt := (TaggedShorterSlotWidth.index_bounds (f.window.widthBase r) x).2
    change TaggedShorterSlotWidth.index (f.window.widthBase r) x < _
    dsimp [Size.stop,Size.widthSrc,Size.src,Size.widthWords,Size.tape]
    exact lt.trans_le (by simp [Format.window];omega)
  | inr x=>
    have lt : (TaggedShorterScatter.fieldIndex f.window.C f.D x).val < f.window.maskWords :=
      (TaggedShorterScatter.fieldIndex f.window.C f.D x).isLt
    have endBoard : f.window.base r+f.window.maskWords ≤ f.window.stop r := by
      unfold Size.stop Size.widthSrc Size.src Size.widthBase
      omega
    exact (Nat.add_lt_add_left lt (f.window.base r)).trans_le endBoard

structure Format.Anchored (f : Format) (a : Inputs) (m : Memory W) (old : Fin f.N → ProtocolRAMEmit.Row)
    (limits : f.Limits W old) where
  groupFit : ∀i,0<pieces old f.w i → (f.rows a m old i).group<f.groups
  bound : ∀g : Fin f.groups,size (f.rows a m old) f.w f.menu f.γ g ≤ f.D
  pl : ∀g : Fin f.groups,Bool → Fin (size (f.rows a m old) f.w f.menu f.γ g) ↪ Fin f.D
  located : ∀b (g : Fin f.groups) (u : Unit (f.rows a m old) f.w f.menu f.γ g.val),
    (pl g b (common (f.rows a m old) f.w f.menu f.γ g.val limits.order.injective u)).val=f.starts a m b u.1.val+u.2.val

def Format.Anchored.word {limits : f.Limits W old} (A : f.Anchored a m₀ old limits) : f.Cell → Word W :=
  Sum.elim (fun x=>(TaggedShorterSlotWidth.value A.pl (TaggedShorterSlotWidth.reportWidth (f.rows a m₀ old) f.w f.menu f.γ limits.order.injective) x:Word W))
    (fun x=>(TaggedShorterScatter.contents _ A.bound limits.batch limits.idFits A.pl x:Word W))

include live keep in
theorem Format.Anchored.run (ready : f.Ready W r a) (data : f.InputWords r a old m₀)
    (limits : f.Limits W old) (A : f.Anchored a m₀ old limits) :
    ∃out,(f.phase W r a).Exec m out (f.clock r a) ∧
      (∀p,out (f.address r p)=A.word old p) ∧ ∀u< r,out u=m u := by
  have run := f.run W r a old m ready (live.words keep old data) limits
  have groups :
      (fun i : Fin f.N => (a.directory.read m (a.owner.eval m (i.val:Word W))).val) =
      (fun i : Fin f.N => (a.directory.read m₀ (a.owner.eval m₀ (i.val:Word W))).val) :=
    congrArg (fun rows : Fin f.N → ProtocolRAMEmit.Row => fun i => (rows i).group) (live.rows_eq keep old)
  unfold Format.rows at run
  rw [groups,live.starts_eq keep] at run
  obtain ⟨out,exec,slot,field,frame⟩ := run A.groupFit A.bound A.pl A.located
  refine ⟨out,exec,?_,frame⟩
  intro p
  cases p with
  | inl x => exact slot x
  | inr x => exact field x

/-- All original role/owner banks, observations and signed term words stay in their
own address space throughout all variable data-dependent format runs. -/
theorem frozen_series {m : ℕ} (f : Fin (m+1) → Format) (floor : ℕ) (m₀ : Memory W)
    (a : Fin (m+1) → Inputs) (old : ∀j,Fin (f j).N → ProtocolRAMEmit.Row)
    (limits : ∀j,(f j).Limits W (old j)) (A : ∀j,(f j).Anchored (a j) m₀ (old j) (limits j))
    (resident : ∀j,(f j).Resident W floor (a j)) :
    let need := fun j=>(f j).window.stop 0
    let atRow := WindowSeries.start floor need
    let phase := fun j=>(f j).phase W (atRow j) (a j)
    let clock := fun j=>(f j).clock (atRow j) (a j)
    (∀j,(f j).Ready W (atRow j) (a j)) → (∀j,(f j).InputWords (atRow j) (a j) (old j) m₀)→
    ∃out,(ProcedureBank.program m phase).Exec m₀ out (∑j,clock j) ∧
      (∀j p,out ((f j).address (atRow j) p)=(A j).word (old j) p) ∧ ∀u<floor,out u=m₀ u := by
  intro need atRow phase clock fit data
  let board (j : Fin (m+1)) (u : ℕ) := ∃p,(f j).address (atRow j) p=u
  let reads (j : Fin (m+1)) (u : ℕ) (v : Word W) := ∀p,(f j).address (atRow j) p=u → v=(A j).word (old j) p
  obtain ⟨out,exec,fields,prior⟩ := WindowSeries.run floor need phase clock m₀ board reads
    (by rintro j _ ⟨p,rfl⟩;exact (f j).cell_bound _ p) (by
      intro j s keep
      obtain ⟨t,ran,read,frame⟩ := (A j).run (resident j) keep (old j) (fit j) (data j) (limits j)
      exact ⟨t,ran,fun u _ p h=>h ▸ read p,frame⟩)
  exact ⟨out,exec,fun j p=>fields j _ ⟨p,rfl⟩ p rfl,prior⟩

end Hierarchy.ProtocolRAMFrozenWindow

end
end OAI
