import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloPhysical
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloRip

/-! # Automatic filling from the first binary stock record -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary.Ticket
open IntegerMultiplication Code Strip Strip.Dims Loom Adic
open BinaryHalo CommonRegisters Space BoxMaskedRecords

noncomputable section

abbrev DenseKey (x : Ticket) := SpanKey x.P x.G x.B (Block 2 x.n)
abbrev HaloKey (x : Ticket) := SpanKey x.P x.G x.B (Block x.b x.e)
abbrev haloStock (x : Ticket) := stock x.b x.P x.G x.B x.e

abbrev denseChart (x : Ticket) := nativeView x.grid x.grid.D 2 x.n x.P x.G x.B rfl rfl rfl rfl
abbrev haloChart (x : Ticket) := nativeView x.grid x.grid.E x.b x.e x.P x.G x.B rfl rfl rfl rfl

private theorem count_dense (x : Ticket) : x.rows.count = x.grid.denseVolume := by
  have H := congrArg List.length (((denseChart x).route fun _ => ()).trans (series_tab _))
  simpa only [Series.card,stream,List.length_ofFn,Shape.denseVolume] using H

private theorem dense_pos (x : Ticket) : 0 < x.rows.count := by
  rw [count_dense, Shape.denseVolume]
  obtain ⟨hP,hD,hG,hB,_⟩ := grid_good x
  positivity

/-- The first genuine record, in the native binary order. -/
def firstRow (x : Ticket) : DenseKey x := x.rows.index.symm ⟨0,dense_pos x⟩

def extendFirst {A : Type} (x : Ticket) (f : DenseKey x → A) : HaloKey x → A :=
  BinaryHalo.extend (denseChart x).cast (haloChart x).cast (f (firstRow x)) f

theorem extendFirst_map {A B : Type} (x : Ticket) (F : A → B) (f : DenseKey x → A) :
    extendFirst x (F ∘ f) = F ∘ extendFirst x f :=
  extend_map (denseChart x).cast (haloChart x).cast F (f (firstRow x)) f

theorem extendFirst_prop {A : Type} (x : Ticket) (f : DenseKey x → A) (Q : A → Prop)
    (h : ∀ i, Q (f i)) (j : HaloKey x) : Q (extendFirst x f j) := extend_prop _ _ Q (h _) h j

variable (f : (x : Ticket) → DenseKey x → Tree) (w : Ticket → ℕ)
variable (sized : ∀ x i, (f x i).count ≤ w x)

def autoCost (x : Ticket) := scanVolume x.total (w x)

def autoInput (grow : Bool) (x : Ticket) : Tree := .fork (send x.grid.header)
  (if grow then stripe x.rows (f x) else stripe x.haloStock (extendFirst x (f x) ∘ swapper _ _ _))

def autoOutput (grow : Bool) (x : Ticket) : Tree :=
  if grow then stripe x.haloStock (extendFirst x (f x)) else stripe x.rows (f x ∘ swapper _ _ _)

private theorem dense_len (x : Ticket) : x.rows.count ≤ x.total := by
  rw [count_dense]; unfold Shape.denseVolume total Shape.volume; gcongr <;> exact (grid_good x).hDE

private theorem halo_len (x : Ticket) : x.haloStock.count = x.total := by
  have H := congrArg List.length (((haloChart x).route fun _ => ()).trans (series_tab _))
  simpa only [Series.card,stream,List.length_ofFn,Shape.volume] using H

private theorem first_of_list (x : Ticket) : (x.rows.tab (f x)).headD (.atom false) = f x (firstRow x) := by
  let j : Fin x.rows.count := ⟨0,dense_pos x⟩
  have hj : j.val < (x.rows.tab (f x)).length := by simpa only [Series.card] using j.isLt
  rw [List.headD_eq_head?_getD,List.head?_eq_getElem?,List.getElem?_eq_getElem hj]
  exact x.rows.get (f x) j hj

private def desc (grow : Bool) (x : Ticket) : BinaryHalo.Packet where
  shape := x.grid
  good := grid_good x
  width := w x
  rows := if grow then x.rows.tab (f x) else x.haloStock.tab (extendFirst x (f x) ∘ swapper _ _ _)
  fill := f x (firstRow x)
  length_le := by
    cases grow
    · simpa only [Bool.false_eq_true,ite_false,Series.card] using (halo_len x).le
    · simpa only [ite_true,Series.card] using dense_len x
  sized := by
    intro t ht
    cases grow
    · obtain ⟨j,rfl⟩ := (x.haloStock.elements _ _).mp ht
      exact extendFirst_prop x (f x) (fun t => t.count ≤ w x) (sized x) _
    · obtain ⟨j,rfl⟩ := (x.rows.elements _ _).mp ht
      exact sized x j
  fill_sized := sized x _

private theorem filled (x : Ticket) :
    BinaryHalo.output true (desc f w sized true x) = autoOutput f true x := by
  simp only [BinaryHalo.output,desc,autoOutput,ite_true,stripe_eq]
  rw [(denseChart x).route,series_tab,expandWith_stream (grid_good x).hDE,(haloChart x).route,series_tab]
  apply congrArg (fun g => send (stream g)); funext y; simp [extendFirst,extend]

private theorem cropped (x : Ticket) :
    BinaryHalo.output false (desc f w sized false x) = autoOutput f false x := by
  simp only [BinaryHalo.output,desc,autoOutput,Bool.false_eq_true,ite_false,stripe_eq]
  rw [(haloChart x).route,series_tab,compress_stream (grid_good x).hDE,(denseChart x).route,series_tab]
  apply congrArg (fun g => send (stream g)); funext y
  have hy : occupied (swap (embed (grid_good x).hDE y)) := ⟨y.2.2.2.1.isLt,y.2.1.isLt⟩
  change extendFirst x (f x) ((haloChart x).cast (swap (embed (grid_good x).hDE y))) =
    f x ((denseChart x).cast (swap y))
  simp only [extendFirst,extend,Function.comp_apply,Equiv.symm_apply_apply,padded,hy,↓reduceDIte]
  rfl

include sized

/-- Uniform scan, including physical selection and duplication of the first record. -/
theorem auto_task (grow : Bool) : Task (autoCost w) (autoInput f grow) (autoOutput f grow) := by
  have run := (BinaryHalo.task grow).on (desc f w sized grow)
  cases grow
  · exact run.conform (fun _ => rfl) (fun x => by simp only [autoInput, Bool.false_eq_true, ite_false,stripe_eq]; rfl) (cropped f w sized)
  · let src (x : Ticket) := (x.grid.header, x.rows.tab (f x))
    have select : Easy (fun a : BinaryHalo.Header × List Tree => (a.1,a.2,a.2.headD (.atom false))) :=
      Easy.fst.pair (Easy.snd.pair (Easy.snd.compose (Iter.leader _)))
    have pre := select.on src
    have pre' : Task (fun x => size (src x)) (autoInput f true) (fun x => BinaryHalo.input true (desc f w sized true x)) :=
      pre.conform (fun _ => rfl) (fun x => by change _ = Tree.fork _ (stripe _ _); rw [stripe_eq]; rfl)
        (fun x => by change send (x.grid.header, x.rows.tab (f x), (x.rows.tab (f x)).headD (.atom false)) = _; rw [first_of_list]; rfl)
    have scan := pre'.compose (run.conform (fun _ => rfl) (fun _ => rfl) (filled f w sized))
    apply scan.bound 18
    intro x
    have H := BinaryHalo.input_count_le (desc f w sized true x) false
    change size (src x) ≤ 16*(autoCost w x+1) at H
    change size (src x) + autoCost w x + 1 ≤ 18*(autoCost w x + 1)
    omega

theorem autoInput_count_le (grow : Bool) (x : Ticket) :
    (autoInput f grow x).count ≤ 16*(autoCost w x+1) := by
  have hi := BinaryHalo.input_count_le (desc f w sized grow x) false
  cases grow <;> simpa [autoInput,BinaryHalo.input,BinaryHalo.cost,autoCost,desc] using hi

/-- Both directions are physical subroutines charged to the binary data and the compact descriptor.
The row widths may include any fixed polynomial descriptor padding allowed by the native stage. -/
theorem auto_rip {k C : ℕ} (hw : ∀ x, w x ≤ C*(x.w+pad k x+1)) (grow : Bool) :
    Rip regime total (fun x => x.w) (autoInput f grow) (autoOutput f grow) :=
  halo_task_rip hw (halo_alive w hw (autoInput_count_le f w sized grow)) (auto_task f w sized grow)

/-- A fixed register cap for the two directions, including first-record selection. -/
theorem native_auto_commands : ∃ R : ℕ, ∃ cmd : Bool → Cmd, ∃ C : ℕ, ∀ grow, Within R (cmd grow) ∧
    ∀ x env r base, DeckCap base r → let T := C*(autoCost w x+1)
    BoundedFits env (cmd grow) (pile 0 (autoInput f grow x) r) (pile 0 (autoOutput f grow x) r) T (base+T) T := by
  choose cmd K run using auto_task f w sized
  obtain ⟨R,hR⟩ := Filter.Eventually.exists
    (Filter.eventually_all.mpr (fun grow => RegisterSelect.within_eventually (cmd grow)))
  let K' := max (K true) (K false)
  refine ⟨R,cmd,K'+16,fun grow => ⟨hR grow,?_⟩⟩
  intro x env r base hr
  have hK : K grow ≤ K' := by cases grow <;> simp [K']
  have hrun := ((run grow x env r).mono (Nat.mul_le_mul_right (autoCost w x+1) hK))
  have hsize := autoInput_count_le f w sized grow x
  have ht := BoundedFits.of_fits hrun (fun i => Nat.add_le_add_right (hr.pile 0 (autoInput f grow x) i) _) le_rfl
  dsimp only
  rw [Nat.add_mul]
  exact ht.mono (by omega) (by omega) (by omega)

end
end InterchangeROMBinary.Ticket

end NearSquareRoot
end Computability
end OAI
