import OAI.Computability.BorderVNP.PackedFrozenNamedKernel

/-! # Guard and geometry of the native tape node on arbitrary histograms

The work-width and record writers retain the geometric circuit's outputs
for every child array and every guessed histogram. On admissible child
geometry the retained guard therefore recognizes the named run's codec.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Shortening.StaticRows PackedHistoryCircuit VPVNP.VerifierNetwork
open private shape from OAI.Computability.BorderVNP.PackedInheritedWorkJoint
open scoped Classical

private theorem jointAt_project {D m k V V' E n np w : ℕ} [NeZero D] {K : Type} [Field K]
    {A B Old : Type} [Fintype A] [Fintype B] [Fintype Old]
    (e : Crossing.PaidIdentity K D m) (seed : A ↪ Fin n) (p : Ports np)
    (eq : V' = siteCapacity e (k*V) n) (fit : V' ≤ 2^w)
    (geom : Frame ((Fin k × Old) ⊕ (A × Fin e.count × Fin w)) (SavedPins B V' E w ⊕ Unit))
    (y : Fin k → WithWidths Old V w → Bool) (g : A × Fin e.count × Fin w → Bool)
    (z : SavedPins B V' E w ⊕ Unit) :
    (jointAt e seed p eq fit geom).eval (Sum.elim (fun t => y t.1 t.2) g) (Sum.map Sum.inl id z) =
      geom.eval (Sum.elim (fun t => y t.1 (.inl t.2)) g) z := by
  subst V'
  let x := Sum.elim (fun t : Fin k × WithWidths Old V w => y t.1 t.2) g
  have hx : (Frame.initial id).eval x = x := funext (Frame.initial_eval id x)
  have projected : (shape (k := k) (V := V) (n := n) (E := E) (w := w) (A := A) (B := B) (Old := Old) e geom).eval x =
      geom.eval (Sum.elim (fun t => y t.1 (.inl t.2)) g) := by
    funext z
    rw [shape, Frame.subst_eval]
    congr 1
    funext t
    cases t <;> exact Frame.initial_eval _ x _
  change (jointNode e seed (p.parallel k V).host (p.parallel k V).width fit geom).eval x _ = _
  rcases z with z | u
  · simp only [Sum.map_inl, jointNode, Retained.joint_geometry, hx, projected]
  · cases u
    simp only [Sum.map_inr, id_eq, jointNode, Retained.joint_flag, hx, projected]

end Packing.Inherited.WorkWords

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Shortening.PublicDenseReceipt
open Shortening.StaticRows Epoch Epoch.Round Packing Packing.Inherited Packing.Inherited.FrozenTape
open Packing.Inherited.WorkWords NamedKernel Physical VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {D m b k last high w np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {V E cap : ℕ → ℕ}
    {Extra : ℕ → Type*} {keep : ∀ j,path.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b,path.Node last high V E w k i} (r : path.NamedRun last high V E w cap keep hk nodes)
    (i : Fin b) (S : Format) (header : WorkWords.Ports np) (leaf : P ↪ Fin np)

local notation3 (prettyPrint := false) "A" i => Shortening.PublicDenseReceipt.Seed (path.pattern i).bins
  (path.asPath.depth last high (Fin.val i+1))
local notation3 (prettyPrint := false) "geo" j => path.StatePins last high V E w j
local notation3 (prettyPrint := false) "ww" j => WithWidths (geo j) (V j) w
local notation3 (prettyPrint := false) "child" => S.Output (geo i.val) (V i.val) w w

variable (rect : ∀ j : Fin b,V (j.val+1)=siteCapacity e (k*V j.val) (Fintype.card (ProgramSchemas.Seeds path last high j)))
    (edgeRect : ∀ j : Fin b,E (j.val+1)=edgeCapacity e (k*E j.val) (Fintype.card (ProgramSchemas.Seeds path last high j)))
    (fits : ∀ j : Fin b,V (j.val+1) ≤ 2^w) (hm : 0 < m)
variable (y : Fin k → S.Output (path.StatePins last high V E w i.val) (V i.val) w w → Bool)
    (g : Words (ProgramSchemas.Seeds path last high i) e.count w → Bool)

local notation3 (prettyPrint := false) "result" => node r i S header leaf rect edgeRect fits hm
local notation3 (prettyPrint := false) "full" => Sum.elim (fun t : Fin k × child => y t.1 t.2) g
local notation3 (prettyPrint := false) "prior" => fun t : Fin k × geo i.val => y t.1 (.inl (.inl t.2))

private theorem widthStep_project (z : (geo (i.val+1)) ⊕ Unit) :
    (widthStep r i S header rect fits).eval full (Sum.map Sum.inl id z) = (nodes i).eval (Sum.elim prior g) z := by
  let select := Sum.map (fun t : Fin k × ww i.val => ((t.1,Sum.inl t.2) : Fin k × child)) (id : Words (A i) e.count w → _)
  let old := fun (j : Fin k) (t : ww i.val) => y j (.inl t)
  have assigned : (Frame.initial select).eval full = Sum.elim (fun t => old t.1 t.2) g := by
    funext t
    cases t <;> exact Frame.initial_eval select full _
  unfold widthStep
  rw [Frame.subst_eval, assigned]
  exact WorkWords.jointAt_project e (r.widthSeed i).toEmbedding (header.nested k V i.val) (rect i) (fits i)
    (nodes i) old g z

/-- The native node tests every guess with the named geometric circuit's own guard. -/
theorem node_guard : (result).eval full (.inr ()) = (nodes i).eval (Sum.elim prior g) (.inr ()) := by
  unfold node nodeWith
  rw [Shared.install_guard]
  exact widthStep_project r i S header rect fits y g (.inr ())

/-- Every geometry output of the native node agrees with the named geometric circuit
on the projected children and the same guessed histogram. -/
theorem node_geometry (z : geo (i.val+1)) :
    (result).eval full (.inl (.inl (.inl z))) = (nodes i).eval (Sum.elim prior g) (.inl z) := by
  unfold node nodeWith
  rw [Shared.install_widths]
  exact widthStep_project r i S header rect fits y g (.inl z)

local notation3 (prettyPrint := false) "pins" => Pin (Cube D) (fun t => (path.pattern t).bins.Bin)
  (path.asPath.depth last high) e.count (fun _ => w) i.val
local notation3 (prettyPrint := false) "pin" => pinEquiv (I := Cube D) (B := fun t => (path.pattern t).bins.Bin)
  (depth := path.asPath.depth last high) (e := e) (fun _ => w) i

/-- On represented child geometry, the native guard accepts exactly the named
program's canonical histogram words in the scheduler's coordinates. -/
theorem node_guard_iff (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
    (guess : pins → Bool) (rep : ∀ j : Fin k, (fun z : geo i.val => y j (.inl (.inl z))) = (c j).val.words) :
    (result).eval (Sum.elim (fun t : Fin k × child => y t.1 t.2) (guess ∘ pin)) (.inr ()) = true ↔
      ∃ q, guess = (r.program.codec r.fits).word i.val i.isLt c q := by
  rw [node_guard r i S header leaf rect edgeRect fits hm y]
  have h := congrFun (scheduled_eval (nodes i) pin id prior guess) (.inr ())
  have valid := r.correct.valid i.val i.isLt c (fun j z => y j (.inl (.inl z))) guess rep
  change (scheduled (nodes i) pin id).eval (Sum.elim prior guess) (.inr ()) = true ↔ _ at valid
  exact (congrArg (· = true) h.symm).to_iff.trans valid

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
