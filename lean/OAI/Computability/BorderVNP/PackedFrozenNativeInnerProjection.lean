import OAI.Computability.BorderVNP.PackedFrozenNativeFrames
import OAI.Computability.BorderVNP.PackedFrozenNativeGuard
import OAI.Computability.BorderVNP.PackedHistoryAllWordProjection

/-! # Geometry and guard projection for the selected inner steps

The same histogram bits pass to the named node after forgetting the
immutable tape and width columns. This holds for arbitrary child tables and
arbitrary profile words, including profiles rejected by a child or parent.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.StaticRows
open Packing Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords NamedKernel Physical
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 4500

universe u
variable {D m b k np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
variable {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type u}
variable {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
variable {nodes : ∀ i : Fin b, src.Node last high V E w k i}
variable (r : src.NamedRun last high V E w cap keep hk nodes) (base : Format)
variable (header : WorkWords.Ports np) (leaf : P ↪ Fin np)
variable (rect : ∀ i : Fin b, V (i.val+1) = siteCapacity e (k*V i.val) (Fintype.card
    (ProgramSchemas.Seeds src last high i)))
variable (edgeRect : ∀ i : Fin b, E (i.val+1) = edgeCapacity e (k*E i.val) (Fintype.card
    (ProgramSchemas.Seeds src last high i)))
variable (fits : ∀ i : Fin b, V (i.val+1) ≤ 2^w) (hm : 0 < m)
local notation3 (prettyPrint := false) "fmt" j => ProgramSchemas.inner src last high k E np w base j
local notation3 (prettyPrint := false) "geo" j => src.StatePins last high V E w j
local notation3 (prettyPrint := false) "pins" j => Format.Output (fmt j) (geo j) (V j) w w
local notation3 (prettyPrint := false) "guesses" => Pin (Cube D) (fun i => (src.pattern i).bins.Bin)
  (src.asPath.depth last high) e.count (fun _ => w)

private theorem cast_geometry {F G : Format} (same : F = G) {X : Type} {v w : ℕ} (z : X) :
    cast (congrArg (fun S : Format => S.Output X v w w) same) (.inl (.inl z)) = .inl (.inl z) := by
  cases same
  rfl

private theorem scheduled_projection {k v v' w : ℕ} {A B X Y : Type} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    (prior next actual : Format) (same : next = actual) (pin : Y → B)
    (kernel : Frame ((Fin k × prior.Output A v w w) ⊕ Y) (actual.Output X v' w w ⊕ Unit))
    (node : Frame ((Fin k × A) ⊕ Y) (X ⊕ Unit))
    (hnode : ∀ (y : Fin k → prior.Output A v w w → Bool) (g : Y → Bool),
      (∀ z : X, kernel.eval (Sum.elim (fun z => y z.1 z.2) g) (.inl (.inl (.inl z))) =
        node.eval (Sum.elim (fun z => y z.1 (.inl (.inl z.2))) g) (.inl z)) ∧
      kernel.eval (Sum.elim (fun z => y z.1 z.2) g) (.inr ()) =
        node.eval (Sum.elim (fun z => y z.1 (.inl (.inl z.2))) g) (.inr ()))
    (x : (Fin k × prior.Output A v w w) ⊕ B → Bool) (result : X ⊕ Unit) :
    let back := cast (congrArg (fun F : Format => F.Output X v' w w) same)
    (scheduled kernel pin back).eval x (Sum.map (fun z => .inl (.inl z)) id result) =
    (scheduled node pin id).eval (x ∘ Sum.map (Prod.map id (fun z => .inl (.inl z))) id) result := by
  intro back
  let y := fun (a : Fin k) (z : prior.Output A v w w) => x (.inl (a,z))
  let g := fun z : B => x (.inr z)
  let child := fun z : Fin k × A => y z.1 (.inl (.inl z.2))
  have aug := scheduled_eval kernel pin back (fun z : Fin k × prior.Output A v w w => y z.1 z.2) g
  have orig := scheduled_eval node pin id child g
  have xsplit : Sum.elim (fun z : Fin k × prior.Output A v w w => y z.1 z.2) g = x := by funext z; cases z <;> rfl
  have plain : Sum.elim child g = x ∘ Sum.map (Prod.map id (fun z : A => .inl (.inl z))) id := by
    funext z; cases z <;> rfl
  rw [xsplit] at aug
  rw [plain] at orig
  rw [aug, orig]
  cases result with
  | inl z =>
    change kernel.eval _ (.inl (back (.inl (.inl z)))) = node.eval _ (.inl z)
    rw [show back (.inl (.inl z)) = .inl (.inl z) from cast_geometry same z]
    exact (hnode y (g ∘ pin)).1 z
  | inr z =>
    cases z
    exact (hnode y (g ∘ pin)).2

/-- Both geometry and the validity bit of a scheduled inner tape node agree
with the original named kernel for every assignment of its child and count pins. -/
theorem steps_project : StepsProject (fun _ z => .inl (.inl z))
    (steps r base header leaf rect edgeRect fits hm) (src.namedKernels last high V E w nodes) := by
  intro j hj x result
  let i : Fin b := ⟨j,hj⟩
  exact scheduled_projection (fmt j) (fmt (j+1)) _ (ProgramSchemas.inner_next src last high k E np w base i)
    (pinEquiv (I := Cube D) (B := fun t => (src.pattern t).bins.Bin)
      (depth := src.asPath.depth last high) (e := e) (fun _ => w) i)
    (node r i (fmt j) header leaf rect edgeRect fits hm) (nodes i)
    (fun y g => ⟨node_geometry r i (fmt j) header leaf rect edgeRect fits hm y g,
      node_guard r i (fmt j) header leaf rect edgeRect fits hm y g⟩) x result

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Inherited WorkWords FrozenTape ProgramSchemas EnrichedOuter SourcePath.NamedRun
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 4500

private theorem resize_project {k b a c : ℕ} (h : a=c) (W : ℕ → ℕ → Type) {V G : ℕ → Type}
    [∀ p i, Fintype (W p i)] [∀ i, Fintype (V i)] [∀ i, Fintype (G i)]
    (pick : ∀ p i, V i → W p i) {f : Steps k b (W a) G} {plain : Steps k b V G}
    (project : StepsProject (pick a) f plain) :
    StepsProject (pick c) (resizeSteps h W G f) plain := by
  subst c
  exact project

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (R : Compiled bits deep budget cap w)
    (base : Format) (header : WorkWords.Ports (CoverScale.sites (Cube D) start))
    (leaf : P ↪ Fin (CoverScale.sites (Cube D) start)) (wr : WidthRanges S start T w) (hm : 0 < m)
    (t : ℕ) (ht : t<T)
local notation3 (prettyPrint := false) "high" => S.high (offset S start t)
local notation3 (prettyPrint := false) "beginFmt" => installed S start w t (epoch S start w base t)
local notation3 (prettyPrint := false) "geo" j => S.source.StatePins S.last high (fun i => (before S start t i).sites)
  (fun i => (before S start t i).edges) w j
local notation3 (prettyPrint := false) "fmt(" p "," j ")" => inner S.source S.last high S.fanIn (fun i => (before S start t i).edges) p w beginFmt j
local notation3 (prettyPrint := false) "state(" p "," j ")" => (fmt(p,j)).Output (geo j) (before S start t j).sites w w

/-- The inner tape stages of the selected machine preserve the original
geometric states and guard on every histogram assignment, through the actual
transport to the public port numbering. -/
theorem stageSteps_project :
    StepsProject (fun _ z => .inl (.inl z)) (R.stageSteps base header leaf wr hm t ht)
      (R.machine t ht).step := by
  exact resize_project (input_port_count (S := S) (start := start) t) (fun p j => state(p,j))
    (fun _ _ z => .inl (.inl z))
    (NativeTape.steps_project (R.atLevel t ht).program beginFmt (header.outer S start t) (privatePorts S leaf t)
      (width_rectangle S deep ht) (tapeEdgeRectangle S deep ht) (wr.successor t ht) hm)

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
