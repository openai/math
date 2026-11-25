import OAI.Computability.BorderVNP.PackedFrozenNamedSteps
import OAI.Computability.BorderVNP.PackedFrozenNamedRead

/-! # Transporting complete native reads onto the scheduled histogram pins -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.StaticRows
open Packing Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords InheritedBank NamedKernel Physical
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

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
local notation3 (prettyPrint := false) "native" i => node r i (fmt (Fin.val i)) header leaf rect edgeRect fits hm

private theorem read_cast (bound : ℕ → ℕ) (j : ℕ) (a : NamedState.Admissible (src.NamedGood last high V E w cap keep) j)
    (p : Site.Programs a.val.placed.pack.layout) {F G : Format} (same : F = G)
    (y : G.Output (geo j) (V j) w w → Bool) (read : Read header leaf bound j G a p y) :
    Read header leaf bound j F a p (y ∘ cast (congrArg (fun S : Format => S.Output (geo j) (V j) w w) same)) := by
  cases same
  exact read

/-- After transporting the physical output pins to the equal cumulative
format, the same complete read is available on its new numbering. -/
theorem Read.of_reindex (bound : ℕ → ℕ) (j : ℕ) (a : NamedState.Admissible (src.NamedGood last high V E w cap keep) j)
    (p : Site.Programs a.val.placed.pack.layout) {F G : Format} (same : F = G)
    (y : G.Output (geo j) (V j) w w → Bool)
    (read : Read header leaf bound j F a p (y ∘ cast (congrArg (fun S : Format => S.Output (geo j) (V j) w w) same))) :
    Read header leaf bound j G a p y := by cases same; exact read

variable (seeds : ∀ i : Fin b, ProgramSchemas.Seeds src last high i → ℕ) (number : e.Entry → ℕ)
variable (bound : ℕ → ℕ) (i : Fin b) (c : Fin k → NamedState.Admissible (src.NamedGood last high V E w cap keep) i.val)
variable (q : (r.program.stage i c).Index e)
variable (old : ∀ j, Site.Programs (c j).val.placed.pack.layout)
variable (y : Fin k → (ProgramSchemas.inner src last high k E np w base i.val).Output
    (src.StatePins last high V E w i.val) (V i.val) w w → Bool)
local notation3 (prettyPrint := false) "saved" => r.program.savePrivatePrograms r.saveNames
  (r.privateSiteRows leaf seeds) number i c q old
local notation3 (prettyPrint := false) "g" => (r.program.codec r.fits).word i.val i.isLt c q
local notation3 (prettyPrint := false) "localWord" => NamedReceipt.word (r.program.stage i c) (r.fits i c) q
local notation3 (prettyPrint := false) "assign" => Sum.elim (fun z : Fin k × pins i.val => y z.1 z.2)

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 4500 in
/-- A genuine local histogram is read on the scheduled pins at exactly its
canonical count word. This transports the full physical read through the
successor-format equality. -/
theorem steps_read_of_node
    (checked : Read header leaf bound (i.val+1) (ProgramSchemas.innerRound src last high k E np w i (fmt i.val))
      (r.program.advance i c q) saved (((native i).eval (assign localWord)) ∘ Sum.inl)) :
    Read header leaf bound (i.val+1) (fmt (i.val+1)) (r.program.advance i c q) saved
      (((steps r base header leaf rect edgeRect fits hm i.val i.isLt).eval (assign g)) ∘ Sum.inl) := by
  let guess := pinEquiv (I := Cube D) (B := fun t => (src.pattern t).bins.Bin)
    (depth := src.asPath.depth last high) (e := e) (fun _ => w) i
  let same := ProgramSchemas.inner_next src last high k E np w base i
  let back := cast (congrArg (fun F : Format => F.Output (geo (i.val+1)) (V (i.val+1)) w w) same)
  have hw : g ∘ guess = localWord := word_at_pin (B := fun t => (src.pattern t).bins.Bin)
    (lev := src.asPath.depth last high) (w := fun _ => w) i (r.program.stage i c) (r.fits i c) q
  have eval := scheduled_eval (native i) guess back (fun z : Fin k × pins i.val => y z.1 z.2) g
  rw [hw] at eval
  have eqn : ((steps r base header leaf rect edgeRect fits hm i.val i.isLt).eval (assign g)) ∘ Sum.inl =
      ((native i).eval (assign localWord) ∘ Sum.inl) ∘ back := funext fun z => congrFun eval (.inl z)
  rw [eqn]
  exact read_cast header leaf bound (i.val+1) (r.program.advance i c q) saved same _ checked

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
