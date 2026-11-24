import OAI.Computability.VPVNP.RankCoordinateDynamic
import OAI.Computability.VPVNP.RankCoordinateRootInit
import OAI.Computability.VPVNP.RankCoordinateReplacement
import OAI.Computability.VPVNP.RankCoordinateTargetPorts
import OAI.Computability.VPVNP.RankCoordinateNativeReader

/-!
# Installing the live Cramer query into its paired root banks

The four copied words are the replacement ordinal, the original monomial
index, the one-based label mark, and the target power scale. The first two
come from the greedy selector's binary register bank. Every write is to a
scalar-reader port of the numerator. Both roots, the arithmetic field advice,
and the entire denominator reader retain their initialized contents.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.ArgumentStage

open RAMTape UniversalCountStack SliceArithmetic NativeReader
open RadicalCertificate.MonomialIndex

/-- The four live Cramer arguments consist of a replacement-row index and three target-row
words. -/
abbrev Field := Unit ⊕ Fin 3
/-- The numerator workspace compares the row index and then reads either the original submatrix
or the replacement row. -/
abbrev Num (K : Type) := Replacement.Work (Submatrix.Work K)

variable {A H K D T : Type}

/-- The comparison register and the three independent inputs of the target reader. -/
def numSlot (target : Fin 3 ↪ K) : Field ↪ Num K where
  toFun := Sum.elim (fun _ ↦ .inl (.reg 1)) (fun i ↦ .inr (.aux (target i)))
  inj' := by
    rintro (⟨⟩ | i) (⟨⟩ | j) h <;> simp_all [target.injective.eq_iff]

/-- Actual physical destination of each word in the paired roots. -/
def destination (host : RootInit.RootHost D (Num K) ↪ H) (target : Fin 3 ↪ K) : Field ↪ H where
  toFun := host ∘ RootInit.readerPort ∘ Sum.inr ∘ numSlot target
  inj' := host.injective.comp (RootInit.readerPort_injective.comp
    (Sum.inr_injective.comp (numSlot target).injective))

/-- Place a working stack on the auxiliary side of the coordinate callback's bus. -/
def workPort (h : H) : Bus A H := .aux (.inr h)

private theorem workPort_injective : Function.Injective (workPort (A := A) (H := H)) :=
  fun _ _ h ↦ Sum.inr.inj (Reader.Port.aux.inj h)

/-- Offsets five and seven are the two outputs of `Dynamic.machine`. The mark
and scale may have independent advice or runtime source ports. -/
def sources (dyn : Dynamic.Host T ↪ H) (mark scale : Bus A H) : Field → Bus A H :=
  Sum.elim (fun _ ↦ workPort (dyn (.inl (.reg 5)))) ![workPort (dyn (.inl (.reg 7))), mark, scale]

/-- Only two dynamic registers are read during transport, so other registers
can be aliased to the enclosing evaluator's public ports. -/
theorem source_words_at {addr : ℕ} (dyn : Dynamic.Host T ↪ H) (mark scale : Bus A H)
    (label current next result : List Bool) (advice : Stacks A) (work : Stacks H)
    (offNext mono marked power : ℕ)
    (hnext : work (dyn (.inl (.reg 5))) = digits addr offNext)
    (hmono : work (dyn (.inl (.reg 7))) = digits addr mono)
    (hm : state label current next result advice work mark = digits addr marked)
    (hs : state label current next result advice work scale = digits addr power) :
    ∀ f, state label current next result advice work (sources dyn mark scale f) =
      Sum.elim (fun _ : Unit ↦ digits addr offNext) (TargetRead.words addr mono power marked) f := by
  rintro (⟨⟩ | i)
  · exact hnext
  · fin_cases i
    · exact hmono
    · exact hm
    · exact hs

theorem source_words {addr : ℕ} (dyn : Dynamic.Host T ↪ H) (mark scale : Bus A H)
    (label current next result : List Bool) (advice : Stacks A) (work : Stacks H)
    (aux : Stacks T) (u v rank rows offCur offNext original mono marked power : ℕ)
    (hr : ∀ i, work (dyn i) = Dynamic.bank aux (Dynamic.regs (w := addr) u v rank rows offCur offNext original mono) i)
    (hm : state label current next result advice work mark = digits addr marked)
    (hs : state label current next result advice work scale = digits addr power) :
    ∀ f, state label current next result advice work (sources dyn mark scale f) =
      Sum.elim (fun _ : Unit ↦ digits addr offNext) (TargetRead.words addr mono power marked) f := by
  exact source_words_at dyn mark scale label current next result advice work offNext mono marked power
    (hr (.inl (.reg 5))) (hr (.inl (.reg 7))) hm hs

private noncomputable def plan (dst : Field ↪ H) (src : Field → Bus A H) : List (Bus A H × Bus A H) :=
  Finset.univ.toList.map fun f ↦ (src f, workPort (dst f))

/-- Clear the four template words and copy their replacements with one shared
scratch stack. The control is independent of the values and address width. -/
noncomputable def machine
    (host : RootInit.RootHost D (Num K) ↪ H) (target : Fin 3 ↪ K) (src : Field → Bus A H) (scratch : H) :
    FiniteRoutine (Bus A H) :=
  let ps := plan (destination host target) src
  (CallClear.cleanup (ps.map Prod.snd)).followedBy (CallCopies.copyPlan (workPort scratch) ps)

/-- Bound the steps to clear and copy all four argument words of the given width. -/
def clock (width : ℕ) : ℕ := (4*(width+1)+1) + (4*(5*width+2)+1)

private theorem valid (dst : Field ↪ H) (src : Field → Bus A H) (scratch : H)
    (apart : ∀ f g, src f ≠ workPort (dst g)) (hs : ∀ f, src f ≠ workPort scratch)
    (hd : ∀ f, dst f ≠ scratch) : CallCopies.Valid (workPort scratch) (plan dst src) := by
  simp only [CallCopies.Valid, plan, List.map_map, Function.comp_def]
  refine ⟨(Finset.nodup_toList _).map (workPort_injective.comp dst.injective), ?_, ?_, ?_⟩
  · rintro _ hk hdest
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hk
    obtain ⟨g, _, hg⟩ := List.mem_map.mp hdest
    exact apart f g hg.symm
  · rintro hk
    obtain ⟨f, _, hf⟩ := List.mem_map.mp hk
    exact hs f hf
  · rintro hk
    obtain ⟨f, _, hf⟩ := List.mem_map.mp hk
    exact hd f (workPort_injective hf)

variable [DecidableEq A] [DecidableEq H]

theorem machine_bounded (host : RootInit.RootHost D (Num K) ↪ H) (target : Fin 3 ↪ K)
    (src : Field → Bus A H) (scratch : H) (width cap : ℕ)
    (label current next result : List Bool) (advice : Stacks A) (work : Stacks H) (values : Stacks Field)
    (apart : ∀ f g, src f ≠ workPort (destination host target g))
    (hs : ∀ f, src f ≠ workPort scratch) (hd : ∀ f, destination host target f ≠ scratch)
    (empty : work scratch = [])
    (hvalues : ∀ f, state label current next result advice work (src f) = values f)
    (small : ∀ f, (values f).length ≤ width)
    (old : ∀ f, (work (destination host target f)).length ≤ width)
    (room : ∀ k, (state label current next result advice work k).length ≤ cap) :
    ∃ t ≤ clock width, (machine host target src scratch).BoundedRun (cap+clock width) t
      (state label current next result advice work)
      (state label current next result advice (installStacks (destination host target) work values)) := by
  let dst := destination host target
  let ps := plan dst src
  let start := state label current next result advice work
  let middle := CallClear.erased (ps.map Prod.snd) start
  let finish := state label current next result advice (installStacks dst work values)
  have ok := valid dst src scratch apart hs hd
  have plen : ps.length = 4 := by simp [ps, plan, Field]
  obtain ⟨a, ha, clear⟩ := CallClear.cleanup_runs (ps.map Prod.snd) start width (by
    simp only [ps, plan, List.map_map, Function.comp_def, List.mem_map]
    rintro _ ⟨f, _, rfl⟩; exact old f)
  have raw (f : Field) : middle (src f) = values f := by
    have mem : src f ∈ ps.map Prod.fst := by simp [ps, plan, List.map_map, Function.comp_def, List.mem_map]
    rw [show middle (src f) = start (src f) from ite_eq_right (ok.2.1 _ mem)]
    exact hvalues f
  have tmp : middle (workPort scratch) = [] := by
    rw [show middle (workPort scratch) = start (workPort scratch) from ite_eq_right ok.2.2.2]
    exact empty
  obtain ⟨b, hb, cp⟩ := CallCopies.copyPlan_runs (workPort scratch) ps middle width ok tmp (by
    intro pair hpair; exact ite_eq_left (List.mem_map.mpr ⟨pair, hpair, rfl⟩)) (by
    intro pair hpair; obtain ⟨f, _, rfl⟩ := List.mem_map.mp hpair; exact (raw f) ▸ small f)
  have hfinish : CallCopies.copied ps middle = finish := by
    funext k
    by_cases h : ∃ f, workPort (A := A) (dst f) = k
    · obtain ⟨f, rfl⟩ := h
      rw [CallCopies.copied_at _ _ ok.1 (show (src f, workPort (dst f)) ∈ ps from
        List.mem_map.mpr ⟨f, by simp, rfl⟩), raw]
      exact (installStacks_at dst.injective work values f).symm
    · have absent : k ∉ ps.map Prod.snd := by
        simp only [ps, plan, List.map_map, Function.comp_def, List.mem_map]
        rintro ⟨f, _, he⟩; exact h ⟨f, he⟩
      rw [CallCopies.copied_outside _ _ _ absent, show middle k = start k from ite_eq_right absent]
      cases k with
      | label | current | next | result => rfl
      | aux i =>
        cases i with
        | inl => rfl
        | inr j =>
          exact (installStacks_outside work values fun f hf ↦ h ⟨f, congrArg workPort hf⟩).symm
  rw [hfinish] at cp
  have htime : a+b ≤ clock width := by
    rw [List.length_map, plen] at ha
    rw [plen] at hb
    exact Nat.add_le_add ha hb
  exact ⟨a+b, htime, spaceRun_of_steps (clear.followedBy cp) fun k ↦ Nat.add_le_add (room k) htime⟩

/-- Install a smaller bank through a larger port embedding. This characterizes
the returned bank both on and off the four written stacks. -/
private theorem install_comp {X Y Z : Type} (x : X → Y) (y : Y → Z)
    (hx : Function.Injective x) (hy : Function.Injective y) (s : Stacks Z) (v : Stacks X) :
    installStacks (y ∘ x) s v = installStacks y s (installStacks x (s ∘ y) v) := by
  apply (installStacks_frame hy ?_ ?_).symm
  · intro k
    by_cases h : ∃ j, x j = k
    · obtain ⟨j, rfl⟩ := h
      exact (installStacks_at (hy.comp hx) s v j).trans (installStacks_at hx (s ∘ y) v j).symm
    · rw [installStacks_outside (ports := y ∘ x) s v (fun j he ↦ h ⟨j, hy he⟩),
        installStacks_outside (s ∘ y) v (not_exists.mp h)]
      rfl
  · intro k hout
    exact installStacks_outside s v fun j ↦ hout (x j)

/-- The four updates change precisely the replacement ordinal and the target
reader's own raw-bank slots, leaving the two submatrix index stacks empty. -/
theorem num_bank_after (target : Fin 3 ↪ K) (w : ℕ) (old new : List Bool)
    (raw : Stacks K) (words : Stacks (Fin 3)) :
    installStacks (numSlot target) (Replacement.workBank w old (Submatrix.workBank [] [] raw))
      (Sum.elim (fun _ : Unit ↦ new) words) =
      Replacement.workBank w new (Submatrix.workBank [] [] (installStacks target raw words)) := by
  apply installStacks_frame (numSlot target).injective
  · rintro (⟨⟩|i)
    · rfl
    · exact installStacks_at target.injective raw words i
  · rintro (p|p) hout
    · cases p with
      | reg j => fin_cases j <;> first | rfl | exact (hout (.inl ()) rfl).elim
      | _ => rfl
    · cases p with
      | row | col => rfl
      | aux k =>
        exact installStacks_outside raw words (fun i hi ↦
          hout (.inr i) (congrArg (fun j : K ↦ (Sum.inr (.aux j) : Num K)) hi))

omit [DecidableEq H] in
/-- If the template has already been loaded, the entire paired host now sees
the correct updated root banks. Static denominator inputs survive unchanged. -/
theorem host_after {p e : ℕ} (c : Vector p e) (r addr v : ℕ)
    (host : RootInit.RootHost D (Num K) ↪ H) (target : Fin 3 ↪ K)
    (den : Stacks D) (raw : Stacks K) (old new : List Bool) (words : Stacks (Fin 3))
    (work : Stacks H) (hhost : ∀ i, work (host i) = RootInit.template c r addr v den
      (Replacement.workBank addr old (Submatrix.workBank [] [] raw)) i) (i : RootInit.RootHost D (Num K)) :
    installStacks (destination host target) work (Sum.elim (fun _ : Unit ↦ new) words) (host i) =
      RootInit.template c r addr v den
        (Replacement.workBank addr new (Submatrix.workBank [] [] (installStacks target raw words))) i := by
  let num := Replacement.workBank addr old (Submatrix.workBank [] [] raw)
  let incoming : Stacks Field := Sum.elim (fun _ : Unit ↦ new) words
  let routes : D ⊕ Num K → H := host ∘ RootInit.readerPort
  have stored : work ∘ routes = Sum.elim den num := by
    funext j
    cases j <;> exact hhost (RootInit.readerPort _)
  have update : installStacks (Sum.inr ∘ numSlot target) (Sum.elim den num) incoming =
      Sum.elim den (Replacement.workBank addr new (Submatrix.workBank [] [] (installStacks target raw words))) := by
    rw [install_comp (numSlot target) Sum.inr (numSlot target).injective Sum.inr_injective]
    change installStacks Sum.inr (Sum.elim den num) (installStacks (numSlot target) num incoming) = _
    rw [num_bank_after]
    funext j
    rcases j with j|j
    · exact installStacks_outside _ _ fun _ he ↦ by cases he
    · exact installStacks_at Sum.inr_injective ..
  change installStacks (routes ∘ (Sum.inr ∘ numSlot target)) work incoming (host i) = _
  rw [install_comp (Sum.inr ∘ numSlot target) routes (Sum.inr_injective.comp (numSlot target).injective)
    (host.injective.comp RootInit.readerPort_injective), stored, update]
  exact RootInit.setReaders_mounted host work c r addr v den den num _ hhost i

/-- Readiness of the updated numerator and denominator after the exact word
copies. Only the raw reader's own ready predicate is needed here. -/
theorem root_ready {p e : ℕ} (c : Vector p e) (r addr v : ℕ) (hr : r < 2^addr)
    {denReady : Stacks D → Prop} {rawReady : Stacks K → Prop} (den : Stacks D) (hd : denReady den)
    (raw : Stacks K) (hw : rawReady raw) (replace : ℕ) :
    let num := Replacement.workBank addr (digits addr replace) (Submatrix.workBank [] [] raw)
    GramEngine.Ready addr v r r c denReady (GramEngine.initial addr v r r c den) ∧
    GramEngine.Ready addr v r r c (Replacement.Ready addr replace (Submatrix.Ready rawReady))
      (GramEngine.initial addr v r r c num) :=
  RootInit.template_ready c r addr v hr den _ hd ⟨_, ⟨raw, hw, rfl⟩, rfl⟩

/-- Mount the concrete three target words inside any containing raw workspace.
Every unmounted raw-reader port retains the old value. -/
theorem target_bank_after (mount : TargetRead.Work ↪ K) (w : ℕ)
    (d : PairCall.Inputs) (constants : Bool → List Bool) (source scale mark : ℕ) (raw : Stacks K)
    (hraw : raw ∘ mount = TargetRead.bank w d constants) :
    installStacks (mount ∘ TargetRead.slot) raw (TargetRead.words w source scale mark) =
      installStacks mount raw (TargetRead.bank w (TargetRead.setDynamic d source scale mark) constants) := by
  rw [install_comp TargetRead.slot mount TargetRead.slot.injective mount.injective, hraw,
    TargetRead.stage_dynamic]

end RankQuery.Stack.Coordinate.ArgumentStage

end VPVNP
end Computability
end OAI
