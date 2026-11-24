import OAI.Computability.VPVNP.RankCoordinateCramer
import OAI.Computability.VPVNP.RankCoordinateReader
import OAI.Computability.VPVNP.RankQueryPlainRoot
import OAI.Computability.VPVNP.RankQueryStackGramInitialization
import OAI.Computability.VPVNP.SliceArithmeticCallCopies

/-! # Loading the two determinant roots from reusable advice

The static root registers and field parameters can be stored once in advice.
A fixed scan copies these stacks into fresh work ports before a pair of Schur
queries. The private matrix-reader ports are the only parts of the root banks
which depend on the live entry query.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.RootInit

open RAMTape UniversalCountStack SliceArithmetic

variable {T A H : Type} [Fintype T]

private def src (source : T → A) (i : T) : Reader.Port (A ⊕ H) := .aux (.inl (source i))
private def dst (destination : T ↪ H) (i : T) : Reader.Port (A ⊕ H) := .aux (.inr (destination i))

private noncomputable def plan (source : T → A) (destination : T ↪ H) :
    List (Reader.Port (A ⊕ H) × Reader.Port (A ⊕ H)) :=
  Finset.univ.toList.map (fun i => (src source i, dst destination i))

/-- Copy each advised template stack to its corresponding root port. -/
noncomputable def load (source : T → A) (destination : T ↪ H) (tmp : H) :=
  CallCopies.copyPlan (.aux (.inr tmp)) (plan source destination)

private theorem plan_valid (source : T → A) (destination : T ↪ H) (tmp : H)
    (fresh : ∀ i, destination i ≠ tmp) :
    CallCopies.Valid (.aux (.inr tmp)) (plan source destination) := by
  simp only [CallCopies.Valid, plan, List.map_map, Function.comp_def]
  refine ⟨(Finset.nodup_toList _).map (fun i j eq => destination.injective (Sum.inr.inj (Reader.Port.aux.inj eq))),
    ?_, ?_, ?_⟩
  · intro k hk hl
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
    obtain ⟨j, _, h⟩ := List.mem_map.mp hl
    cases h
  · intro hk
    obtain ⟨i, _, h⟩ := List.mem_map.mp hk
    cases h
  · intro hk
    obtain ⟨i, _, h⟩ := List.mem_map.mp hk
    exact fresh i (Sum.inr.inj (Reader.Port.aux.inj h))

/-- Bound the finite scan that copies all root stacks from advice, using the number of ports
and maximum saved stack height. -/
def loadClock (T : Type) [Fintype T] (M : ℕ) := Fintype.card T * (5*M+2)+1

/-- Runtime copying retains both the reusable sources and every stack outside
the chosen destinations. The space cap uses the initial height of all ports. -/
theorem load_runs [DecidableEq A] [DecidableEq H]
    (source : T → A) (destination : T ↪ H) (tmp : H) (fresh : ∀ i, destination i ≠ tmp)
    (label current next result : List Bool) (advice : Stacks A) (work : Stacks H) (template : Stacks T)
    (hsource : ∀ i, advice (source i) = template i) (blank : ∀ i, work (destination i) = [])
    (scratch : work tmp = []) (M ambient : ℕ) (fits : ∀ i, (template i).length ≤ M)
    (bankFits : ∀ i, ((Reader.bank label current next result (Sum.elim advice work)) i).length ≤ ambient) :
    ∃ t ≤ loadClock T M, (load source destination tmp).BoundedRun (ambient + loadClock T M) t
      (Reader.bank label current next result (Sum.elim advice work))
      (Reader.bank label current next result (Sum.elim advice (installStacks destination work template))) := by
  let before := Reader.bank label current next result (Sum.elim advice work)
  let after := Reader.bank label current next result (Sum.elim advice (installStacks destination work template))
  let pairs := plan source destination
  have valid := plan_valid source destination tmp fresh
  obtain ⟨t, ht, run⟩ := CallCopies.copyPlan_runs (Reader.Port.aux (Sum.inr tmp : A ⊕ H)) pairs before M valid scratch (by
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact blank i) (by
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    change (advice (source i)).length ≤ M
    simpa only [hsource] using fits i)
  have bound : t ≤ loadClock T M := by simpa only [pairs, plan, List.length_map,
    Finset.length_toList, Finset.card_univ, loadClock] using ht
  have out : CallCopies.copied pairs before = after := by
    funext k
    by_cases hk : ∃ i : T, dst destination i = k
    · obtain ⟨i, rfl⟩ := hk
      have mem : (src source i, dst destination i) ∈ pairs := List.mem_map.mpr ⟨i, by simp, rfl⟩
      rw [CallCopies.copied_at _ _ valid.1 mem]
      change advice (source i) = installStacks destination work template (destination i)
      rw [hsource, installStacks_at destination.injective]
    · have absent : k ∉ pairs.map Prod.snd := by
        simp only [pairs, plan, List.map_map, Function.comp_def, List.mem_map]
        rintro ⟨i, _, hi⟩
        exact hk ⟨i, hi⟩
      rw [CallCopies.copied_outside _ _ _ absent]
      cases k with
      | label | current | next | result => rfl
      | aux a =>
        rcases a with a | j
        · rfl
        · change work j = installStacks destination work template j
          apply (installStacks_outside work template _).symm
          intro i he
          exact hk ⟨i, congrArg (fun k : H => (Reader.Port.aux (.inr k) : Reader.Port (A ⊕ H))) he⟩
  rw [out] at run
  exact ⟨t, bound, spaceRun_of_steps run (fun k => Nat.add_le_add (bankFits k) bound)⟩

/-- Full work-port type of the two streamed determinants, with the matrix reader's
private ports parameterized independently for numerator and denominator. -/
abbrev RootHost (K L : Type) := Cramer.SchurPair.Host (GramEngine.Aux K) (GramEngine.Aux L)

variable {K L : Type} {p e : ℕ}

/-- Both engines start at the top coefficient of the degree-`r` pencil. Their
continuation stacks and result ports are empty. -/
def template (c : Vector p e) (r addr width : ℕ) (denReader : Stacks K) (numReader : Stacks L) :
    Stacks (RootHost K L) :=
  Cramer.SchurPair.host
    (Cramer.SchurPair.entryBank c r addr width (GramEngine.initial addr width r r c denReader))
    (Cramer.SchurPair.entryBank c r addr width (GramEngine.initial addr width r r c numReader))
    (Cramer.frame p e width (Cramer.digits width c) [] [] [])

/-- The two root auxiliary banks meet the concrete determinant readers' readiness
conditions, including the binary matrix dimensions and packed field advice. -/
theorem template_ready (c : Vector p e) (r addr width : ℕ) (hr : r < 2^addr)
    (denReader : Stacks K) (numReader : Stacks L) {denReady : Stacks K → Prop} {numReady : Stacks L → Prop}
    (hd : denReady denReader) (hn : numReady numReader) :
    GramEngine.Ready addr width r r c denReady (GramEngine.initial addr width r r c denReader) ∧
    GramEngine.Ready addr width r r c numReady (GramEngine.initial addr width r r c numReader) :=
  ⟨GramEngine.initial_ready denReader hd hr hr, GramEngine.initial_ready numReader hn hr hr⟩

/-- Location of a dynamic scalar-reader input within the paired root banks. -/
def readerPort : K ⊕ L → RootHost K L
  | .inl k => .inl (.aux (.inl (.inr (.aux k))))
  | .inr l => .inr (.inl (.aux (.inl (.inr (.aux l)))))

theorem readerPort_injective : Function.Injective (readerPort (K := K) (L := L)) := by
  rintro (k|k) (l|l) h <;> simp_all [readerPort]

/-- Filling the private reader inputs after loading the constant advice has
exactly the same effect as placing those inputs in the corresponding root banks. -/
theorem setReaders (c : Vector p e) (r addr width : ℕ) (oldD newD : Stacks K) (oldN newN : Stacks L) :
    installStacks readerPort (template c r addr width oldD oldN) (Sum.elim newD newN) =
      template c r addr width newD newN := by
  apply installStacks_frame readerPort_injective
  · rintro (i|i) <;> rfl
  · rintro (i | i | i) outside
    · cases i with
      | aux j =>
        rcases j with (j|j)|j
        · rfl
        · cases j <;> first | rfl | exact (outside (.inl _) rfl).elim
        · cases j <;> rfl
      | frame f => cases f <;> rfl
      | condition | result => rfl
    · cases i with
      | aux j =>
        rcases j with (j|j)|j
        · rfl
        · cases j <;> first | rfl | exact (outside (.inr _) rfl).elim
        · cases j <;> rfl
      | frame f => cases f <;> rfl
      | condition | result => rfl
    · rfl

/-- The reader update can be made after the roots are mounted in a larger
workspace. Every engine port then sees its precise initialized value. -/
theorem setReaders_mounted (host : RootHost K L ↪ H) (work : Stacks H) (c : Vector p e)
    (r addr width : ℕ) (oldD newD : Stacks K) (oldN newN : Stacks L)
    (hhost : ∀ i, work (host i) = template c r addr width oldD oldN i) (i : RootHost K L) :
    installStacks (host ∘ readerPort) work (Sum.elim newD newN) (host i) =
      template c r addr width newD newN i := by
  rw [← setReaders c r addr width oldD newD oldN newN]
  by_cases hin : ∃ j, readerPort j = i
  · obtain ⟨j, rfl⟩ := hin
    rw [installStacks_at readerPort_injective]
    exact installStacks_at (host.injective.comp readerPort_injective) work (Sum.elim newD newN) j
  · rw [installStacks_outside (ports := host ∘ readerPort) _ _ (fun j h => hin ⟨j, host.injective h⟩),
      installStacks_outside _ _ (not_exists.mp hin)]
    exact hhost i

/-- A uniform height bound for the fixed root template plus a scalar reader
whose own input stacks each have length at most `a`. -/
def templateCap (addr width e a : ℕ) :=
  max (max (addr+width+e+e*width+a) (max 1 (max addr (e*width)))) ((e+1)*(width+1))

variable [Fact p.Prime]

theorem template_length (c : Vector p e) (r addr width a : ℕ) (hr : r < 2^addr)
    (hw : Word.workingWidth p ≤ width) (denReader : Stacks K) (numReader : Stacks L)
    (hd : ∀ i, (denReader i).length ≤ a) (hn : ∀ j, (numReader j).length ≤ a) (i : RootHost K L) :
    ((template c r addr width denReader numReader) i).length ≤ templateCap addr width e a := by
  have rootBound {J : Type} (localBank : Stacks J) (hj : ∀ j, (localBank j).length ≤ a)
      (k : Engine.Port (GramEngine.Aux J)) :
      (Cramer.SchurPair.entryBank c r addr width (GramEngine.initial addr width r r c localBank) k).length
        ≤ templateCap addr width e a := by
    let ready (s : Stacks J) := ∀ j, (s j).length ≤ a
    have hready := GramEngine.initial_ready (readerReady := ready) (c := c) (v := width) localBank hj hr hr
    have small := GramEngine.ready_length hready (fun _ hs => hs)
    have h := Engine.state_length (d := 0) (c := c) (w := addr) (v := width)
      (.enter (SchurKey.root (n := r) (Fin.last r) (Fin.last 0)), []) (by simp) _ small k
    apply (le_trans h ?_)
    simp only [Nat.zero_mul, Nat.max_zero]
    exact le_max_left ..
  rcases i with i | i | i
  · exact rootBound denReader hd i
  · exact rootBound numReader hn i
  · have h := Cramer.frame_length hw c c c i
    apply (le_trans ?_ h).trans (le_max_right ..)
    rcases i with ((i|i)|i)|i
    · exact le_rfl
    · cases i <;> exact le_rfl
    · cases i <;> first | exact le_rfl | exact Nat.zero_le _
    · cases i <;> first | exact le_rfl | exact Nat.zero_le _

/-- Each advised word is counted once, even when different ports receive equal data. -/
theorem template_total_length [Fintype (RootHost K L)] (c : Vector p e) (r addr width a : ℕ)
    (hr : r < 2^addr) (hw : Word.workingWidth p ≤ width) (denReader : Stacks K) (numReader : Stacks L)
    (hd : ∀ i, (denReader i).length ≤ a) (hn : ∀ j, (numReader j).length ≤ a) :
    ∑ i, ((template c r addr width denReader numReader) i).length ≤
      Fintype.card (RootHost K L) * templateCap addr width e a := by
  calc
    _ ≤ ∑ _ : RootHost K L, templateCap addr width e a :=
      Finset.sum_le_sum fun i _ => template_length c r addr width a hr hw denReader numReader hd hn i
    _ = _ := by simp

/-- Initialize the actual paired Schur workspaces in an empty scratch bank. Both
roots are installed at the top pencil query, and the copy's temporary port is
empty on return. The loaded template can be patched at `readerPort` with the
current entry request before the two determinant calls. -/
theorem loadRoot_runs [Fintype (RootHost K L)] [DecidableEq A] [DecidableEq H]
    (source : RootHost K L → A) (host : RootHost K L ↪ H) (scratch : H) (fresh : ∀ i, host i ≠ scratch)
    (c : Vector p e) (r addr width readerBound ambient : ℕ) (hr : r < 2^addr)
    (hw : Word.workingWidth p ≤ width) (denReader : Stacks K) (numReader : Stacks L)
    (hd : ∀ i, (denReader i).length ≤ readerBound) (hn : ∀ j, (numReader j).length ≤ readerBound)
    (label current next : List Bool) (advice : Stacks A)
    (hsource : ∀ i, advice (source i) = template c r addr width denReader numReader i)
    (bankFits : ∀ i, (Reader.bank label current next [] (Sum.elim advice (fun _ : H => [])) i).length ≤ ambient) :
    let cap := templateCap addr width e readerBound
    ∃ t ≤ loadClock (RootHost K L) cap, ∃ work : Stacks H, work scratch = [] ∧
      (∀ i, work (host i) = template c r addr width denReader numReader i) ∧
      (load source host scratch).BoundedRun (ambient + loadClock (RootHost K L) cap) t
        (Reader.bank label current next [] (Sum.elim advice (fun _ => [])))
        (Reader.bank label current next [] (Sum.elim advice work)) := by
  let tplt := template c r addr width denReader numReader
  let cap := templateCap addr width e readerBound
  let work := installStacks host (fun _ : H => []) tplt
  obtain ⟨t, ht, run⟩ := load_runs source host scratch fresh label current next [] advice (fun _ => [])
    tplt hsource (fun _ => rfl) rfl cap ambient (template_length c r addr width readerBound hr hw
      denReader numReader hd hn) bankFits
  exact ⟨t, ht, work, installStacks_outside _ _ fresh, installStacks_at host.injective _ _, run⟩

end RankQuery.Stack.Coordinate.RootInit

end VPVNP
end Computability
end OAI
