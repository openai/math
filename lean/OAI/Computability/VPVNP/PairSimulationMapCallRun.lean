import OAI.Computability.VPVNP.PairSimulationMapCallSetup

/-!
# A native motif call from its private descriptor

Initializing all operand registers and installing the pointer directory precede
the actual map evaluation on the same machine. The combined prefix counts every
initializer tick and retains the initial histogram on all rejecting paths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapCallSetup

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifEntry
open MapEntryTable MapPortAgreement MapResidentAgreement
open BurstRAM.PrivateRAM PrimedCounter.GuessWord CompressorRecords
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {r k p w t u : ℕ}

omit [DecidableEq J] in
private theorem prepend_post {P : MapEntry.Program B z j p r k} {M : Machine w p r k}
    {c m : Config w p r} {n hist cap : ℕ} {value : Option (List (Fin t))}
    {saved after : BurstRAM.Word w → Prop} {post : PrivateScratch.Memory w → Prop}
    (pre : Prefix M c (List.replicate n .tick) m) (per : m.persistent = c.persistent)
    (mem : ∀ l : Fin t, m.privateMem ((hist + l.val : ℕ) : BurstRAM.Word w) =
      c.privateMem ((hist + l.val : ℕ) : BurstRAM.Word w))
    (old : ∀ a, saved a → m.privateMem a = c.privateMem a) (sub : ∀ a, saved a → after a)
    (run : P.RunsPost M m hist cap after value post) :
    P.RunsPost M c hist (n + cap) saved value post := by
  obtain ⟨steps, out, bound, tail, hp, frame, result, exactMem⟩ := run.path
  refine ⟨n + steps, out, Nat.add_le_add_left bound _, ?_, hp.trans per,
    fun a ha ↦ (frame a (sub a ha)).trans (old a ha), ?_, exactMem⟩
  · rw [List.replicate_add]
    exact pre.append tail
  · cases value <;> simpa only [MapEntry.Program.Effect, mem] using result

variable (A : Allocation B z j r k) (args : Arg D E ≃ Fin (Fintype.card (Arg D E)))
  (slots : Register D E ≃ Fin (Fintype.card (Register D E))) (loc : A.Address → Fin p)
  {demand : D → ℕ} {v : E → ℕ} {d : DemandBits src dst demand j}
  {x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j}
  (X : MapEntry.Program.Workspace (A.program loc) demand v d x t w)

/-- All input cells and all exterior call state outside the pointer directory,
selector and label staging arrays, and histogram survive the full call. -/
def Outside (a : BurstRAM.Word w) : Prop :=
  (A.program loc).Outside X a ∧
    ∀ i : MapDirectoryInit.Row A, a ≠ X.directory + (i.val : BurstRAM.Word w)

/-- The operand initializer's private directory after all port pointers have been written. -/
noncomputable def directoryMemory (old : PrivateScratch.Memory w) : PrivateScratch.Memory w :=
  PrivateScratch.write X.directory (fun i : MapDirectoryInit.Row A ↦
    MapResidentAgreement.selectorStart v X.portBase ((ports G j A.edgeOrder).get i)) old

/-- Complete successful memory update, including the newly published pointer directory. -/
def Success (sel : Selector B ↪ BurstRAM.Word w) (ord : (parameterData B).Entry → Fin t)
    (old new : PrivateScratch.Memory w) : Prop :=
  (A.program loc).Success X sel ord (directoryMemory A loc X old) new

/-- Once the operands give a successful row sequence, each output memory cell depends
on the initial memory only at that same cell. -/
theorem Success.eq_at {sel : Selector B ↪ BurstRAM.Word w} {ord : (parameterData B).Entry → Fin t}
    {old old' new new' : PrivateScratch.Memory w}
    (h : Success A loc X sel ord old new) (h' : Success A loc X sel ord old' new')
    (θ : Fin u → Selector B) (tags : (selectorRun G (selectorTable B) (selectorCode B) v j x).1 =
      some θ) (valid : ∀ e, v e = totalWidth (basePayload B) θ e)
    (a : BurstRAM.Word w) (ha : old a = old' a) : new a = new' a := by
  rw [h θ tags valid, h' θ tags valid]
  exact (A.program loc).successMemory_congr_at X sel ord θ a
    (PrivateScratch.write_congr_at _ _ a ha)

/-- Fixed setup geometry and the native body can all occupy arbitrary addresses of
the enclosing vertex machine. Only the prescribed instruction text is required. -/
theorem run_post (M : Machine w p r k)
    (core : ∀ a, A.installed a = true → M.code (loc a) = (A.text loc a).resize w)
    (ptr : Fin r) (scratch : Fin 2 ↪ Fin r) (apart : ∀ a i, A.reg a ≠ scratch i)
    (dirPC : MapDirectoryInit.Address A → Fin p)
    (dirLink : ∀ a, M.code (dirPC a) =
      (MapDirectoryInit.text A scratch dirPC ((A.selector loc).scan 0) a).resize w)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t)
    (pub : ∀ a, M.publicData (A.pub a) = Allocation.words fb fd fs sel
      (fun e ↦ ((ord e).val : BurstRAM.Word w)) a)
    (histApart : ∀ (l : Fin t) (i : MapDirectoryInit.Row A),
      ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)) :
    let f := recipes A args (MapDirectoryInit.portField (anchorPort G j)) slots
    ∀ (vm : Fin (RegisterSetup.regCount f) ↪ Fin r)
      (_place : ∀ a, vm (RegisterSetup.output f (slots a)) = A.reg a)
      (_safe : ∀ i, vm i ≠ ptr) (pc : ℕ → Fin p)
      (_hl : MapInitCompiler.Linked vm ptr M pc (RegisterSetup.lines f))
      (_endPC : pc (RegisterSetup.lines f).length = dirPC (.inl ()))
      (c : Config w p r), c.pc = pc 0 → Input A args loc X ptr c →
      (A.program loc).RunsPost M c X.hist ((RegisterSetup.lines f).length +
        (1 + 3 * (ports G j A.edgeOrder).length) + MapNativeClock.cap B z j u) (Outside A loc X)
        ((MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
          (selectorTable B) (selectorCode B) v j d x).1.map (List.map ord))
        (Success A loc X sel ord c.privateMem) := by
  intro f vm place safe pc hl endPC c hc input
  obtain ⟨m, pre, ready, hp, hm⟩ := native A args loc X slots M ptr scratch apart dirPC dirLink
    vm place safe pc hl endPC c hc input
  have result := (A.program loc).native_post X M (A.linked loc M core) (A.separate loc)
    sel ord fb fd fs
    (A.public_spec loc fb fd fs sel _ M pub) m ready
  have hdir : m.privateMem = directoryMemory A loc X c.privateMem :=
    PrivateScratch.eq_write _ _ ready.selector.resident.pointers hm
  apply prepend_post pre hp (fun l ↦ hm _ (histApart l)) (fun a ha ↦ hm a ha.2)
    (fun _ ha ↦ ha.1)
  change (A.program loc).RunsPost M m X.hist _ _ _
    ((A.program loc).Success X sel ord (directoryMemory A loc X c.privateMem))
  rw [← hdir]
  exact result

/-- Keep the map result and the exterior memory frame. -/
theorem run_framed (M : Machine w p r k)
    (core : ∀ a, A.installed a = true → M.code (loc a) = (A.text loc a).resize w)
    (ptr : Fin r) (scratch : Fin 2 ↪ Fin r) (apart : ∀ a i, A.reg a ≠ scratch i)
    (dirPC : MapDirectoryInit.Address A → Fin p)
    (dirLink : ∀ a, M.code (dirPC a) =
      (MapDirectoryInit.text A scratch dirPC ((A.selector loc).scan 0) a).resize w)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t)
    (pub : ∀ a, M.publicData (A.pub a) = Allocation.words fb fd fs sel
      (fun e ↦ ((ord e).val : BurstRAM.Word w)) a)
    (histApart : ∀ (l : Fin t) (i : MapDirectoryInit.Row A),
      ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)) :
    let f := recipes A args (MapDirectoryInit.portField (anchorPort G j)) slots
    ∀ (vm : Fin (RegisterSetup.regCount f) ↪ Fin r)
      (_place : ∀ a, vm (RegisterSetup.output f (slots a)) = A.reg a)
      (_safe : ∀ i, vm i ≠ ptr) (pc : ℕ → Fin p)
      (_hl : MapInitCompiler.Linked vm ptr M pc (RegisterSetup.lines f))
      (_endPC : pc (RegisterSetup.lines f).length = dirPC (.inl ()))
      (c : Config w p r), c.pc = pc 0 → Input A args loc X ptr c →
      (A.program loc).RunsFramed M c X.hist ((RegisterSetup.lines f).length +
        (1 + 3 * (ports G j A.edgeOrder).length) + MapNativeClock.cap B z j u) (Outside A loc X)
        ((MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
          (selectorTable B) (selectorCode B) v j d x).1.map (List.map ord)) := by
  intro f vm place safe pc hl endPC c hc input
  exact (run_post A args slots loc X M core ptr scratch apart dirPC dirLink fb fd fs
    sel ord pub histApart vm place safe pc hl endPC c hc input).framed _

/-- The full initializer and map prefix, projected to its histogram result. -/
theorem run (M : Machine w p r k)
    (core : ∀ a, A.installed a = true → M.code (loc a) = (A.text loc a).resize w)
    (ptr : Fin r) (scratch : Fin 2 ↪ Fin r) (apart : ∀ a i, A.reg a ≠ scratch i)
    (dirPC : MapDirectoryInit.Address A → Fin p)
    (dirLink : ∀ a, M.code (dirPC a) =
      (MapDirectoryInit.text A scratch dirPC ((A.selector loc).scan 0) a).resize w)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t)
    (pub : ∀ a, M.publicData (A.pub a) = Allocation.words fb fd fs sel
      (fun e ↦ ((ord e).val : BurstRAM.Word w)) a)
    (histApart : ∀ (l : Fin t) (i : MapDirectoryInit.Row A),
      ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)) :
    let f := recipes A args (MapDirectoryInit.portField (anchorPort G j)) slots
    ∀ (vm : Fin (RegisterSetup.regCount f) ↪ Fin r)
      (_place : ∀ a, vm (RegisterSetup.output f (slots a)) = A.reg a)
      (_safe : ∀ i, vm i ≠ ptr) (pc : ℕ → Fin p)
      (_hl : MapInitCompiler.Linked vm ptr M pc (RegisterSetup.lines f))
      (_endPC : pc (RegisterSetup.lines f).length = dirPC (.inl ()))
      (c : Config w p r), c.pc = pc 0 → Input A args loc X ptr c →
      (A.program loc).Runs M c X.hist ((RegisterSetup.lines f).length +
        (1 + 3 * (ports G j A.edgeOrder).length) + MapNativeClock.cap B z j u)
        ((MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
          (selectorTable B) (selectorCode B) v j d x).1.map (List.map ord)) := by
  intro f vm place safe pc hl endPC c hc input
  exact (run_framed A args slots loc X M core ptr scratch apart dirPC dirLink fb fd fs
    sel ord pub histApart vm place safe pc hl endPC c hc input).forget _

end PairSimulation.MapCallSetup

end VPVNP
end Computability
end OAI
