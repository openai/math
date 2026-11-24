import OAI.Computability.VPVNP.PairNodeChildLoop

/-!
# Composing the native stages of a shrinking vertex

The old-half-wire reader passes its exact stream suffix and private memory
to the hidden-field reader. The deterministic resident maps start with the
resulting private fields. The same entry scratch determines the path and
the entire returned scratch for every compatible native configuration.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM DFS NodeArguments.ChildScan
open scoped Fin.CommRing

variable {w endAddr p r k : ℕ} {α β : Type*}

/-- The data, native trace, and full scratch result of one local stage. -/
structure Outcome (w endAddr : ℕ) (α : Type*) where
  /-- Typed value produced by this visit stage, such as its decoded child arguments or chosen
  hidden fields. -/
  value : α
  /-- Chronological native events emitted while producing the stage's value. -/
  trace : List (Event w)
  /-- Private scratch image retained by the next stage after this reader finishes. -/
  updated : Scratch w endAddr

/-- A partial visit-stage decoder for a node and scratch image. Success returns the typed
outcome and the unconsumed suffix of the choice tape. -/
abbrev Reader (w endAddr : ℕ) (α : Type*) :=
  Word w → Scratch w endAddr → List Bool → Option (Outcome w endAddr α × List Bool)

/-- The four DFS registers and every private stack address protected across
the stage, together with its persistent word. -/
structure Frame (dfs : Fin 9 ↪ Fin r) (endAddr : ℕ) (c d : Config w p r) : Prop where
  registers : ∀ i, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → d.reg (dfs i) = c.reg (dfs i)
  below : ∀ a : Word w, a.val < endAddr → d.privateMem a = c.privateMem a
  persistent : d.persistent = c.persistent

theorem Frame.trans {dfs : Fin 9 ↪ Fin r} {c d e : Config w p r}
    (h : Frame dfs endAddr c d) (h' : Frame dfs endAddr d e) : Frame dfs endAddr c e :=
  ⟨fun i hi => (h'.registers i hi).trans (h.registers i hi),
    fun a ha => (h'.below a ha).trans (h.below a ha), h'.persistent.trans h.persistent⟩

theorem Frame.keepsPending {dfs : Fin 9 ↪ Fin r} {c d : Config w p r}
    (h : Frame dfs endAddr c d) {top : ℕ} {pending : List (Word w)}
    (atEnd : top + pending.length = endAddr) (st : Represents c.privateMem top pending) :
    Represents d.privateMem top pending := by
  refine ⟨st.1, fun i => (h.below _ ?_).trans (st.2 i)⟩
  change (top + i.val) % (2 ^ w) < endAddr
  exact (Nat.mod_le ..).trans_lt (atEnd ▸ Nat.add_lt_add_left i.isLt top)

/-- Each accepted result runs from every native input satisfying the entry
predicate, and a failed read precludes returning for every fuel. -/
structure Realizes (read : Reader w endAddr α) (M : Machine w p r k) (m : Memory w)
    (dfs : Fin 9 ↪ Fin r) (pre : Word w → Config w p r → Prop)
    (post : α → Word w → Config w p r → Prop) : Prop where
  success : ∀ node c bs out rest, pre node c →
    read node (scratch endAddr c.privateMem) bs = some (out, rest) →
      bs = choiceBits out.trace ++ rest ∧ ∃ d, post out.value node d ∧ Frame dfs endAddr c d ∧
        scratch endAddr d.privateMem = out.updated ∧ Prefix M m c d (choiceBits out.trace) out.trace
  reject : ∀ node c bs, pre node c →
    read node (scratch endAddr c.privateMem) bs = none → ¬ Returns M c m bs

/-- Pass the first stage's parsed values, scratch, and suffix to the next. -/
def bind (first : Reader w endAddr α) (next : α → Reader w endAddr β) :
    Reader w endAddr β := fun node saved bs =>
  match first node saved bs with
  | none => none
  | some (a, tail) => (next a.value node a.updated tail).map fun (b, rest) =>
      (⟨b.value, a.trace ++ b.trace, b.updated⟩, rest)

/-- Successful parses split the supplied tape at the native choice events. -/
def Splits (read : Reader w endAddr α) : Prop :=
  ∀ node saved bs out rest, read node saved bs = some (out, rest) →
    bs = choiceBits out.trace ++ rest

theorem Splits.bind {first : Reader w endAddr α} {next : α → Reader w endAddr β}
    (h : Splits first) (h' : ∀ a, Splits (next a)) : Splits (ShrinkRole.bind first next) := by
  intro node saved bs out rest read
  cases hx : first node saved bs with
  | none => simp [ShrinkRole.bind, hx] at read
  | some pair =>
    obtain ⟨x, tail⟩ := pair
    cases hy : next x.value node x.updated tail with
    | none => simp [ShrinkRole.bind, hx, hy] at read
    | some pair =>
      obtain ⟨y, leftover⟩ := pair
      obtain ⟨rfl,rfl⟩ : (⟨y.value, x.trace ++ y.trace, y.updated⟩ : Outcome w endAddr β) = out ∧
          leftover = rest := by simpa [ShrinkRole.bind, hx, hy] using read
      rw [PrimedInputRAM.Flow.choiceBits_append, h _ _ _ _ _ hx, (h' x.value) _ _ _ _ _ hy,
        List.append_assoc]

variable {M : Machine w p r k} {m : Memory w} {dfs : Fin 9 ↪ Fin r}
  {pre : Word w → Config w p r → Prop} {mid : α → Word w → Config w p r → Prop}
  {post : β → Word w → Config w p r → Prop}

/-- A later consumer may discard unused facts established at the exit. -/
theorem Realizes.weakenPost {read : Reader w endAddr α}
    {done done' : α → Word w → Config w p r → Prop}
    (h : Realizes read M m dfs pre done)
    (weaken : ∀ a node d, done a node d → done' a node d) :
    Realizes read M m dfs pre done' := by
  refine ⟨?_, h.reject⟩
  intro node c bs out rest hc got
  obtain ⟨part,d,hd,fr,updated,path⟩ := h.success node c bs out rest hc got
  exact ⟨part, d, weaken _ _ _ hd, fr, updated, path⟩

/-- A rejection in a later stage follows back through the successful prefixes
of the earlier stages. This covers truncation within any consumed field. -/
theorem Realizes.bind {first : Reader w endAddr α} {next : α → Reader w endAddr β}
    (h : Realizes first M m dfs pre mid) (h' : ∀ a, Realizes (next a) M m dfs (mid a) post) :
    Realizes (bind first next) M m dfs pre post := by
  constructor
  · intro node c bs out rest hc hr
    cases ha : first node (scratch endAddr c.privateMem) bs with
    | none => simp [ShrinkRole.bind, ha] at hr
    | some z =>
      obtain ⟨a,tail⟩ := z
      obtain ⟨part,d,hd,fr,sd,one⟩ := h.success _ _ _ _ _ hc ha
      cases hb : next a.value node a.updated tail with
      | none => simp [ShrinkRole.bind, ha, hb] at hr
      | some z =>
        obtain ⟨b,left⟩ := z
        simp only [ShrinkRole.bind, ha, hb, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl,rfl⟩ := hr
        obtain ⟨part',e,he,fr',se,two⟩ :=
          (h' a.value).success node d tail b left hd (sd ▸ hb)
        rw [PrimedInputRAM.Flow.choiceBits_append]
        exact ⟨by rw [part, part', List.append_assoc], e, he, fr.trans fr', se, one.trans two⟩
  · intro node c bs hc hr
    cases ha : first node (scratch endAddr c.privateMem) bs with
    | none => exact h.reject node c bs hc ha
    | some z =>
      obtain ⟨a,tail⟩ := z
      obtain ⟨part,d,hd,_,sd,one⟩ := h.success _ _ _ _ _ hc ha
      cases hb : next a.value node a.updated tail with
      | none =>
        rw [part]
        exact mt (one.returns tail).mp ((h' a.value).reject node d tail hd (sd ▸ hb))
      | some z => rcases z with ⟨b,left⟩; simp [ShrinkRole.bind, ha, hb] at hr

/-- A deterministic register-setup stage described on the caller's scratch. -/
structure Setup (w endAddr : ℕ) where
  /-- Events of the deterministic setup at the given popped node and incoming scratch image. -/
  trace : Word w → Scratch w endAddr → List (Event w)
  /-- Scratch image left by the deterministic setup for the subsequent visit stage. -/
  updated : Word w → Scratch w endAddr → Scratch w endAddr
  quiet : ∀ node saved, choiceBits (trace node saved) = []

/-- Expose deterministic setup as a unit-valued reader that emits its trace, updates scratch,
and retains the entire choice tape. -/
def Setup.reader (s : Setup w endAddr) : Reader w endAddr Unit := fun node saved bs =>
  some (⟨(), s.trace node saved, s.updated node saved⟩, bs)

/-- A register-only setup has a fixed number of local ticks and keeps all scratch. -/
def Setup.ticks (n : ℕ) : Setup w endAddr where
  trace _ _ := List.replicate n .tick
  updated _ s := s
  quiet _ _ := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [List.replicate_succ, choiceBits] using ih

/-- Consecutive setup fragments expose one trace and the last scratch update. -/
def Setup.seq (a b : Setup w endAddr) : Setup w endAddr where
  trace n s := a.trace n s ++ b.trace n (a.updated n s)
  updated n s := b.updated n (a.updated n s)
  quiet n s := by
    simp only [PrimedInputRAM.Flow.choiceBits_append, a.quiet, b.quiet, List.nil_append]

theorem Setup.seq_realizes {a b : Setup w endAddr}
    {pre mid post : Word w → Config w p r → Prop}
    (ha : Realizes a.reader M m dfs pre (fun _ => mid))
    (hb : Realizes b.reader M m dfs mid (fun _ => post)) :
    Realizes (a.seq b).reader M m dfs pre (fun _ => post) :=
  ha.bind fun _ => hb

theorem Setup.splits (s : Setup w endAddr) : Splits s.reader := by
  intro node saved bs out rest h
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
  simp only [s.quiet, List.nil_append]

/-- A linked setup may read the real directory or write the private operands.
Its specified trace and writes must hold on every eligible input configuration. -/
theorem Setup.realizes {M : Machine w p r k} {m : Memory w} {dfs : Fin 9 ↪ Fin r}
    (s : Setup w endAddr) {pre post : Word w → Config w p r → Prop}
    (run : ∀ node c, pre node c →
      ∃ d, post node d ∧ Frame dfs endAddr c d ∧
        scratch endAddr d.privateMem = s.updated node (scratch endAddr c.privateMem) ∧
        Prefix M m c d [] (s.trace node (scratch endAddr c.privateMem))) :
    Realizes s.reader M m dfs pre (fun _ => post) := by
  constructor
  · intro node c bs out rest hc h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simpa only [s.quiet, List.nil_append, true_and] using run node c hc
  · intro node c bs hc h
    cases h

/-- Convert the composed local reader into one DFS visit with its full
scratch snapshot as the input condition. -/
def hook (read : Reader w endAddr α) : HookParser w endAddr where
  read node saved bs := (read node saved bs).map fun (out, rest) =>
    (⟨node, out.trace, (· = saved), fun _ => out.updated⟩, rest)

/-- Native state at a DFS visit after the node was popped. -/
structure Entry (dfs : Fin 9 ↪ Fin r) (endAddr : ℕ) (visit : Fin p) (node : Word w)
    (c : Config w p r) (top : ℕ) (pending : List (Word w)) : Prop where
  pc : c.pc = visit
  nodeWord : c.reg (dfs 7) = node
  stack : Represents c.privateMem top pending
  atEnd : top + pending.length = endAddr
  topWord : c.reg (dfs 5) = (top : Word w)
  endWord : c.reg (dfs 6) = (endAddr : Word w)
  one : c.reg (dfs 3) = 1

/-- Any compatible entry configuration produces the same parsed trace and
scratch result. The bit identity must also hold for a successful read whose
input scratch currently has no compatible DFS stack. -/
theorem Realizes.exactOn {visit ret : Fin p} {read : Reader w endAddr α}
    (h : Realizes read M m dfs pre (fun _ _ d => d.pc = ret))
    {domain : Word w → Scratch w endAddr → Prop}
    (splitBits : ∀ node saved bs out rest, domain node saved →
      read node saved bs = some (out, rest) → bs = choiceBits out.trace ++ rest)
    (start : ∀ node c top pending, domain node (scratch endAddr c.privateMem) →
      Entry dfs endAddr visit node c top pending → pre node c) :
    (hook read).ExactOn domain M visit ret dfs m := by
  constructor
  · intro node saved dom bs job tail hr
    obtain ⟨⟨out, rest⟩, got, eqn⟩ := Option.map_eq_some_iff.mp hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eqn
    refine ⟨rfl, rfl, splitBits _ _ _ _ _ dom got, ?_⟩
    intro c top pending enabled pc nodeWord stack atEnd topWord endWord one
    change scratch endAddr c.privateMem = saved at enabled
    have hc := start node c top pending (enabled ▸ dom)
      ⟨pc, nodeWord, stack, atEnd, topWord, endWord, one⟩
    obtain ⟨_,d,done,fr,updated,path⟩ := h.success node c bs out rest hc (enabled ▸ got)
    exact ⟨d, done, (fr.registers 7 (by simp)).trans nodeWord,
      (fr.registers 5 (by simp)).trans topWord, (fr.registers 6 (by simp)).trans endWord,
      (fr.registers 3 (by simp)).trans one, fr.persistent, fr.keepsPending atEnd stack,
      updated, path⟩
  · intro node bs c top pending dom pc nodeWord stack atEnd topWord endWord one reject
    exact h.reject node c bs (start _ _ _ _ dom
      ⟨pc, nodeWord, stack, atEnd, topWord, endWord, one⟩) (Option.map_eq_none_iff.mp reject)

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
