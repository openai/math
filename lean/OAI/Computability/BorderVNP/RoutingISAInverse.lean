import OAI.Computability.BorderVNP.RoutingISALink

/-!
# Inverting the signed instruction table

Every accepting path from an assembled fragment either reaches an explicit
accept inside that fragment or returns normally and accepts in the continuation.
The decomposition retains the entire chronological trace, including private choices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w p : ℕ}

/-- A structured path that stops inside a fragment at an explicit accept instruction. -/
inductive EarlyAccept {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) :
    Code → Bank w → Memory w → List (TeamRAM.Event w) → Prop where
  | accept {s m} : EarlyAccept pub macros .accept s m []
  | seqLeft {a b s m es} (h : EarlyAccept pub macros a s m es) :
      EarlyAccept pub macros (.seq a b) s m es
  | seqRight {a b s m es t mt fs} (r : Runs pub macros a s m es t mt)
      (h : EarlyAccept pub macros b t mt fs) : EarlyAccept pub macros (.seq a b) s m (es ++ fs)
  | ifEq {x y a b s m es} (h : EarlyAccept pub macros (if s x = s y then a else b) s m es) :
      EarlyAccept pub macros (.ifEq x y a b) s m (tick w :: es)
  | ifLt {x y a b s m es} (h : EarlyAccept pub macros (if s x < s y then a else b) s m es) :
      EarlyAccept pub macros (.ifLt x y a b) s m (tick w :: es)
  | choose {a b s m es} (bit : Bool)
      (h : EarlyAccept pub macros (if bit then a else b) s m es) :
      EarlyAccept pub macros (.choose a b) s m (choiceTick w bit :: es)
  | whileBody {x y a s m es} (guard : s x < s y) (h : EarlyAccept pub macros a s m es) :
      EarlyAccept pub macros (.whileLt x y a) s m (tick w :: es)
  | whileNext {x y a s m es t mt fs} (guard : s x < s y)
      (r : Runs pub macros a s m es t mt) (h : EarlyAccept pub macros (.whileLt x y a) t mt fs) :
      EarlyAccept pub macros (.whileLt x y a) s m (tick w :: (es ++ fs))

/-- A fragment whose successful paths can only leave by normal return. -/
def Code.withoutAccept : Code → Bool
  | .accept => false
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b | .choose a b => a.withoutAccept && b.withoutAccept
  | .whileLt _ _ a => a.withoutAccept
  | _ => true

/-- Successful early termination requires an explicit accept somewhere in the fragment. -/
theorem EarlyAccept.containsAccept {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c s m es} (h : EarlyAccept pub macros c s m es) : c.withoutAccept = false := by
  induction h with
  | accept => rfl
  | seqLeft _ ih | seqRight _ _ ih | whileBody _ _ ih =>
    simp [Code.withoutAccept, ih]
  | whileNext _ _ _ ih => exact ih
  | ifEq _ ih | ifLt _ ih | choose _ _ ih =>
    split at ih <;> simp [Code.withoutAccept, ih]

/-- An accepting native trace with every previous word recovered from memory. -/
private abbrev Path {S : Type*} (P : S → TeamRAM.Instr w S) (s : S) (m : Memory w)
    (es : List (TeamRAM.Event w)) := TeamRAM.Local P s es ∧ TeamRAM.Correct m es

private theorem Path.halt {S : Type*} {P : S → TeamRAM.Instr w S} {s m es}
    (h : Path P s m es) (ha : P s = .accept) : es = [] := by
  cases es with
  | nil => rfl
  | cons e es => simpa [TeamRAM.Local, ha, TeamRAM.Instr.action] using h.1

private theorem Path.reject {S : Type*} {P : S → TeamRAM.Instr w S} {s m es}
    (h : Path P s m es) (ha : P s = .reject) : False := by
  cases es <;> simpa [TeamRAM.Local, ha, TeamRAM.Instr.action] using h.1

private theorem Path.uncons {S : Type*} {P : S → TeamRAM.Instr w S} {s m es}
    (h : Path P s m es) (hne : P s ≠ .accept) :
    ∃ a bits next sign fs, (P s).action = some a ∧
      (P s).advance bits (TeamRAM.previous m a) = some (next, sign) ∧
      Path P next (TeamRAM.afterAction m a) fs ∧ es = ⟨a, TeamRAM.previous m a, bits, sign⟩ :: fs := by
  cases es with
  | nil => exact (hne h.1).elim
  | cons e es =>
    obtain ⟨ha, next, hn, hl⟩ := h.1
    obtain ⟨ho, hm⟩ := h.2
    rcases e with ⟨a,vs,bs,sg⟩
    change vs = TeamRAM.previous m a at ho
    subst vs
    exact ⟨a,bs,next,sg,es,ha,hn,⟨hl,hm⟩,rfl⟩

private theorem Path.jump {S : Type*} {P : S → TeamRAM.Instr w S} {s m es next}
    (h : Path P s m es) (hp : P s = .localStep next .plus) :
    ∃ fs, es = tick w :: fs ∧ Path P next m fs := by
  obtain ⟨a,bits,t,sign,fs,ha,hn,ht,rfl⟩ := h.uncons (by simp [hp])
  rw [hp] at ha hn
  have := Option.some.inj ha
  subst a
  cases bits <;> simp [TeamRAM.Instr.advance, TeamRAM.previous] at hn
  obtain ⟨rfl,rfl⟩ := hn
  exact ⟨fs,rfl,ht⟩

private theorem Path.guess {S : Type*} {P : S → TeamRAM.Instr w S} {s m es} {next : Bool → S}
    (h : Path P s m es) (hp : P s = .choose next) :
    ∃ b fs, es = choiceTick w b :: fs ∧ Path P (next b) m fs := by
  obtain ⟨a,bits,t,sign,fs,ha,hn,ht,rfl⟩ := h.uncons (by simp [hp])
  rw [hp] at ha hn
  have := Option.some.inj ha
  subst a
  cases bits with
  | nil => simp [TeamRAM.Instr.advance] at hn
  | cons b bs =>
    cases bs <;> simp [TeamRAM.Instr.advance, TeamRAM.previous] at hn
    obtain ⟨rfl,rfl⟩ := hn
    exact ⟨b,fs,rfl,ht⟩

/-- Either a fragment reaches an explicit accepting instruction or its normal
trace ends at the prescribed continuation, where the remaining native trace accepts. -/
private def Parsed (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (P : TeamOpcode.State w p 64 → TeamRAM.Instr w (TeamOpcode.State w p 64))
    (finish : Fin p) (c : Code) (s : Bank w) (m : Memory w) (es : List (TeamRAM.Event w)) :=
  EarlyAccept pub macros c s m es ∨ ∃ gs t mt fs, es = gs ++ fs ∧
    Runs pub macros c s m gs t mt ∧ Path P ⟨finish,t⟩ mt fs

private theorem Parsed.wrap {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {P : TeamOpcode.State w p 64 → TeamRAM.Instr w (TeamOpcode.State w p 64)}
    {finish c d s m z mz es} (h : Parsed pub macros P finish c s m es)
    (front : List (TeamRAM.Event w))
    (early : ∀ {gs}, EarlyAccept pub macros c s m gs → EarlyAccept pub macros d z mz (front ++ gs))
    (normal : ∀ {gs t mt}, Runs pub macros c s m gs t mt → Runs pub macros d z mz (front ++ gs) t mt) :
    Parsed pub macros P finish d z mz (front ++ es) := by
  rcases h with ha | ⟨gs,t,mt,fs,rfl,hr,hp⟩
  · exact .inl (early ha)
  · exact .inr ⟨front ++ gs,t,mt,fs,List.append_assoc .. |>.symm,normal hr,hp⟩

private theorem atom_ne_accept {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} (s : Bank w) (h : c.isAtom = true) (pc : Fin p) :
    resume pc (c.atom pub macros s) ≠ .accept := by
  cases c <;> try contradiction
  case binary op d x y =>
    by_cases bad : (op = .div ∨ op = .mod) ∧ s y = 0 <;> simp [Code.atom, bad, resume]
  all_goals simp [Code.atom, resume]

private theorem parseAtom {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {rows : Fin p → Line p} {label : ℕ → Fin p} {start finish : ℕ}
    {c : Code} {s m es} (hc : Contains rows label start finish c)
    (ha : c.isAtom = true) (path : Path (fetch rows pub macros) ⟨label start,s⟩ m es) :
    Parsed pub macros (fetch rows pub macros) (label finish) c s m es := by
  have hf := (fetch_entry hc pub macros s).trans
    (fetch_atom label start start finish c ha pub macros s)
  obtain ⟨act,bits,z,sign,fs,hact,hstep,ht,rfl⟩ :=
    path.uncons (hf ▸ atom_ne_accept s ha _)
  rw [hf, resume_action] at hact
  rw [hf, resume_advance, Option.map_eq_some_iff] at hstep
  obtain ⟨⟨t,sg⟩,hadv,he⟩ := hstep
  cases he
  exact .inr ⟨[_],t,_,fs,rfl,.atom ha hact hadv,ht⟩

private theorem parse {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {rows : Fin p → Line p} {label : ℕ → Fin p} (k : ℕ) :
    ∀ {c : Code} {start finish : ℕ} {s : Bank w} {m es},
      es.length + c.slots = k → Contains rows label start finish c →
      Path (fetch rows pub macros) ⟨label start,s⟩ m es →
      Parsed pub macros (fetch rows pub macros) (label finish) c s m es := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro c start finish s m es hk hc hp
    by_cases hatom : c.isAtom = true
    · exact parseAtom hc hatom hp
    cases c <;> try contradiction
    case accept =>
      have hf : fetch rows pub macros ⟨label start,s⟩ = .accept := fetch_entry hc pub macros s
      obtain rfl := hp.halt hf
      exact .inl .accept
    case reject =>
      have hf : fetch rows pub macros ⟨label start,s⟩ = .reject := fetch_entry hc pub macros s
      exact (hp.reject hf).elim
    case seq a b =>
      have hca : Contains rows label start (start+a.slots) a := by
        intro i hi hj
        rw [hc i hi (by simp only [Code.slots]; omega)]
        simp [Code.emit, hj]
      have hcb : Contains rows label (start+a.slots) finish b := by
        intro i hi hj
        rw [hc i (by omega) (by simp only [Code.slots]; omega)]
        simp [Code.emit, not_lt.mpr hi]
      simp only [Code.slots] at hk
      have hleft := ih _ (by have := b.slots_pos; omega) rfl hca hp
      rcases hleft with early | ⟨gs,t,mt,fs,rfl,hr,hp'⟩
      · exact .inl (.seqLeft early)
      · have hright := ih _ (by simp only [List.length_append] at hk; have := a.slots_pos; omega)
          rfl hcb hp'
        exact hright.wrap gs (.seqRight hr ·) (.seq hr ·)
    case ifEq x y a b =>
      have hf := (fetch_entry hc pub macros s).trans (by
        simp only [Code.emit, ite_true]
        exact fetch_jumpEq pub macros (label start) (label (start+1)) (label (start+1+a.slots)) s x y)
      obtain ⟨fs,rfl,ht⟩ := hp.jump hf
      have hca := hc.forkLeft (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_left hi])
      have hcb := hc.forkRight (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_right (not_lt.mpr hi)])
      simp only [List.length_cons, Code.slots] at hk
      have hchild : Parsed pub macros (fetch rows pub macros) (label finish)
          (if s x = s y then a else b) s m fs := by
        split <;> rename_i hb
        · simp only [hb, ite_true] at ht
          exact ih _ (by omega) rfl hca ht
        · simp only [hb, ite_false] at ht
          exact ih _ (by omega) rfl hcb ht
      exact hchild.wrap [tick w] (.ifEq ·) (.ifEq ·)
    case ifLt x y a b =>
      have hf := (fetch_entry hc pub macros s).trans (by
        simp only [Code.emit, ite_true]
        exact fetch_jumpLt pub macros (label start) (label (start+1)) (label (start+1+a.slots)) s x y)
      obtain ⟨fs,rfl,ht⟩ := hp.jump hf
      have hca := hc.forkLeft (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_left hi])
      have hcb := hc.forkRight (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_right (not_lt.mpr hi)])
      simp only [List.length_cons, Code.slots] at hk
      have hchild : Parsed pub macros (fetch rows pub macros) (label finish)
          (if s x < s y then a else b) s m fs := by
        split <;> rename_i hb
        · simp only [hb, ite_true] at ht
          exact ih _ (by omega) rfl hca ht
        · simp only [hb, ite_false] at ht
          exact ih _ (by omega) rfl hcb ht
      exact hchild.wrap [tick w] (.ifLt ·) (.ifLt ·)
    case choose a b =>
      have hf := (fetch_entry hc pub macros s).trans (by
        simp only [Code.emit, ite_true]
        exact fetch_choose pub macros (label start) (label (start+1)) (label (start+1+a.slots)) s)
      obtain ⟨bit,fs,rfl,ht⟩ := hp.guess hf
      have hca := hc.forkLeft (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_left hi])
      have hcb := hc.forkRight (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_right (not_lt.mpr hi)])
      simp only [List.length_cons, Code.slots] at hk
      have hchild : Parsed pub macros (fetch rows pub macros) (label finish)
          (if bit then a else b) s m fs := by
        split <;> rename_i hb
        · simp only [hb, ite_true] at ht
          exact ih _ (by omega) rfl hca ht
        · simp only [hb] at ht
          exact ih _ (by omega) rfl hcb ht
      exact hchild.wrap [choiceTick w bit] (.choose bit ·) (.choose bit ·)
    case whileLt x y body =>
      have hf := (fetch_entry hc pub macros s).trans (by
        simp only [Code.emit, ite_true]
        exact fetch_jumpLt pub macros (label start) (label (start+1)) (label finish) s x y)
      obtain ⟨fs,rfl,ht⟩ := hp.jump hf
      by_cases guard : s x < s y
      · simp only [guard, ite_true] at ht
        have child : Contains rows label (start+1) start body := by
          intro i hlo hhi
          rw [hc i (by omega) (by simp only [Code.slots]; omega)]
          simp only [Code.emit, ite_eq_right (by omega : i ≠ start)]
        have bodyPath := ih _ (by simp only [List.length_cons, Code.slots] at hk; omega) rfl child ht
        rcases bodyPath with early | ⟨gs,t,mt,fs',rfl,hr,hp'⟩
        · exact .inl (.whileBody guard early)
        · have loopPath := ih _ (by simp only [List.length_cons, List.length_append] at hk; omega)
            rfl hc hp'
          exact loopPath.wrap (tick w :: gs) (.whileNext guard hr ·) (.whileStep guard hr ·)
      · simp only [guard, ite_false] at ht
        exact .inr ⟨[tick w],s,m,fs,rfl,.whileDone guard,ht⟩

/-- An accepting native execution is either an early structured accept or a full
structured run to the table's accepting continuation. The event choices are the
exact supplied choice tape. -/
theorem Code.of_execute {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s : Bank w} {m bits es}
    (he : TeamRAM.execute (c.program.fetch pub macros) ⟨0,s⟩ m bits = some es) :
    (EarlyAccept pub macros c s m es ∨ ∃ t mt, Runs pub macros c s m es t mt) ∧
      es.map TeamRAM.Event.choices = bits := by
  obtain ⟨hl,hm,hbits⟩ := TeamRAM.execute_spec he
  refine ⟨?_, hbits⟩
  let lab (i : ℕ) : Fin (c.slots+1) := ⟨min i c.slots, by omega⟩
  have hc : Contains c.row lab 0 c.slots c := by
    intro i _ hi
    have hlt : i < c.slots := by omega
    simp [lab, Code.row, min_eq_left hlt.le, hlt]
  have atZero : lab 0 = 0 := Fin.ext (by simp [lab])
  have atLast : lab c.slots = Fin.last c.slots := Fin.ext (by simp [lab])
  have fetchEq : fetch c.row pub macros = c.program.fetch pub macros := by
    funext q
    exact fetch_row c pub macros q
  have hp : Path (fetch c.row pub macros) ⟨lab 0,s⟩ m es := by
    rw [fetchEq, atZero]; exact ⟨hl,hm⟩
  rcases parse _ rfl hc hp with early | ⟨gs,t,mt,fs,rfl,hr,ht⟩
  · exact .inl early
  · obtain rfl := ht.halt (by rw [fetchEq,atLast]; exact c.fetch_finish pub macros t)
    exact .inr ⟨t,mt,by simpa using hr⟩

/-- For a table with only fall-through success, native acceptance coincides with
structured execution at exactly the given sequence of private choices. -/
theorem Code.execute_iff_runs {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} (hc : c.withoutAccept = true) {s : Bank w} {m bits es} :
    TeamRAM.execute (c.program.fetch pub macros) ⟨0,s⟩ m bits = some es ↔
      (∃ t mt, Runs pub macros c s m es t mt) ∧ es.map TeamRAM.Event.choices = bits := by
  constructor
  · intro he
    obtain ⟨early | h, hbits⟩ := of_execute he
    · simp [early.containsAccept] at hc
    · exact ⟨h,hbits⟩
  · rintro ⟨⟨t,mt,h⟩, rfl⟩
    exact h.execute


private theorem Path.prepend {S : Type*} {P : S → TeamRAM.Instr w S} {s m gs t mt fs}
    (head : NativePrefix P s m gs t mt) (tail : Path P t mt fs) : Path P s m (gs ++ fs) := by
  induction head with
  | nil => exact tail
  | cons ha hn _ ih => exact ⟨⟨ha,_,hn,(ih tail).1⟩,rfl,(ih tail).2⟩

private theorem Path.consJump {S : Type*} {P : S → TeamRAM.Instr w S} {s m q es}
    (hp : P s = .localStep q .plus) (tail : Path P q m es) : Path P s m (tick w :: es) :=
  ⟨⟨by rw [hp]; rfl, q, by rw [hp]; rfl, tail.1⟩,rfl,tail.2⟩

private theorem Path.consGuess {S : Type*} {P : S → TeamRAM.Instr w S} {s m f es} (b : Bool)
    (hp : P s = .choose f) (tail : Path P (f b) m es) : Path P s m (choiceTick w b :: es) :=
  ⟨⟨by rw [hp]; rfl, f b, by rw [hp]; rfl, tail.1⟩,rfl,tail.2⟩

private theorem EarlyAccept.path {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c s m es} (h : EarlyAccept pub macros c s m es)
    (rows : Fin p → Line p) (label : ℕ → Fin p) {start finish : ℕ}
    (hc : Contains rows label start finish c) : Path (fetch rows pub macros) ⟨label start,s⟩ m es := by
  induction h generalizing start finish with
  | @accept s m => exact ⟨fetch_entry hc pub macros s,trivial⟩
  | @seqLeft a b s m es early ih =>
    apply ih (finish := start+a.slots)
    intro i hi hj
    rw [hc i hi (by simp only [Code.slots]; omega)]
    simp [Code.emit, hj]
  | @seqRight a b s m es t mt fs r early ih =>
    have hca : Contains rows label start (start+a.slots) a := by
      intro i hi hj
      rw [hc i hi (by simp only [Code.slots]; omega)]
      simp [Code.emit, hj]
    apply Path.prepend (r.nativePrefix rows label hca) (ih (finish := finish) _)
    intro i hi hj
    rw [hc i (by omega) (by simp only [Code.slots]; omega)]
    simp [Code.emit, not_lt.mpr hi]
  | @ifEq x y a b s m es early ih =>
    have hf := (fetch_entry hc pub macros s).trans (by
      simp only [Code.emit, ite_true]
      exact fetch_jumpEq pub macros (label start) (label (start+1)) (label (start+1+a.slots)) s x y)
    apply Path.consJump hf
    by_cases hbit : s x = s y
    · simp only [hbit, ite_true] at ih ⊢
      exact ih (hc.forkLeft (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_left hi]))
    · simp only [hbit, ite_false] at ih ⊢
      exact ih (hc.forkRight (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_right (not_lt.mpr hi)]))
  | @ifLt x y a b s m es early ih =>
    have hf := (fetch_entry hc pub macros s).trans (by
      simp only [Code.emit, ite_true]
      exact fetch_jumpLt pub macros (label start) (label (start+1)) (label (start+1+a.slots)) s x y)
    apply Path.consJump hf
    by_cases hbit : s x < s y
    · simp only [hbit, ite_true] at ih ⊢
      exact ih (hc.forkLeft (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_left hi]))
    · simp only [hbit, ite_false] at ih ⊢
      exact ih (hc.forkRight (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_right (not_lt.mpr hi)]))
  | @choose a b s m es bit early ih =>
    have hf := (fetch_entry hc pub macros s).trans (by
      simp only [Code.emit, ite_true]
      exact fetch_choose pub macros (label start) (label (start+1)) (label (start+1+a.slots)) s)
    apply Path.consGuess bit hf
    by_cases hbit : bit = true
    · simp only [hbit, ite_true] at ih ⊢
      exact ih (hc.forkLeft (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_left hi]))
    · simp only [hbit] at ih ⊢
      exact ih (hc.forkRight (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_right (not_lt.mpr hi)]))
  | @whileBody x y a s m es guard early ih =>
    refine Path.consJump (q := ⟨label (start+1),s⟩) ?_ ?_
    · simpa only [Code.emit, ite_true, fetch_jumpLt, ite_eq_left guard] using fetch_entry hc pub macros s
    apply ih (finish := start)
    intro i hlo hhi
    rw [hc i (by omega) (by simp only [Code.slots]; omega)]
    simp only [Code.emit, ite_eq_right (by omega : i ≠ start)]
  | @whileNext x y a s m es t mt fs guard r early ih =>
    have child : Contains rows label (start+1) start a := by
      intro i hlo hhi
      rw [hc i (by omega) (by simp only [Code.slots]; omega)]
      simp only [Code.emit, ite_eq_right (by omega : i ≠ start)]
    apply Path.consJump _ ((ih hc).prepend (r.nativePrefix rows label child))
    simpa only [Code.emit, ite_true, fetch_jumpLt, ite_eq_left guard] using fetch_entry hc pub macros s

/-- An explicit structured accepting halt gives a successful native execution
on the entire tape of recorded ordinary and private choices. -/
theorem EarlyAccept.execute {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s : Bank w} {m es} (h : EarlyAccept pub macros c s m es) :
    TeamRAM.execute (c.program.fetch pub macros) ⟨0,s⟩ m (es.map TeamRAM.Event.choices) = some es := by
  let lab (i : ℕ) : Fin (c.slots+1) := ⟨min i c.slots, by omega⟩
  have hc : Contains c.row lab 0 c.slots c := by
    intro i _ hi
    have hlt : i < c.slots := by omega
    simp [lab, Code.row, min_eq_left hlt.le, hlt]
  have hp := h.path c.row lab hc
  have fetchEq : fetch c.row pub macros = c.program.fetch pub macros := by
    funext q
    exact fetch_row c pub macros q
  have atZero : lab 0 = 0 := Fin.ext (by simp [lab])
  rw [fetchEq, atZero] at hp
  exact TeamRAM.execute_iff.mpr ⟨hp.1,hp.2,rfl⟩

/-- Complete native accepting trace correspondence, including early accepting
halts and implicit acceptance on returning to the top-level continuation. -/
theorem Code.execute_iff {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s : Bank w} {m bits es} :
    TeamRAM.execute (c.program.fetch pub macros) ⟨0,s⟩ m bits = some es ↔
      (EarlyAccept pub macros c s m es ∨ ∃ t mt, Runs pub macros c s m es t mt) ∧
        es.map TeamRAM.Event.choices = bits := by
  refine ⟨of_execute, ?_⟩
  rintro ⟨early | ⟨t,mt,normal⟩,rfl⟩
  · exact early.execute
  · exact normal.execute

end RoutingISA

end BorderVNP
end Computability
end OAI
