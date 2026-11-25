import OAI.ThreeFlat.RAM.CachedBlock

namespace OAI
/-! # Preserving arbitrary native continuations after cached-operand blocks -/

namespace ThreeFlat.RAM.CachedBlock
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
variable {w p r k P R K : ℕ}

def atPC {a b : ℕ} (i : Fin b) (c : Config w a R) : Config w b R :=
  ⟨i,c.persistent,c.reg,c.privateMem⟩

def liftPC {a b : ℕ} (label : Fin a→Fin b) (c : Config w a R) := atPC (label c.pc) c

private def actionMap {A C : Type*} (f : A→C) : CallAction w A→CallAction w C
  | .localStep c => .localStep (f c)
  | .branch b => .branch (fun x => f (b x))
  | .read a n => .read a (fun x => f (n x))
  | .write a v c => .write a v (f c)
  | .finish v => .finish v
  | .reject => .reject

private theorem run_map {a b s t : ℕ} (f : Fin a→Fin b) (pub : Fin s→Fin t)
    (data : Fin t→Word w) (i : Instr w a R s) (c : Config w a R) (fromPC : Fin b) :
    (mapInstr f id pub i).run data (atPC fromPC c)=
      actionMap (liftPC f) (i.run (data ∘ pub) c) := by
  cases i <;> simp only [mapInstr,Instr.run,actionMap,id_eq,Function.comp_apply,atPC,liftPC,
    Config.put,Config.store,apply_ite] <;> rfl

def Cached {a : ℕ} (reg : Fin (r+k) ↪ Fin R) (values : Fin k→Word w) (c : Config w a R) :=
  ∀ j,c.reg (reg (Fin.natAdd r j))=values j

private def every {A : Type*} (good : A→Prop) : CallAction w A→Prop
  | .localStep c | .write _ _ c => good c
  | .branch f => ∀ b,good (f b)
  | .read _ f => ∀ x,good (f x)
  | _ => True

private theorem protects {a : ℕ} (reg : Fin (r+k) ↪ Fin R) (values : Fin k→Word w)
    (i : Instr w a r k) (c : Config w a R) (hc : Cached reg values c) :
    every (Cached reg values) ((mapInstr id (reg ∘ Fin.castAdd k) id i).run values c) := by
  have apart (x : Fin k) (y : Fin r) : reg (Fin.natAdd r x)≠reg (y.castAdd k) := by
    intro eq
    have same := congrArg Fin.val (reg.injective eq)
    simp only [Fin.val_natAdd,Fin.val_castAdd] at same
    have small := y.isLt
    omega
  cases i <;> simp [mapInstr,Instr.run,every,Cached,Config.put,Config.store,Function.update_of_ne,
    apart] <;> solve_by_elim

private theorem cached_eq {a : ℕ} (reg : Fin (r+k) ↪ Fin R) (values : Fin k→Word w)
    (data : Fin K→Word w) (i : Instr w a r k) (c : Config w a R) (hc : Cached reg values c) :
    (cachedInstr id (reg ∘ Fin.castAdd k) (reg ∘ Fin.natAdd r) i).run data c=
    (mapInstr id (reg ∘ Fin.castAdd k) id i).run values c := by
  cases i <;> try rfl
  case publicWord dst idx next =>
    simp [cachedInstr,mapInstr,Instr.run,hc idx]

private theorem map_cached {a b : ℕ} (f : Fin a→Fin b) (reg : Fin r→Fin R) (cache : Fin k→Fin R)
    (i : Instr w a r k) :
    mapInstr f id (id : Fin K→Fin K) (cachedInstr id reg cache i)=cachedInstr f reg cache i := by
  cases i <;> rfl

variable {F : Type*} [Semiring F]

private def after {A : Type*} (field : FieldCode F w) (next : A→Memory w→F) (m : Memory w) :
    CallAction w A→F
  | .localStep c => next c m
  | .branch f => next (f false) m + next (f true) m
  | .read a f => next (f (m a.val)) m
  | .write a v c => next c (writeMemory m a v)
  | .finish v => field.terminal v
  | .reject => 0

private theorem mass_next {A : Type*} (field : FieldCode F w) (pgm : Program w A)
    (t : ℕ) (c : A) (m : Memory w) :
    mass field pgm (t+1) c m=after field (mass field pgm t) m (pgm.step c) := by
  rw [mass]
  cases pgm.step c <;> rfl

private theorem after_match {A C D : Type*} (field : FieldCode F w) (m : Memory w) (a : CallAction w A)
    (good : A→Prop) (ok : every good a) (l : A→C) (r : A→D) (f : C→Memory w→F) (g : D→Memory w→F)
    (same : ∀ x o,good x → f (l x) o=g (r x) o) :
    after field f m (actionMap l a)=after field g m (actionMap r a) := by
  cases a with
  | localStep c => exact same _ _ ok
  | branch b => exact congrArg₂ (·+·) (same _ _ (ok false)) (same _ _ (ok true))
  | read a c => exact same _ _ (ok _)
  | write a v c => exact same _ _ ok
  | finish _ => rfl
  | reject => rfl

private theorem action_id {A : Type*} (a : CallAction w A) : actionMap id a=a := by
  cases a <;> rfl

/-- The source proof runs in the first bank with the genuine operand values. Its
exit enters the second bank, which is an exact copy of the whole physical host.
The latter includes every subsequent entry to the same lowering. -/
def shadow (b : Block w p r k) (M : Machine w P R K) (reg : Fin (r+k) ↪ Fin R)
    (exit : Fin P) (values : Fin k→Word w) : Machine w (p+P) R (k+K) where
  entry := b.first.castAdd P
  publicData := Fin.addCases values M.publicData
  code := Fin.addCases
    (b.emit (Fin.castAddEmb P) ((Fin.castAddEmb k).trans reg) (Fin.castAdd K) (Fin.natAdd p exit))
    (fun i => mapInstr (Fin.natAdd p) id (Fin.natAdd k) (M.code i))

theorem shadow_installed (b : Block w p r k) (M : Machine w P R K) (reg : Fin (r+k) ↪ Fin R)
    (exit : Fin P) (values : Fin k→Word w) :
    b.Installed (shadow b M reg exit values) (Fin.castAddEmb P) ((Fin.castAddEmb k).trans reg)
      (Fin.castAdd K) (Fin.natAdd p exit) := by
  intro i
  simp [shadow]

@[simp] theorem shadow_param (b : Block w p r k) (M : Machine w P R K) (reg : Fin (r+k) ↪ Fin R)
    (exit : Fin P) (values : Fin k→Word w) (j : Fin k) :
    (shadow b M reg exit values).publicData (j.castAdd K)=values j := by simp [shadow]

theorem mass_right (b : Block w p r k) (M : Machine w P R K) (reg : Fin (r+k) ↪ Fin R)
    (exit : Fin P) (values : Fin k→Word w) (field : FieldCode F w) (t : ℕ)
    (c : Config w P R) (m : Memory w) :
    mass field (shadow b M reg exit values).program t (liftPC (Fin.natAdd p) c) m =
      mass field M.program t c m := by
  induction t generalizing c m with
  | zero => rfl
  | succ t ih =>
    rw [mass_next,mass_next]
    have step : (shadow b M reg exit values).program.step (liftPC (Fin.natAdd p) c)=
        actionMap (liftPC (Fin.natAdd p)) (M.program.step c) := by
      have hp : (shadow b M reg exit values).publicData ∘ Fin.natAdd k=M.publicData := by
        funext j
        simp [shadow]
      have row : (shadow b M reg exit values).code (Fin.natAdd p c.pc)=
          mapInstr (Fin.natAdd p) id (Fin.natAdd k) (M.code c.pc) := by
        simp [shadow]
      change ((shadow b M reg exit values).code (Fin.natAdd p c.pc)).run _ (atPC (Fin.natAdd p c.pc) c)=_
      rw [row,run_map,hp]; rfl
    rw [step]
    calc
      _=after field (mass field M.program t) m (actionMap id (M.program.step c)) :=
        after_match field m _ (fun _ => True) (by cases M.program.step c <;> simp [every]) _ _ _ _
          (fun x o _ => ih x o)
      _=_ := by rw [action_id]

/-- At each original label, program counters in the two machines can have
different numerical values. All host registers, private words, persistent
state, and external cells start identical and execute the same update. -/
theorem mass_body (b : Block w p r k) (nat : Natural b) (M : Machine w P R K)
    (pc : Fin p ↪ Fin P) (reg : Fin (r+k) ↪ Fin R) (pub : Fin 0→Fin K) (exit : Fin P)
    (ins : (body b).Installed M pc reg pub exit) (values : Fin k→Word w)
    (field : FieldCode F w) (t : ℕ) (j : Fin p) (c : Config w P R) (m : Memory w)
    (entry : c.pc=pc j) (loaded : Cached reg values c) :
    mass field (shadow b M reg exit values).program t (atPC (j.castAdd P) c) m =
      mass field M.program t c m := by
  let H := shadow b M reg exit values
  let left := targets (Fin.castAddEmb P) (Fin.natAdd p exit)
  let right := targets pc exit
  let orig : Fin r→Fin R := reg ∘ Fin.castAdd k
  let cache : Fin k→Fin R := reg ∘ Fin.natAdd r
  induction t generalizing j c m with
  | zero => rfl
  | succ t ih =>
    let i := canonicalRow b j
    let s : Config w (p+1) R := atPC (Fin.natAdd p (0 : Fin 1)) c
    let a := (mapInstr id orig id i).run values s
    have ok : every (Cached reg values) a := protects reg values i s loaded
    have source : H.program.step (atPC (j.castAdd P) c)=actionMap (liftPC left) a := by
      change (H.code (j.castAdd P)).run H.publicData _=_
      have row := shadow_installed b M reg exit values j
      change H.code (Fin.castAdd P j)=_ at row
      rw [row,nat (Fin.castAddEmb P) ((Fin.castAddEmb k).trans reg) (Fin.castAdd K) (Fin.natAdd p exit)]
      have mp : mapInstr left id (Fin.castAdd K) (mapInstr id orig id i)=
          mapInstr left ((Fin.castAddEmb k).trans reg) (Fin.castAdd K) i := by
        rw [mapInstr_comp]; rfl
      rw [←mp]
      change (mapInstr left id (Fin.castAdd K) (mapInstr id orig id i)).run H.publicData
        (atPC (j.castAdd P) s)=_
      rw [run_map]
      have hp : H.publicData ∘ Fin.castAdd K=values := funext (shadow_param b M reg exit values)
      rw [hp]
    have target : M.program.step c=actionMap (liftPC right) a := by
      change (M.code c.pc).run M.publicData c=_
      rw [entry,ins]
      change (cachedInstr right orig cache i).run _ _=_
      rw [←map_cached]
      have recn : atPC c.pc s=c := by cases c; rfl
      conv_lhs => rw [←recn]
      rw [run_map]
      change actionMap (liftPC right) ((cachedInstr id orig cache i).run M.publicData s)=_
      rw [cached_eq reg values M.publicData i s loaded]
    rw [mass_next,mass_next,source,target]
    apply after_match field m a (Cached reg values) ok
    intro x o good
    have next (n : Fin (p+1)) :
        mass field H.program t (atPC (left n) x) o=
        mass field M.program t (atPC (right n) x) o := by
      refine Fin.addCases (fun u => ?_) (fun u => ?_) n
      · simp only [left,right,targets,Fin.addCases_left,Fin.castAddEmb_apply]
        exact ih u (atPC (pc u) x) o rfl good
      · simp only [left,right,targets,Fin.addCases_right]
        exact mass_right b M reg exit values field t (atPC exit x) o
    exact next x.pc

end ThreeFlat.RAM.CachedBlock

namespace ThreeFlat.RAM.CachedBlock
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
variable {w p r k P R K : ℕ}

private theorem advance_match {A C D : Type*} (L : Program w C) (T : Program w D)
    (c : C) (d : D) (m : Memory w) (t : ℕ) (a : CallAction w A) (good : A→Prop)
    (ok : every good a) (l : A→C) (r : A→D)
    (ls : L.step c=actionMap l a) (rs : T.step d=actionMap r a)
    {z : C} {y : D} {out : Memory w}
    (ih : ∀ x o, good x → advance L t (l x) o=some (z,out) →
      advance T t (r x) o=some (y,out))
    (step : advance L (t+1) c m=some (z,out)) :
    advance T (t+1) d m=some (y,out) := by
  rw [advance,ls] at step
  rw [advance,rs]
  cases a with
  | localStep x => exact ih _ _ ok step
  | read addr f => exact ih _ _ (ok _) step
  | write addr v x => exact ih _ _ ok step
  | branch f => contradiction
  | finish v => contradiction
  | reject => contradiction

private theorem advance_right (b : Block w p r k) (M : Machine w P R K)
    (reg : Fin (r+k) ↪ Fin R) (exit : Fin P) (values : Fin k→Word w) (t : ℕ)
    (c : Config w P R) (m : Memory w) {z : Config w (p+P) R} {out : Memory w}
    (step : advance (shadow b M reg exit values).program t (liftPC (Fin.natAdd p) c) m=some (z,out))
    (done : z.pc=Fin.natAdd p exit) :
    advance M.program t c m=some (atPC exit z,out) := by
  induction t generalizing c m with
  | zero =>
    obtain ⟨hz,hm⟩ := Prod.mk.inj (Option.some.inj step)
    subst z
    subst out
    have hp : c.pc=exit := Fin.natAdd_injective P p done
    cases c with
    | mk i s v pm =>
      change i=exit at hp
      subst i
      rfl
  | succ t ih =>
    have ls : (shadow b M reg exit values).program.step (liftPC (Fin.natAdd p) c)=
        actionMap (liftPC (Fin.natAdd p)) (M.program.step c) := by
      have hp : (shadow b M reg exit values).publicData ∘ Fin.natAdd k=M.publicData := by
        funext j
        simp [shadow]
      have row : (shadow b M reg exit values).code (Fin.natAdd p c.pc)=
          mapInstr (Fin.natAdd p) id (Fin.natAdd k) (M.code c.pc) := by
        simp [shadow]
      change ((shadow b M reg exit values).code (Fin.natAdd p c.pc)).run _
        (atPC (Fin.natAdd p c.pc) c)=_
      rw [row,run_map,hp]; rfl
    exact advance_match _ _ _ _ m t (M.program.step c) (fun _ => True)
      (by cases M.program.step c <;> simp [every]) _ id ls (action_id _).symm
      (fun x o _ h => ih x o h) step

/-- A deterministic prefix ending at the shadow exit takes the physical host
to its own exit with the same registers, private state, and external memory. -/
theorem advance_body (b : Block w p r k) (nat : Natural b) (M : Machine w P R K)
    (pc : Fin p ↪ Fin P) (reg : Fin (r+k) ↪ Fin R) (pub : Fin 0→Fin K) (exit : Fin P)
    (ins : (body b).Installed M pc reg pub exit) (values : Fin k→Word w)
    (t : ℕ) (j : Fin p) (c : Config w P R) (m : Memory w)
    (entry : c.pc=pc j) (loaded : Cached reg values c) {z : Config w (p+P) R} {out : Memory w}
    (step : advance (shadow b M reg exit values).program t (atPC (j.castAdd P) c) m=some (z,out))
    (done : z.pc=Fin.natAdd p exit) :
    advance M.program t c m=some (atPC exit z,out) := by
  let H := shadow b M reg exit values
  let left := targets (Fin.castAddEmb P) (Fin.natAdd p exit)
  let right := targets pc exit
  let orig : Fin r→Fin R := reg ∘ Fin.castAdd k
  let cache : Fin k→Fin R := reg ∘ Fin.natAdd r
  induction t generalizing j c m with
  | zero =>
    have hz := (Prod.mk.inj (Option.some.inj step)).1
    subst z
    change j.castAdd P=Fin.natAdd p exit at done
    have h := congrArg Fin.val done
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h
    have hj := j.isLt
    omega
  | succ t ih =>
    let i := canonicalRow b j
    let s : Config w (p+1) R := atPC (Fin.natAdd p (0 : Fin 1)) c
    let a := (mapInstr id orig id i).run values s
    have ok : every (Cached reg values) a := protects reg values i s loaded
    have source : H.program.step (atPC (j.castAdd P) c)=actionMap (liftPC left) a := by
      change (H.code (j.castAdd P)).run H.publicData _=_
      have row := shadow_installed b M reg exit values j
      change H.code (Fin.castAdd P j)=_ at row
      rw [row,nat (Fin.castAddEmb P) ((Fin.castAddEmb k).trans reg) (Fin.castAdd K) (Fin.natAdd p exit)]
      have mp : mapInstr left id (Fin.castAdd K) (mapInstr id orig id i)=
          mapInstr left ((Fin.castAddEmb k).trans reg) (Fin.castAdd K) i := by
        rw [mapInstr_comp]; rfl
      rw [←mp]
      change (mapInstr left id (Fin.castAdd K) (mapInstr id orig id i)).run H.publicData
        (atPC (j.castAdd P) s)=_
      rw [run_map]
      have hp : H.publicData ∘ Fin.castAdd K=values := funext (shadow_param b M reg exit values)
      rw [hp]
    have target : M.program.step c=actionMap (liftPC right) a := by
      change (M.code c.pc).run M.publicData c=_
      rw [entry,ins]
      change (cachedInstr right orig cache i).run _ _=_
      rw [←map_cached]
      have recn : atPC c.pc s=c := by cases c; rfl
      conv_lhs => rw [←recn]
      rw [run_map]
      change actionMap (liftPC right) ((cachedInstr id orig cache i).run M.publicData s)=_
      rw [cached_eq reg values M.publicData i s loaded]
    apply advance_match H.program M.program _ _ m t a (Cached reg values) ok _ _ source target _ step
    intro x o good
    have next (n : Fin (p+1)) :
        advance H.program t (atPC (left n) x) o=some (z,out) →
        advance M.program t (atPC (right n) x) o=some (atPC exit z,out) := by
      refine Fin.addCases (fun u => ?_) (fun u => ?_) n
      · simp only [left,right,targets,Fin.addCases_left,Fin.castAddEmb_apply]
        exact fun h => ih u (atPC (pc u) x) o rfl good h
      · simp only [left,right,targets,Fin.addCases_right]
        exact fun h => advance_right b M reg exit values t (atPC exit x) o h done
    exact next x.pc

end ThreeFlat.RAM.CachedBlock

end OAI
