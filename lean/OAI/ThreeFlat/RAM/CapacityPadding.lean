import OAI.ThreeFlat.RAM.NativeRelocate
import OAI.ThreeFlat.RAM.ProgramValue

namespace OAI
/-! # Padding a native RAM to common public program and register capacities -/

namespace ThreeFlat.RAM.CapacityPadding

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
variable {F α : Type*} {w p r k P R K : ℕ}

/-- Embed a finite vector as the low prefix, filling every extra position
with the same public value. -/
def fillPrefix (fallback : α) (xs : Fin p → α) (i : Fin P) : α :=
  if h : i.val < p then xs ⟨i.val,h⟩ else fallback

@[simp] theorem prefix_at (fallback : α) (xs : Fin p → α) (hp : p ≤ P) (i : Fin p) :
    fillPrefix fallback xs (i.castLE hp) = xs i := by simp [fillPrefix,i.isLt]

/-- The added instruction addresses reject and the added public words
are zero. All original opcodes use their original numeric indices. -/
def pad (M : Machine w p r k) (hp : p ≤ P) (hr : r ≤ R) (hk : k ≤ K) : Machine w P R K where
  entry := M.entry.castLE hp
  code := fillPrefix .reject (fun i => NativeRelocate.relocate (Fin.castLEEmb hp) (Fin.castLEEmb hr)
    (fun j => j.castLE hk) (M.code i))
  publicData := fillPrefix 0 M.publicData

private def embed (hp : p ≤ P) (_hr : r ≤ R) (c : Config w p r) : Config w P R :=
  ⟨c.pc.castLE hp,c.persistent,fillPrefix 0 c.reg,c.privateMem⟩

private theorem prefix_update (xs : Fin r → Word w) (hr : r ≤ R) (a : Fin r) (v : Word w) :
    Function.update (fillPrefix 0 xs) (a.castLE hr) v = fillPrefix 0 (Function.update xs a v) := by
  funext j
  by_cases hit : j = a.castLE hr
  · subst j
    simp
  · rw [Function.update_of_ne hit]
    by_cases hl : j.val < r
    · have hne : (⟨j.val,hl⟩ : Fin r) ≠ a := fun he => hit (Fin.ext (congrArg (fun z : Fin r => z.val) he))
      simp [fillPrefix,hl,Function.update_of_ne hne]
    · simp [fillPrefix,hl]

private theorem put_embed (hp : p ≤ P) (hr : r ≤ R) (c : Config w p r) (n : Fin p) (a : Fin r) (v : Word w) :
    (embed hp hr c).put (n.castLE hp) (a.castLE hr) v = embed hp hr (c.put n a v) := by
  simp [Config.put,embed,prefix_update]

private def mapAction {C D : Type*} (up : C → D) : CallAction w C → CallAction w D
  | .localStep c => .localStep (up c)
  | .branch f => .branch (fun b => up (f b))
  | .read a f => .read a (fun x => up (f x))
  | .write a v c => .write a v (up c)
  | .finish v => .finish v
  | .reject => .reject

private theorem step_pad (M : Machine w p r k) (hp : p ≤ P) (hr : r ≤ R) (hk : k ≤ K) (c : Config w p r) :
    (pad M hp hr hk).program.step (embed hp hr c) = mapAction (embed hp hr) (M.program.step c) := by
  change ((pad M hp hr hk).code (c.pc.castLE hp)).run (fillPrefix 0 M.publicData) (embed hp hr c) =
    mapAction _ ((M.code c.pc).run M.publicData c)
  simp only [pad,prefix_at]
  have reg (i : Fin r) : (embed hp hr c).reg (i.castLE hr) = c.reg i :=
    prefix_at 0 c.reg hr i
  cases M.code c.pc <;>
    simp only [NativeRelocate.relocate,Instr.run,mapAction,Fin.castLEEmb_apply,reg,prefix_at,put_embed] <;>
    try rfl
  all_goals first
    | exact congrArg CallAction.localStep (put_embed hp hr c _ _ _)
    | (congr 1; funext v; done)
    | split <;> rfl
    | congr 1; funext b; cases b <;> rfl

/-- Padding changes neither fuel consumption nor the sum of path weights. -/
theorem value_pad [Semiring F] (code : FieldCode F w) (M : Machine w p r k)
    (hp : p ≤ P) (hr : r ≤ R) (hk : k ≤ K) (fuel : ℕ) (st : Word w) (m : Memory w) :
    value code (pad M hp hr hk) fuel st m = value code M fuel st m := by
  have sim (f : ℕ) (c : Config w p r) (mem : Memory w) :
      mass code (pad M hp hr hk).program f (embed hp hr c) mem = mass code M.program f c mem := by
    induction f generalizing c mem with
    | zero => rfl
    | succ f ih =>
      simp only [mass,step_pad]
      cases M.program.step c <;> simp only [mapAction,ih]
  have hs : (pad M hp hr hk).program.start st = embed hp hr (M.program.start st) := by
    have hz : fillPrefix (0 : Word w) (fun _ : Fin r => 0) = (fun _ : Fin R => 0) := by
      funext j
      simp [fillPrefix]
    simp [Machine.program,embed,pad,hz]
  rw [value, hs]
  exact sim ..

/-- Executing the common-capacity self-advice directly simulates the
original program, with the concrete installed bits also visible in memory. -/
theorem adviceValue_pad [Semiring F] (code : FieldCode F w) (M : Machine w p r k) (u : ℕ)
    (hp : p ≤ u) (hr : r ≤ u) (hk : k ≤ u) (h : TextFits w u u u)
    {q : ℕ} (fits : (1+6*u+u)*w ≤ q) (tail : Fin q → Bool)
    (fuel : ℕ) (st : Word w) (base : ℕ) (m : Memory w) :
    let D := installProgram (pad M hp hr hk) tail
    adviceValue code u u u fits D fuel st base m = value code M fuel st (memoryWithAdvice base D m) := by
  dsimp only
  rw [adviceValue_install _ _ h, value_pad]

end ThreeFlat.RAM.CapacityPadding

end OAI
