import OAI.Computability.VPVNP.PairNodeChildLoop

/-!
# Selecting the resident shrinking layout

The old level's field at offset 38 holds the chosen layout bit. The
vertex reader doubles the five-bit literal 19 to obtain that offset,
reads the published field and enters the matching gather continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkLayoutBranch

open BurstRAM BurstRAM.PrivateRAM NodeArguments.ChildScan
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.nil ReadPrefix.tick ReadPrefix.read ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r k : ℕ}

/-- Compute the layout field's address, read it, and branch on its word. -/
def code (pc : Fin 5 → Fin p) (head one tmp : Fin r) (target : Bool → Fin p) :
    Fin 5 → Instr w p r k :=
  ![.constant tmp 19 (pc 1), .binary .add tmp tmp tmp (pc 2),
    .binary .add tmp head tmp (pc 3), .readExternal tmp tmp (pc 4),
    .jumpEq tmp one (target true) (target false)]

theorem resize_code (pc : Fin 5 → Fin p) (head one tmp : Fin r) (target : Bool → Fin p)
    (i : Fin 5) :
    (code (w := 5) (k := k) pc head one tmp target i).resize w = code pc head one tmp target i := by
  fin_cases i <;> rfl

/-- Installation of the five instructions at their relocatable labels. -/
def Linked (M : Machine w p r k) (pc : Fin 5 → Fin p) (head one tmp : Fin r)
    (target : Bool → Fin p) : Prop := ∀ i, M.code (pc i) = code pc head one tmp target i

/-- Chronological events on the external memory supplied to the vertex call. -/
def events (mem : Memory w) (head : Word w) : List (Event w) :=
  [.tick, .tick, .tick, .read (head + 38) (mem (head + 38).val), .tick]

theorem cost (mem : Memory w) (head : Word w) :
    (events mem head).length = 5 ∧ countProbes (events mem head) = 1 ∧
      choiceBits (events mem head) = [] := ⟨rfl,rfl,rfl⟩

variable {M : Machine w p r k} {pc : Fin 5 → Fin p} {head one tmp : Fin r} {target : Bool → Fin p}

private theorem step_at (hl : Linked M pc head one tmp target) (i : Fin 5) {c : Config w p r}
    (hc : c.pc = pc i) : M.program.step c = (code pc head one tmp target i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

/-- The physical field selects its designated continuation. The scratch
register receives the read word. Every other register and both kinds of
caller state survive the branch. -/
theorem native (hl : Linked M pc head one tmp target) (mem : Memory w) (c : Config w p r)
    (start : c.pc = pc 0) (hw : 0 < w) (hhead : head ≠ tmp) (hone : one ≠ tmp)
    (unit : c.reg one = 1) (side : Bool)
    (published : mem (c.reg head + 38).val = (side.toNat : Word w)) :
    ∃ d, Prefix M mem c d [] (events mem (c.reg head)) ∧ d.pc = target side ∧
      d.reg tmp = (side.toNat : Word w) ∧ (∀ a, a ≠ tmp → d.reg a = c.reg a) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  let addr := c.reg head + 38
  let a := c.put (pc 1) tmp 19
  let b := a.put (pc 2) tmp 38
  let e := b.put (pc 3) tmp addr
  let f := e.put (pc 4) tmp (mem addr.val)
  let d := {f with pc := target side}
  have s₀ : M.program.step c = .localStep a := step_at hl 0 start
  have dbl : (19 : Word w) + 19 = 38 := (Nat.cast_add (R := Word w) 19 19).symm
  have s₁ : M.program.step a = .localStep b := by
    rw [step_at hl 1 (by rfl)]
    change CallAction.localStep (a.put _ tmp (a.reg tmp + a.reg tmp)) = _
    rw [show a.reg tmp = 19 from Config.put_same .., dbl]
  have s₂ : M.program.step b = .localStep e := by
    rw [step_at hl 2 (by rfl)]
    change CallAction.localStep (b.put _ tmp (b.reg head + b.reg tmp)) = _
    simp [a,b,e,addr,Config.put,Function.update_of_ne hhead]
  have s₃ : M.program.step e = .read addr (fun x ↦ e.put (pc 4) tmp x) := by
    rw [step_at hl 3 (by rfl)]
    change CallAction.read (e.reg tmp) _ = _
    rw [show e.reg tmp = addr from Config.put_same ..]
  have word : f.reg tmp = (side.toNat : Word w) := (Config.put_same ..).trans published
  have oneEq : f.reg one = 1 := by
    simp [f,e,b,a,Config.put,Function.update_of_ne hone,unit]
  have s₄ : M.program.step f = .localStep d := by
    rw [step_at hl 4 (by rfl)]
    change CallAction.localStep {f with pc := if f.reg tmp = f.reg one then _ else _} = _
    rw [word,oneEq]
    cases side with
    | false =>
      have ne : (0 : Word w) ≠ 1 := by
        intro eq
        have val := congrArg Fin.val eq
        have lt : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
        change 0 = 1 % (2^w) at val
        rw [Nat.mod_eq_of_lt lt] at val
        omega
      simp [d, ne]
    | true => simp [d]
  have path : ReadPrefix M mem c (events mem (c.reg head)) d :=
    ReadPrefix.tick s₀ (ReadPrefix.tick s₁ (ReadPrefix.tick s₂
      (ReadPrefix.read addr s₃ (ReadPrefix.tick s₄ (ReadPrefix.nil d)))))
  refine ⟨d, ?_, rfl, word, ?_, rfl, rfl⟩
  · intro fuel bs
    exact ReadPrefix.execute path fuel bs
  · intro j hj
    simp [d,f,e,b,a,Config.put,Function.update_of_ne hj]

end PairSimulation.ShrinkLayoutBranch

end VPVNP
end Computability
end OAI
