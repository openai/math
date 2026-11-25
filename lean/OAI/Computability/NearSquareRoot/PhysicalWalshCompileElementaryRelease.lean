import OAI.Computability.NearSquareRoot.PhysicalWalshCompileElementaryCharge
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileElementaryAgenda
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileLowWalk

/-! # Effective physical prefix-XOR commands for varying Walsh templates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileElementaryRelease
open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode
open CommonRegisters GeneratorSyntax Filter
open PhysicalWalshCompileSwapRulers (Control World regime)
open PhysicalWalshCompileElementaryAgenda (steps agenda)
open ElementaryGate (Bits2)

def direction (b : Bool) : Bits2 → Bits2 :=
  if b then ElementaryIndex.rewire (0 : Fin 2) 1 else ElementaryIndex.rewire (1 : Fin 2) 0

theorem direction_eq {A : ℕ} (i j : Fin A) : direction (decide (i.val<j.val)) = ElementaryIndex.rewire i j := by
  funext v
  by_cases h : i.val<j.val <;> simp [direction,ElementaryIndex.rewire,h]

def world {a : ℕ} (W : ℕ) (i j : Fin (a+1)) (D : ℕ) (s : Shape) : PhysicalWalshCompileSwapRulers.World :=
  ⟨a,W,i,j,D,s⟩

def cut (trim : Bool) (D A : ℕ) (s : Shape) :=
  if trim then SlotSwap.reserve D A s else ElementarySchedule.slotWidth A s

private def instanceOf {a W : ℕ} (stepsOf : World → ℕ)
    (bound : ∀ u, stepsOf u ≤ ElementarySchedule.slotWidth (u.a+1) u.shape) (i j : Fin (a+1)) (ne : i ≠ j) (D : ℕ) (t : XorInput W) :
    PhysicalWalshCompileLowWalk.World (direction (decide (i.val<j.val))) where
  w := t.shape.w
  count := groups W t.shape*PhysicalWalshNode.inner (a+1) t.shape
  steps := stepsOf (world W i j D t.shape)
  P n := ElementarySchedule.pref W i j t.shape n
  G n := ElementarySchedule.gap i j t.shape n
  B n := ElementarySchedule.suff i j t.shape n
  pPos _ := Nat.mul_pos (Nat.zero_lt_one.trans_le (Nat.le_max_left ..)) (Nat.two_pow_pos _)
  gPos _ := Nat.two_pow_pos _
  bPos _ := Nat.mul_pos (Nat.two_pow_pos _) t.shape.suff_pos
  dims n := ElementarySchedule.gate_count W ne t.shape t.positive
    (n.castLE (bound (world W i j D t.shape)))
  row n := t.row ∘ ElementarySweep.address i j t.shape n
  next n k := by
    rw [direction_eq]
    exact congrArg t.row (ElementarySweep.address_step i j ne t.shape
      (n.castLE (bound (world W i j D t.shape))) k)

def Walks (b : Bool) (d C : ℕ) (cmd : Cmd) : Prop :=
  let S (t : PhysicalWalshCompileLowWalk.World (direction b)) :=
    C*(size (PhysicalWalshCompileLowWalk.tickets t)+1)^d+PhysicalWalshCompileLowWalk.volume t
  EffectiveBoundedTask.Runs cmd (fun t => (t.steps+1)*(S t+1)) S
    (fun t => send (PhysicalWalshCompileLowWalk.tickets t,PhysicalWalshCompileLowWalk.rows t 0))
    (fun t => send (PhysicalWalshCompileLowWalk.rows t t.steps))

private theorem fixedWalk (b : Bool) : ∃ d C cmd, Walks b d C cmd := by
  obtain ⟨d,C,c,h⟩ := PhysicalWalshCompileLowWalk.universal (direction b)
  exact ⟨d,C,c,h⟩

/-- A run on the normalized local clock, for the actual slot and orientation. -/
private theorem release {a W D d e f E C J : ℕ} (stepsOf : World → ℕ)
    (bound : ∀ u, stepsOf u ≤ ElementarySchedule.slotWidth (u.a+1) u.shape) (i j : Fin (a+1)) (ne : i ≠ j)
    (header walk : Cmd) (hd : 1 ≤ d) (de : d ≤ E) (fe : f*e+1 ≤ E)
    (hc : ∃ B : ℕ, ∀ s env park,
      Fits env header (pile 0 (send (Header.wire (a+1) s)) park)
        (pile 0 (send (agenda stepsOf (world W i j D s))) park) (B*(Header.scale (a+1) s+1)^d))
    (hs : ∀ s, size (agenda stepsOf (world W i j D s)) ≤ J*(Header.scale (a+1) s+1)^f)
    (hw : Walks (decide (i.val<j.val)) e C walk) :
    let c s := stepsOf (world W i j D s)
    PhysicalWalshCompileXorRoute.Flat (a:=a) (W:=W) (nodeScan a W E (ElementarySweep.prefixExtra (a+1) c))
      (nodeArena a W E) (PhysicalWalshCompileXorSwap.slice c i j) ((KernelEffectiveFamily.leftCmd header).join walk) := by
  intro c
  let tWorld := instanceOf (W:=W) stepsOf bound i j ne D
  let T (t : XorInput W) := nodeScan a W E (ElementarySweep.prefixExtra (a+1) c) t.shape
  let S (t : XorInput W) := nodeArena a W E t.shape
  let N (t : XorInput W) := groups W t.shape*PhysicalWalshNode.inner (a+1) t.shape
  let V (t : XorInput W) := C*(size (agenda stepsOf (world W i j D t.shape))+1)^e+(N t+1)*(t.shape.w+1)
  have dominates (s : Shape) : allowance (a+1) E s ≤ nodeArena a W E s := le_max_left ..
  have prelude := prepare (W:=W) hd de header (fun s => agenda stepsOf (world W i j D s)) hc
  have pre := prelude.mono (t':=T) (s':=S) (fun t => (dominates t.shape).trans (Nat.le_add_right ..))
    (fun t => dominates t.shape)
  have walkRun := EffectiveBoundedTask.Runs.on hw tWorld
  let K := C*(J+1)^e
  have charges (t : XorInput W) : (c t.shape+1)*(V t+1)+1 ≤ (K+3)*(T t+1) ∧ V t+1 ≤ (K+2)*(S t+1) := by
    have rows : N t ≤ count (a+1) t.shape := Nat.mul_le_mul_right _
      (max_le t.shape.pref_pos (Nat.div_le_self ..))
    have ⟨rt,rs⟩ := walker_charge (d:=E) (e:=e) (C:=C) (N:=N t) (S:=V t) t.shape c
      (bound (world W i j D t.shape)) (hs _) rows rfl fe
    exact ⟨rt.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.add_le_add_right (dominates t.shape) _))),
      rs.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (dominates t.shape)))⟩
  have post := walkRun.bound (t':=T) (s':=S) (K+3) (K+2) (fun t => (charges t).1) (fun t => (charges t).2)
  have stages : EffectiveBoundedTask.Runs walk T S
      (fun t => send (agenda stepsOf (world W i j D t.shape), laneFlat (a+1) W t.shape t.row))
      (fun t => send (laneFlat (a+1) W t.shape (PhysicalWalshCompileXorSwap.slice c i j t.shape t.row))) := by
    apply AgendaOps.conform post (fun _ => rfl) (fun _ => rfl) _ (fun _ => rfl)
    intro t
    change send (agenda stepsOf (world W i j D t.shape),
      laneFlat (a+1) W t.shape (t.row ∘ ElementarySweep.address i j t.shape 0)) = _
    rw [show t.row ∘ ElementarySweep.address i j t.shape 0 = t.row from funext fun n => congrArg t.row (ElementarySweep.address_zero i j t.shape n)]
  exact pre.sequence stages

private def emitter (header : Control → Cmd) (w : Bool → Cmd) (k : Control) :=
  (KernelEffectiveFamily.leftCmd (header k)).join (if k.2.2.1 < k.2.2.2.1 then w true else w false)

private theorem effective_emitter (header : Control → Cmd) (w : Bool → Cmd) (h : Effective ltr header) :
    Effective ltr (emitter header w) := by
  apply (KernelEffectiveFamily.effective_left h).join
  have pred : PrimrecPred (fun k : Control => k.2.2.1 < k.2.2.2.1) :=
    Primrec.nat_lt.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact (Computable.cond pred.decide.to_comp (Computable.const (file ltr (w true))) (Computable.const (file ltr (w false)))).of_eq
    (fun k => by by_cases lt : k.2.2.1 < k.2.2.2.1 <;> simp [lt])

/-- The raw compiler emits one header generator followed by one of two fixed
ticket walkers. One polynomial degree and register bound suffice for every
slot, reserve degree, recursive width, and row. -/
theorem compiledFor (stepsOf : World → ℕ) (known : IntegerMultiplication.Staff.Realizes regime stepsOf)
    (bound : ∀ u, stepsOf u ≤ ElementarySchedule.slotWidth (u.a+1) u.shape) : ∃ (R E : ℕ) (c : Control → Cmd),
    Effective ltr c ∧ (∀ k, Within R (c k)) ∧
    ∀ a W (i j : Fin (a+1)), i ≠ j → ∀ D d, E ≤ d →
      PhysicalWalshCompileXorRoute.Flat (a:=a) (W:=W) (nodeScan a W d (ElementarySweep.prefixExtra (a+1) (fun s => stepsOf (world W i j D s))))
        (nodeArena a W d) (PhysicalWalshCompileXorSwap.slice (fun s => stepsOf (world W i j D s)) i j) (c (a+1,W,i.val,j.val,D)) := by
  have generated := PhysicalWalshCompileElementaryAgenda.generated stepsOf known
  obtain ⟨N,d,header,hd,he,hr,hc⟩ := PhysicalWalshCompileSwapRulers.configured generated
  obtain ⟨f,hs⟩ := PhysicalWalshCompileSwapRulers.compact_size generated
  choose exp coef walk hw using fixedWalk
  let E := max d (f*(max (exp false) (exp true))+1)
  obtain ⟨R,rR,hN,hF,hT⟩ := ((eventually_gt_atTop (0:ℕ)).and ((eventually_ge_atTop N).and
    ((RegisterSelect.within_eventually (walk false)).and (RegisterSelect.within_eventually (walk true))))).exists
  refine ⟨R,E,emitter header walk,effective_emitter header walk he,fun k => ?_,?_⟩
  · refine ⟨KernelEffectiveFamily.within_left rR (RegisterSelect.within_mono hN _ (hr k)),?_⟩
    split <;> assumption
  intro a W i j ne D n hn
  obtain ⟨B,hB⟩ := hc a W i j D
  obtain ⟨J,hJ⟩ := hs a W i j D
  let b := decide (i.val<j.val)
  have eqn : (if i.val < j.val then walk true else walk false) = walk b := by by_cases lt : i.val < j.val <;> simp [b,lt]
  have e : exp b ≤ max (exp false) (exp true) := by cases b <;> first | exact le_max_left .. | exact le_max_right ..
  have h₁ : d ≤ n := (le_max_left ..).trans hn
  have h₂ : f*exp b+1 ≤ n := (Nat.succ_le_succ (Nat.mul_le_mul_left f e)).trans ((le_max_right ..).trans hn)
  unfold emitter
  simp only [eqn]
  apply release stepsOf bound i j ne _ _ hd h₁ h₂ _ hJ (hw b)
  refine ⟨B,fun s env park => ?_⟩
  simpa only [Nat.add_zero,world,PhysicalWalshCompileSwapRulers.control,PhysicalWalshCompileSwapRulers.descriptor] using hB s env park

/-- Full-width and fixed-reserve specializations of the generated sweep. -/
theorem compiled (trim : Bool) : ∃ (R E : ℕ) (c : Control → Cmd),
    Effective ltr c ∧ (∀ k, Within R (c k)) ∧
    ∀ a W (i j : Fin (a+1)), i ≠ j → ∀ D d, E ≤ d →
      PhysicalWalshCompileXorRoute.Flat (a:=a) (W:=W) (nodeScan a W d (ElementarySweep.prefixExtra (a+1) (cut trim D (a+1))))
        (nodeArena a W d) (PhysicalWalshCompileXorSwap.slice (cut trim D (a+1)) i j) (c (a+1,W,i.val,j.val,D)) :=
  compiledFor (steps trim) (PhysicalWalshCompileElementaryAgenda.steps_realizes trim)
    (PhysicalWalshCompileElementaryAgenda.steps_le trim)

end PhysicalWalshCompileElementaryRelease

end NearSquareRoot
end Computability
end OAI
