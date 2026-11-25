import OAI.Computability.NearSquareRoot.PhysicalWalshParamHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshParamLiterals
import OAI.Computability.NearSquareRoot.PhysicalWalshPieceHeaders

/-! # Effective source family for selected-Walsh piece headers

One interpreter reads both template parameters and the compact width rulers.
Its program and polynomial exponent are uniform. Specialization prepends the
parameter pair as a computably emitted program literal.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Carry Staff Strip PhysicalWalshNode CommonRegisters GeneratorSyntax

variable {I : Type} {r : Regime I} {a b k s w j t : I → ℕ}

private theorem digitLen (ha : Realizes r a) (base : ∀ i, 1 < a i) (hs : Realizes r s) :
    Realizes r (fun i => (walshPieceDigits (a i) (s i)).length) := by
  have half := hs.dividing (Realizes.fix 2)
  have h := (Realizes.fix 0).select ((ParamHeader.depth_realizes ha base hs).plus (Realizes.fix 1))
    (half.below (Realizes.fix 1))
  convert h using 1
  funext i
  by_cases zero : s i / 2 = 0
  · simp [walshPieceDigits, zero]
  · rw [walshPieceDigits,Nat.length_digits _ _ (base i) zero]
    simp [WalshPadding.depth,show ¬s i/2 < 1 by omega]

private theorem digitAt (ha : Realizes r a) (base : ∀ i, 1 < a i) (hs : Realizes r s)
    (hj : Realizes r j) : Realizes r (fun i => digit (a i) (s i) (j i)) := by
  let radix := Figure.of_spoken ha
  have value := (((Figure.of_spoken (hs.dividing (Realizes.fix 2))).quotients
    (radix.repeated hj)).modded radix)
  apply value.pay
  exact (diameter a ha).mono fun i => (Nat.mod_lt _ (by have := base i; omega : 0<a i)).le

private theorem jointHeader (ha : Realizes r a) (base : ∀ i, 1 < a i)
    (hb : Realizes r b) (branch : ∀ i, 0 < b i) (hk : Realizes r k)
    (hs : Realizes r s) (hw : Realizes r (fun i => w i+1))
    (hj : Realizes r j) (ht : Realizes r t) (fits : ∀ i, (a i)^(j i) ≤ s i / 2) :
    r.Has (fun i => Header.wire (a i) (shape (a i) (b i) (branch i) (k i) (s i) (w i) (j i) (t i))) := by
  have pow : Realizes r (fun i => a i^(j i)) := ((Figure.of_spoken ha).repeated hj).pay
    ((diameter s hs).mono (fun i => (fits i).trans (Nat.div_le_self ..)))
  have bits : Realizes r (fun i => grow (a i) (j i)) := (Realizes.fix 2).times pow
  have off : Realizes r (fun i => offset (a i) (s i) (j i) (t i)) :=
    ((Realizes.fix 2).times ((hs.dividing (Realizes.fix 2)).rem pow)).plus (ht.times bits)
  have pref := (ParamHeader.paddedRows_figure ha base hb hk hs).multiplied
    ((Figure.natural 2).repeated off)
  have suff := (Figure.natural 2).repeated ((hs.minused off).minused bits)
  exact (Regime.Has.pair hj (Regime.Has.pair bits hw)).pair ((Header.toBinary pref).pair (Header.toBinary suff))

/-- Tabulate every header on the actual run-time base and branching factor. -/
theorem jointHeaders (ha : Realizes r a) (base : ∀ i, 1 < a i)
    (hb : Realizes r b) (branch : ∀ i, 0 < b i) (hk : Realizes r k)
    (hs : Realizes r s) (hw : Realizes r (fun i => w i+1)) :
    r.Has (fun i => (schedule (a i) (b i) (branch i) (k i) (s i) (w i)).map (Header.wire (a i))) := by
  let len (i : I) := (walshPieceDigits (a i) (s i)).length
  let n (u : Across len) := digit (a u.1) (s u.1) u.2.val
  have H : Realizes r len := digitLen ha base hs
  have sj := landing len H s hs
  have aj := landing len H a ha
  have jj := floor_ len H
  have D : Realizes (signal len H) n := digitAt aj (fun i => base i.1) sj jj
  have term : (signal n D).Has (fun z : Across n => Header.wire (a z.1.1)
      (shape (a z.1.1) (b z.1.1) (branch z.1.1) (k z.1.1) (s z.1.1) (w z.1.1) z.1.2.val z.2.val)) :=
    jointHeader (w := fun z : Across n => w z.1.1) (landing n D _ aj) (fun z => base z.1.1)
      (landing n D _ (landing len H b hb)) (fun z => branch z.1.1)
      (landing n D _ (landing len H k hk)) (landing n D _ sj)
      (landing n D _ (landing len H _ hw)) (landing n D _ jj) (floor_ n D)
      (fun z => (Nat.lt_digits_length_iff (base z.1.1) (s z.1.1 / 2)).mp z.1.2.isLt)
  let wire (u : Across len) (t : Fin (n u)) := Header.wire (a u.1)
    (shape (a u.1) (b u.1) (branch u.1) (k u.1) (s u.1) (w u.1) u.2.val t.val)
  have both := (harvest len H (fun i j => List.ofFn (wire ⟨i,j⟩)) (harvest n D wire term)).ez Easy.flatten
  simpa only [Function.comp_def,schedule,List.map_flatten,List.map_ofFn,len,n,wire] using both

/-- Only valid template choices are needed by the joint interpreter. -/
private abbrev Instance := {p : ℕ×ℕ // 1<p.1 ∧ 0<p.2} × (ℕ×ℕ×ℕ)

private def jointInput : Regime Instance where
  scale x := x.1.val.1+x.1.val.2+x.2.1+x.2.2.1+x.2.2.2
  header x := .fork (ParamLiterals.literal x.1.val.1 x.1.val.2) (scheduleInput.header x.2)
  gauge := by
    refine ⟨1,12,fun x => ?_⟩
    change size ((tally x.1.val.1,tally x.1.val.2),((tally x.2.1,tally x.2.2.1),tally (x.2.2.2+1))) ≤ _
    simp only [size_prod,size_tally,tally_length,pow_one]
    omega

private def native (A W : ℕ) (hW : 0<W) (p : ℕ×ℕ×ℕ) :=
  (schedule A W hW p.1 p.2.1 p.2.2).map (Header.wire A)

private theorem jointTask : ∃ d C : ℕ,
    let t (x : Instance) := C*(jointInput.scale x + 1)^d
    Space.BoundedTask t t jointInput.header (fun x => send (native x.1.val.1 x.1.val.2 x.1.property.2 x.2)) := by
  have given : jointInput.Has (fun x => ((tally x.1.val.1,tally x.1.val.2),
      ((tally x.2.1,tally x.2.2.1),tally (x.2.2.2+1)))) := Regime.self
  have ha : Realizes jointInput (fun x => x.1.val.1) := given.ez (Easy.fst.compose Easy.fst)
  have hb : Realizes jointInput (fun x => x.1.val.2) := given.ez (Easy.fst.compose Easy.snd)
  have tail := given.ez Easy.snd
  have hk : Realizes jointInput (fun x => x.2.1) := tail.ez (Easy.fst.compose Easy.fst)
  have hs : Realizes jointInput (fun x => x.2.2.1) := tail.ez (Easy.fst.compose Easy.snd)
  have hw : Realizes jointInput (fun x => x.2.2.2+1) := tail.ez Easy.snd
  obtain ⟨b',hb',task⟩ := jointHeaders (w := fun x : Instance => x.2.2.2)
    ha (fun x => x.1.property.1) hb (fun x => x.1.property.2) hk hs hw
  obtain ⟨d,C,bound⟩ := jointInput.gauge.add hb'
  refine ⟨d,C,(Space.BoundedTask.of_time task).mono (fun x => ?_) (fun x => bound x)⟩
  exact (Nat.le_add_left (b' x) (jointInput.header x).count).trans (bound x)

/-- The native agenda program is effectively emitted from the two template
parameters. One exponent and one register ceiling serve all choices. -/
theorem effectiveHeaders :
    ∃ (cmd : ℕ×ℕ → Cmd) (R d : ℕ), Effective ltr cmd ∧ 0<R ∧
      (∀ p, Within R (cmd p)) ∧ ∀ A W (_hA : 1 < A) (hW : 0 < W),
        let t (z : ℕ×ℕ×ℕ) := (z.1+z.2.1+z.2.2+1)^d
        EffectiveBoundedTask.Runs (cmd (A,W)) t t
          (fun z => send ((tally z.1,tally z.2.1),tally (z.2.2+1)))
          (fun z => send ((schedule A W hW z.1 z.2.1 z.2.2).map (Header.wire A))) := by
  obtain ⟨d,C,core,F,H⟩ := jointTask
  have all : EffectiveBoundedTask.Runs core (fun x : Instance => C*(jointInput.scale x+1)^d)
      (fun x => C*(jointInput.scale x+1)^d) jointInput.header
      (fun x => send (native x.1.val.1 x.1.val.2 x.1.property.2 x.2)) := ⟨F,H⟩
  obtain ⟨R,Rpos,Rok⟩ := ((Filter.eventually_gt_atTop (0:ℕ)).and (RegisterSelect.within_eventually core)).exists
  refine ⟨fun p => ParamLiterals.command p.1 p.2 core,R,d+1,ParamLiterals.effective core,Rpos,
    fun p => ParamLiterals.within Rpos Rok _ _,?_⟩
  intro A W hA hW t
  let src := scheduleInput.header
  let vol (z : ℕ×ℕ×ℕ) := z.1+z.2.1+z.2.2+1
  let row (z : ℕ×ℕ×ℕ) : Instance := (⟨(A,W),hA,hW⟩,z)
  let work z := C*(jointInput.scale (row z)+1)^d
  let tall z := work z + (src z).count
  have coreRun : EffectiveBoundedTask.Runs core tall tall (fun z => .fork (ParamLiterals.literal A W) (src z))
      (fun z => send (native A W hW z)) :=
    (all.on row).mono (fun z => Nat.le_add_right (work z) _) (fun z => Nat.le_add_right (work z) _)
  have emitted := ParamLiterals.runs A W coreRun (fun z => Nat.le_add_left (src z).count _)
  let cap := C*(A+W+1)^d+10
  have charge (z : ℕ×ℕ×ℕ) : tall z + 1 ≤ cap*(t z+1) := by
    have hv : 1 ≤ vol z := Nat.succ_pos _
    have hp : vol z ≤ vol z^(d+1) := by
      rw [pow_succ]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos hv)
    have hq : vol z^d ≤ vol z^(d+1) := Nat.pow_le_pow_right hv (Nat.le_succ d)
    have inc : jointInput.scale (row z)+1 ≤ (A+W+1)*vol z := by
      dsimp only [jointInput,row]
      have := Nat.le_mul_of_pos_right (A+W) hv
      rw [Nat.succ_mul]; dsimp only [vol] at *; omega
    have cost : work z ≤ C*(A+W+1)^d * t z := by
      apply (Nat.mul_le_mul_left C (Nat.pow_le_pow_left inc d)).trans
      rw [mul_pow,Nat.mul_assoc]
      exact Nat.mul_le_mul_left C (Nat.mul_le_mul_left _ hq)
    have input : (src z).count + 1 ≤ 9*t z := by
      change size ((tally z.1,tally z.2.1),tally (z.2.2+1))+1 ≤ _
      simp only [size_prod,size_tally,tally_length]
      change vol z ≤ t z at hp
      dsimp only [vol] at hp
      omega
    dsimp only [cap,tall]
    rw [Nat.add_mul,Nat.mul_add]
    omega
  exact emitted.bound cap cap charge charge

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
