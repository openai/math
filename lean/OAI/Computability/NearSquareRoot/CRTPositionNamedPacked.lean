import OAI.Computability.NearSquareRoot.CRTControlledEffectiveCross
import OAI.Computability.NearSquareRoot.CRTControlledPrefixCommand
import OAI.Computability.NearSquareRoot.CRTPositionOpcodeCall

/-! # A single rectangular command template for the packed position opcode

The residue fit test uses only the input rulers. A fitting pass executes the
guarded XOR on the three low chunks. The high remainder is carried through
each invocation by the fixed prefix traversal.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication Code Strip Adic Loom Packed Staff NamedPacked Effective
open PositionPreparation

noncomputable section

private theorem crossProgram {X : Type} {R : Regime X} {l : X → ℕ}
    (N G r k : X → ℕ) (read : (x : X) → Fin (N x) → Option (Fin (N x)))
    (hg : ∀ x, 0 < G x) (hn : Realizes R N) (hG : Realizes R G) (hr : Realizes R r)
    (tab : R.Has fun x => List.ofFn fun j => tally (((read x j).map Fin.val).getD (N x)))
    (hnk : ∀ x, N x ≤ k x) (guard : ∀ x, guardWidth (k x) ≤ G x)
    {U : X → Type} (u : (x : X) → Series (U x)) (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → Block 2 (crossWidth (N x)) → U x → Bead) :
    let flat x := line 2 (crossWidth (N x))
    Program rectContract k R (fun x => (flat x).count) l (together R.header (cloth flat u f))
      (cloth flat u fun x a => f x (crossResidueMask (r := r x) (hg x) (read x) a)) := by
  let flat x := line 2 (crossWidth (N x))
  have stat := terminal (p:=2) (by decide) (fun x => crossWidth (N x)) ((hn.plus hn).plus hn)
  have live := cloth_size flat u stat f z
  obtain ⟨tag,ready,tagged⟩ := hn.below (hr.plus hG)
  have both := (Rip.header (l:=l) stat.1 ready).left live
  have prep := both.split.1.twice both.again
  let Y := {x : X // tag x = false}
  let input := together R.header (cloth flat u f)
  let output := cloth flat u fun x a => f x (crossResidueMask (r := r x) (hg x) (read x) a)
  have fit (y : Y) : r y.val + G y.val ≤ N y.val := Nat.le_of_not_gt fun h => by
    have ht := (tagged y.val).1 h
    rw [y.property] at ht
    contradiction
  obtain ⟨yes,hy⟩ := crossFitTemplate (R := R.pull (Subtype.val : Y → X)) (l := l ∘ Subtype.val)
    (N ∘ Subtype.val) (G ∘ Subtype.val) (r ∘ Subtype.val) (fun x => read x) (fun x => hg x) fit
    (Task.BT.map hn _) (Task.BT.map hG _) (Task.BT.map hr _) (Task.BT.map tab _)
    (fun y => crossSparse (hg _) (fit y) (hnk _) (guard _)) (fun x => u x) (fun x => z x) (fun x => f x)
  obtain ⟨no,he⟩ := Program.ofRip (rect := rectContract) (width := k) both.split.2
  obtain ⟨pre,decode⟩ := namedBranch (u := input) (v := output) tag prep
  refine ⟨.branch pre yes no,fun c ρ hρ hc => decode (Spindle.modes k (τ:=ρ)) _ _ ?_ ?_⟩
  · apply (hy c ρ hρ hc).raise
    intro y
    have fits := crossFit (hg y.val) (fit y)
    have hnk' := hnk y.val
    have le : crossExtent (N y.val) (G y.val) (r y.val) ≤ k y.val := by unfold crossExtent; omega
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.succ_le_succ le) hρ
  · let nofit := (Subtype.val : {x : X // tag x = true} → X)
    have h := (he c ρ hρ hc).on nofit
    convert h using 1
    funext x
    change stripe _ (fun a => strip _ (f x.val (crossResidueMask (r := r x.val) (hg x.val) (read x.val) a))) = _
    simp only [crossResidueMask,dite_eq_right (Nat.not_le_of_gt ((tagged x.val).2 x.property))]
    rfl

private def prefixFrame (H : Type) [Codec H] : Effective.Frame where
  apply := PrefixCommand.command H
  effective := PrefixCommand.command_effective H
  within := PrefixCommand.command_within H

open private posGuard from OAI.Computability.NearSquareRoot.CRTPositionPackedDispatch

/-- The same syntax handles every native width, residue, legal selector table
and record array. An exponent is supplied only when instantiating the rectangle. -/
theorem packedProgram :
    Program rectContract Call.k (Call.regime packed) (fun x => (line 2 x.k).count) Call.width
      Call.input Call.output := by
  let X := Call packed
  let k : X → ℕ := Call.k
  let R := Call.regime packed
  let q : X → Tally × List Tally := Call.operand
  let l : X → ℕ := Call.width
  let u (x : X) := Series.natural x.width
  let head (x : X) := (tally x.k,packed x.operand)
  let p (x : X) := k x % 3
  let n (x : X) := crossWidth (k x / 3)
  let flat x := line 2 (k x)
  let move (x : X) := crossResidueMask (N := k x / 3) (r := (q x).1.length) (posGuard (k x)) (packedRead (q x).2)
  let f (x : X) := x.data
  let view x := prefixView (chunkFactor (k x))
  let Y := (x : X) × Block 2 (p x)
  let pr : Y → X := Sigma.fst
  let fs (v : Y) (a : Block 2 (n v.1)) := f v.1 ((view v.1).cast (v.2,a))
  have key (x : X) : R.header x = send (head x) := rfl
  have hk : Realizes R k := Call.widthHas
  have payload : R.Has q := packedPayload_has (Call.opcodeHas (wrap:=packed))
  have hN := third_realizes hk
  have hn : Realizes R n := (hN.plus hN).plus hN
  have hp : Realizes R p := thirdRemainder_realizes hk
  have hG := guardWidth_realizes hk
  have hr : Realizes R (fun x => (q x).1.length) := by
    have hd := payload.ez Easy.fst
    change R.Has (fun x => tally (q x).1.length)
    simpa only [recover_tally] using hd
  have ht : R.Has (fun x => List.ofFn (fun j : Fin (k x/3) =>
      tally (((packedRead (q x).2 j).map Fin.val).getD (k x/3)))) := by
    have valid (x : X) : WellFormed (k x) (guardWidth (k x)) (packed (q x)) := x.legal
    simpa only [packedRead_table (valid _)] using (payload.ez Easy.snd)
  have hu (x : X) : (u x).count ≤ l x := by simp [u,l]
  have inner := crossProgram (R := R.pull pr) (l := l ∘ pr)
    (fun y => k (pr y)/3) (fun y => guardWidth (k (pr y))) (fun y => (q (pr y)).1.length) (k ∘ pr)
    (fun y => packedRead (q (pr y)).2) (fun y => posGuard _) (Task.BT.map hN pr)
    (Task.BT.map hG pr) (Task.BT.map hr pr) (Task.BT.map ht pr) (fun y => Nat.div_le_self ..)
    (fun _ => le_rfl) (fun y => u (pr y)) (fun y => hu (pr y)) fs
  obtain ⟨low,run⟩ := inner
  have hh : R.Has head := Regime.self
  have dims := (hp.pair hn).pair hh
  have stat := terminal (p:=2) (by decide) k hk
  have prep := (Rip.header (l:=l) stat.1 dims).left (cloth_size flat u stat f hu)
  obtain ⟨front,pre⟩ := Program.ofRip (rect:=rectContract) (width:=k) prep
  have same (x : X) (a : Block 2 (k x)) : nativeOp (k x) (guardWidth (k x)) (packed (q x)) a =
      underPrefix (chunkFactor (k x)) (move x) a :=
    prefixBit_injective _ ((nativeOp_bits ..).trans (packedPass_bits (q x) x.legal a).symm)
  refine ⟨.next front (.frame (prefixFrame (Tally × Op)) low),fun c ρ hρ hc => ?_⟩
  have step := PrefixCommand.binaryPrefixPassFor (r := R) (width := l)
    (rate := Spindle.modes k (τ:=ρ)) p n k (fun x => chunkFactor (k x)) head key hp hn
    (Spindle.belly k hρ) u hu move f (run c ρ hρ hc)
  have out := (pre c ρ hρ hc).next step
  convert out using 1 <;> try rfl
  funext x
  change stripe _ (fun a => strip _ (x.data (nativeOp (k x) (guardWidth (k x)) (packed (q x)) a))) = _
  simp only [same]
  rfl

theorem packedOpcodeTemplate :
    ∃ t : Effective.Template, ∀ c ρ, 1/2 < ρ → rectContract c ρ → OpAt (t.eval c) ρ packed := by
  obtain ⟨t,run⟩ := packedProgram
  exact ⟨t,fun c ρ hρ => run c ρ (by linarith)⟩

end
end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
