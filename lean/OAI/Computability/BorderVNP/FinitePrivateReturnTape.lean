import OAI.Computability.BorderVNP.FinitePrivateReplay

/-! # Canonical choice strings for finite-field private returns

On raw input, a physical private call accepts precisely the tape obtained by
prefixing the original native choices with the code of their actual return
class. Thus guessing the return class preserves every native path once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldSelect

open TeamPrivateTape TeamPrivateValue
variable {Q Γ : Type} {F : Type*} {m g : ℕ}

/-- Observe the field output of a native finite-alphabet routine on exactly its
consumed choices. The halt uses one clock tick. -/
def nativeReturn (P : TapeTable Q Γ m) (blank : Γ) (w : Return Q Γ F m) :
    ℕ → Q → (Fin m → SymbolTape Γ) → List Bool → Option F
  | 0, _, _, _ => none
  | t+1, q, ts, bits => match P q (fun i => (ts i).head) with
    | .halt ok sign => if ok && bits.isEmpty then some (w q (fun i => (ts i).head) sign) else none
    | .one c => nativeReturn P blank w t c.next (c.apply blank ts) bits
    | .two l h => match bits with
      | [] => none
      | b :: tail => let c := if b then h else l; nativeReturn P blank w t c.next (c.apply blank ts) tail

private theorem observe_class [DecidableEq F] (a : Alphabet Γ g) (P : TapeTable Q Γ m)
    (w : Return Q Γ F m) (v : F) (f : ℕ) (q : Q) (ts : Fin m → SymbolTape Γ) (bs : List Bool) :
    observe (trackTable a (selectTable P w v)) f q (tracks a ts) bs =
      (if nativeReturn P a.blank w f q ts bs = some v then some false else none) := by
  classical
  induction f generalizing q ts bs with
  | zero => simp [observe,TeamPrivateCall.evaluate,nativeReturn]
  | succ f ih =>
    have heads_eq : (fun i : Fin m => a.read (fun j => heads (tracks a ts) (finProdFinEquiv (i,j)))) =
        (fun i => (ts i).head) := by
      funext i
      simpa only [heads,tracks,Equiv.symm_apply_apply,SymbolTape.track] using a.read_bits (ts i).head
    cases op : P q (fun i => (ts i).head) with
    | halt ok sign =>
      cases ok <;> cases bs <;> by_cases test : w q (fun i => (ts i).head) sign = v <;>
        simp [observe,TeamPrivateCall.evaluate,nativeReturn,trackTable,heads_eq,selectTable,op,test]
    | one c =>
      simp only [observe,TeamPrivateCall.evaluate,nativeReturn,trackTable,heads_eq,selectTable,op,tracks_apply]
      change observe _ f c.next (tracks a (c.apply a.blank ts)) bs = _
      rw [ih]
    | two l h =>
      cases bs with
      | nil => simp [observe,TeamPrivateCall.evaluate,nativeReturn,trackTable,heads_eq,selectTable,op]
      | cons b bs =>
        cases b
        · simp only [observe,TeamPrivateCall.evaluate,nativeReturn,trackTable,heads_eq,selectTable,op,
            Bool.false_eq_true,ite_false,tracks_apply]
          change observe _ f l.next (tracks a (l.apply a.blank ts)) bs = _
          rw [ih]
        · simp only [observe,TeamPrivateCall.evaluate,nativeReturn,trackTable,heads_eq,selectTable,op,
            ite_true,tracks_apply]
          change observe _ f h.next (tracks a (h.apply a.blank ts)) bs = _
          rw [ih]

variable [Field F] [Fintype F]

/-- The exact physical choice prefix for one field return. -/
noncomputable def returnTape (z : F) (bits : List Bool) : List Bool :=
  choiceTape (Fintype.card F - ((Fintype.equivFin F z).val + 1)) bits

/-- The real loader, output-class selector, finite-alphabet tape machine and cleanup
have exactly the native accepting paths. Only the prefix determined by the genuine
return element can pass, even when that element is zero. -/
theorem mem_call_iff (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (P : TapeTable Q Γ m)
    (w : Return Q Γ F m) (start : Q) (raw : List Bool) (f ticks : ℕ)
    (hs : TapeStops P a.blank f start (input a.blank digit i raw))
    (ht : TeamPrivateInput.steps g raw + budget f (tracks a (input a.blank digit i raw)) + Fintype.card F ≤ ticks)
    (tape : List Bool) (z : F) :
    (tape,z) ∈ FieldReplay.leaves (call a digit i P w start) callOutput ticks (.select (Fin.last _))
      (TeamPrivateInput.initial raw) ↔ ∃ bits,
      tape = returnTape z bits ∧ nativeReturn P a.blank w f start (input a.blank digit i raw) bits = some z := by
  classical
  let cls := (Fintype.equivFin F).symm
  let weight := fun (j : Fin (Fintype.card F)) (u : TeamPrivateCompiler.Control Q m g) =>
    if TeamPrivateCompiler.negative u then -(cls j) else cls j
  let ts := input a.blank digit i raw
  have body (j : Fin (Fintype.card F)) (skip : ℕ) (hj : j.val + skip + 1 = Fintype.card F) (bs : List Bool) :
      (bs,z) ∈ FieldReplay.leaves (classCode a digit i P w start j) (weight j) (ticks-(skip+1))
        (.load .start) (TeamPrivateInput.initial raw) ↔
      nativeReturn P a.blank w f start ts bs = some (cls j) ∧ cls j = z := by
    have hstop := (stops_iff P a.blank w f start ts (cls j)).mpr hs
    rw [classCode, private_leaf_iff a digit i _ start _ raw f _ hstop (by omega),observe_class]
    by_cases test : nativeReturn P a.blank w f start ts bs = some (cls j)
    · simp [weight,cls,TeamPrivateCompiler.negative,ts] at test ⊢
    · simp [weight,cls,TeamPrivateCompiler.negative,ts] at test ⊢
  change (tape,z) ∈ FieldReplay.leaves (code (classCode a digit i P w start) (.load .start)) (output weight) ticks
    (.select (Fin.last (Fintype.card F))) (TeamPrivateInput.initial raw) ↔ _
  refine (mem_selection_iff (classCode a digit i P w start) weight (.load .start) (TeamPrivateInput.initial raw) z
    (Fintype.card F) le_rfl ticks tape).trans ?_
  constructor
  · rintro ⟨j,skip,hj,bs,he,hm⟩
    obtain ⟨hv,hz⟩ := (body j skip hj bs).mp hm
    have heq : Fintype.equivFin F z = j := by rw [← hz]; exact (Fintype.equivFin F).apply_symm_apply j
    refine ⟨bs,?_,by simpa only [← hz] using hv⟩
    rw [he,returnTape,heq,show Fintype.card F - (j.val+1) = skip by omega]
  · rintro ⟨bs,he,hv⟩
    let j := Fintype.equivFin F z
    let skip := Fintype.card F - (j.val+1)
    have hj : j.val + skip + 1 = Fintype.card F := by have := j.isLt; dsimp [skip]; omega
    have hz : cls j = z := (Fintype.equivFin F).symm_apply_apply z
    exact ⟨j,skip,hj,bs,he,(body j skip hj bs).mpr ⟨by simpa only [hz] using hv,hz⟩⟩

end FieldSelect

end BorderVNP
end Computability
end OAI
