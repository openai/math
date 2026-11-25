import OAI.Optimization.LinearProgramming.OracleSpec.WordDialogueDeployment

/-! Compose a finite native subdialogue inside another finite word dispatcher. The
subroutine may rewrite outgoing packets and retain an arbitrary caller continuation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner

open OracleSpec

abbrev WireAction (C : Type) := Word ⊕ (Word × C)
abbrev ViewAction (Y R C : Type) := Y ⊕ (R × C)

def wireView {Y R C : Type} (out : Y → Word) (row : R → Word) : ViewAction Y R C → WireAction C
  | .inl y => .inl (out y)
  | .inr (r,c) => .inr (row r,c)

def routeView {Y R C K : Type} (done : Y → WireAction K) (send : R → Word) (embed : C → K) :
    ViewAction Y R C → WireAction K
  | .inl y => done y
  | .inr (r,c) => .inr (send r,embed c)

def historyWith (past : Transcript) (adapt : Word → Word) (h : Transcript) : Transcript :=
  h.map (fun e => (adapt e.1,e.2)) ++ past

def oracleWith (past : Transcript) (adapt : Word → Word) (o : WordOracle) : WordOracle :=
  fun h w => o (historyWith past adapt h) (adapt w)

private theorem sessionStateBound {I C : Type} {ei : I → Word} {ec : C → Word}
    {f : I ⊕ (Word × C) → WireAction C} {o : WordOracle} {L : ℕ} {s h w h' k}
    (hs : WordDialogue.Session ei ec f o L s h w h' k) : (WordDialogue.stateCode ei ec s).length ≤ L := by
  cases hs with
  | done _ h _ => exact h
  | query _ h _ _ _ => exact h

/-- A subroutine's finite interaction transfers literally. When its terminal action is
reached the next phase runs at the same dispatch boundary. All costs count genuine calls. -/
theorem transferSession {I C Y R J K : Type}
    {ei : I → Word} {ec : C → Word} {ej : J → Word} {ek : K → Word}
    {sub : I ⊕ (Word × C) → WireAction C} {outer : J ⊕ (Word × K) → WireAction K}
    (view : I ⊕ (Word × C) → ViewAction Y R C) (outCode : Y → Word) (rowCode : R → Word)
    (exactWire : ∀ s, wireView outCode rowCode (view s)=sub s)
    (done : Y → WireAction K) (send : R → Word) (embed : C → K) (adapt : Word → Word)
    (adaptation : ∀ a, adapt (rowCode a)=send a)
    (resume : ∀ w c, outer (.inr (w,embed c))=routeView done send embed (view (.inr (w,c))))
    (past : Transcript) (o : WordOracle) (post : Transcript → Prop) (L bound rest : ℕ) (hL : L≤bound)
    (packetBound : ∀ a, (rowCode a).length ≤ L → (send a).length ≤ bound)
    (carryBound : ∀ w c, (WordDialogue.stateCode ei ec (.inr (w,c))).length ≤ L →
      (WordDialogue.stateCode ej ek (.inr (w,embed c))).length ≤ bound)
    {st : I ⊕ (Word × C)} {h final : Transcript} {out answer : Word} {k : ℕ}
    (run : WordDialogue.Session ei ec sub (oracleWith past adapt o) L st h out final k)
    (terminal : ∀ y, outCode y=out → ∀ (s : J ⊕ (Word × K)),
      outer s=done y → (WordDialogue.stateCode ej ek s).length ≤ bound →
      ∃ hist cnt, cnt≤rest ∧ WordDialogue.Session ej ek outer o bound s (historyWith past adapt final) answer hist cnt ∧ post hist)
    (s : J ⊕ (Word × K)) (start : outer s=routeView done send embed (view st))
    (startBound : (WordDialogue.stateCode ej ek s).length ≤ bound) :
    ∃ hist cnt, cnt≤k+rest ∧ WordDialogue.Session ej ek outer o bound s (historyWith past adapt h) answer hist cnt ∧ post hist := by
  induction run generalizing s with
  | @done st h out step _ _ =>
    cases hv : view st with
    | inl y =>
      have hy : outCode y=out := by simpa [wireView,hv,step] using exactWire st
      obtain ⟨hist,cnt,hc,hs,hp⟩ := terminal y hy s (by simpa [hv,routeView] using start) startBound
      exact ⟨hist,cnt,by omega,hs,hp⟩
    | inr a => have bad := exactWire st; rcases a with ⟨r,c⟩; simp [wireView,hv,step] at bad
  | @query st h packet c out final count step _ hp hr next ih =>
    cases hv : view st with
    | inl y => have bad := exactWire st; simp [wireView,hv,step] at bad
    | inr a =>
      obtain ⟨r,c'⟩ := a
      have he : rowCode r=packet ∧ c'=c := by simpa [hv,wireView,step] using exactWire st
      obtain ⟨hpacket,hcarry⟩ := he
      subst packet
      subst c
      let reply := oracleWith past adapt o h (rowCode r)
      obtain ⟨hist,cnt,hc,hs,hok⟩ := ih terminal (.inr (reply,embed c')) (resume reply c')
        (carryBound _ _ (sessionStateBound next))
      have replyEq : o (historyWith past adapt h) (send r)=reply := by simp [reply,oracleWith,adaptation]
      have tail : WordDialogue.Session ej ek outer o bound (.inr (o (historyWith past adapt h) (send r),embed c'))
          ((send r,o (historyWith past adapt h) (send r))::historyWith past adapt h) answer hist cnt := by
        simpa [historyWith,oracleWith,adaptation,reply] using hs
      refine ⟨hist,cnt+1,by omega,WordDialogue.Session.query (by simpa [hv,routeView] using start)
        startBound (packetBound r hp) ?_ tail,hok⟩
      rw [replyEq]
      exact hr.trans hL

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
