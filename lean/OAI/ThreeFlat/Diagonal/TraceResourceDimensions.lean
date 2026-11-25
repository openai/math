import OAI.ThreeFlat.Diagonal.TraceTerminalEdges

namespace OAI
/-! # The public number of terminal factors of the selected physical plan -/
namespace ThreeFlat.Diagonal.PhysicalStage.Program
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

/-- Public terminal factor count without an extra outgoing-edge dimension. -/
def finalSites : {s : ℕ} → Program F s → ℕ → ℕ → ℕ
  | _,.done _,rem,v => v*2^rem
  | _,.shrink s _ _ _ tail,rem,v => tail.finalSites rem (v*2^(CompressorPacking.tagBits (2^s)))
  | _,.refresh s _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail,rem,v => tail.finalSites rem (v*2^s)

private theorem cast_sites {d l l' n : ℕ} (e : l=l') (A : State d l) (R : Run F (e ▸ A : State d l'))
    (fixed : ∀ h,Fintype.card (R.terminalLayer h).state.Site=n) :
    ∀ h,Fintype.card ((recast e A R).terminalLayer h).state.Site=n := by cases e;exact fixed

private theorem root_card_after_degree_cast {d l D D' L n : ℕ} {A : State d l} (e : D=D') (R : Move F A D L)
    (all : ∀j,Fintype.card (R.next j).Base=n) : ∀j,Fintype.card ((recastMove e R).next j).Base=n := by
  cases e;exact all

private theorem step_sites {d l D L : ℕ} {A : State d l}
    (M : Move F A D L) (next : ∀ j, Run F (M.next j))
    (h : (Run.step M next).plan.History) :
    Fintype.card ((Run.step M next).terminalLayer h).state.Site =
      Fintype.card ((next h.1).terminalLayer (Run.tailHistory M next h)).state.Site := rfl

set_option maxHeartbeats 850000 in
theorem finalSites_eq {s : ℕ} (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem)) :
    ∀ h,Fintype.card ((P.run rem X).terminalLayer h).state.Site=P.finalSites rem (Fintype.card X.Base) := by
  induction P with
  | done s =>
    intro h
    change Fintype.card X.Site=_
    rw [←Fintype.card_congr X.chart,Fintype.card_prod]
    simp [finalSites,Program.charge,Computability.VPVNP.Compression.BitWord]
  | shrink s t G small tail ih =>
    let b:=tail.charge+rem
    let e:=Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+b):=e ▸ X
    let M:=shrinkBinary G s (2^t) b (Nat.two_pow_pos _) (by exact_mod_cast small) B
    let nxt:=fun j=>tail.run rem (M.next j)
    apply cast_sites e X (.step M nxt)
    intro h
    have size:=shrinkBinary_next_base G s (2^t) b (Nat.two_pow_pos _) (by exact_mod_cast small) B h.1
    refine (step_sites M nxt h).trans ?_
    calc _ = tail.finalSites rem (Fintype.card (M.next h.1).Base) := ih (M.next h.1) (Run.tailHistory M nxt h)
         _ = _ := by rw [size,baseCast e X];rfl
  | refresh s t h pad c γ C G hm hh sym rows zero conn deg tail ih =>
    let b:=tail.charge+rem
    let e:=Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+b):=e ▸ X
    let R:=refreshBinary G B hm hh sym rows zero conn
    let M:=recastMove deg R
    let nxt:=fun j=>tail.run rem (M.next j)
    apply cast_sites e X (.step M nxt)
    intro hist
    have size:=root_card_after_degree_cast deg R (refreshBinary_next_base G B hm hh sym rows zero conn) hist.1
    refine (step_sites M nxt hist).trans ?_
    calc _ = tail.finalSites rem (Fintype.card (M.next hist.1).Base) := ih (M.next hist.1) (Run.tailHistory M nxt hist)
         _ = _ := by rw [size,baseCast e X];rfl

theorem finalSites_card {s : ℕ} (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    (h : (P.run rem X).plan.History) :
    Fintype.card ((P.run rem X).plan.finish h).Site=P.finalSites rem (Fintype.card X.Base) := by
  rw [←(P.run rem X).terminalLayer_shape h]
  exact finalSites_eq P rem X h

theorem finalEdges_sites {s : ℕ} (P : Program F s) (rem v : ℕ) :
    P.finalEdges rem v=2^P.terminalExponent*P.finalSites rem v := by
  induction P generalizing v with
  | done s => simp only [finalEdges,terminalExponent,finalSites];ring
  | shrink _ _ _ _ tail ih => exact ih _
  | refresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail ih => exact ih _

theorem finalSites_le {s : ℕ} (P : Program F s) (rem v : ℕ) :
    P.finalSites rem v≤v*2^(P.charge+rem) := by
  have h:=P.finalEdges_le rem v
  rw [finalEdges_sites] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.two_pow_pos _)

end
end ThreeFlat.Diagonal.PhysicalStage.Program

end OAI
