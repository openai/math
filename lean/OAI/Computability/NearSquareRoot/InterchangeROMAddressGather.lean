import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineClock

/-! # Executing a signed gather instruction from its literal and live header -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress.Affine

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom Space

def scanPrice (M C j classes : ℕ) (descriptor : Template) (h : Header) (N : ℕ)
    (source target : Tree) :=
  M*(classes+1)*(source.count+target.count+1 + (N+1)*(C*(size (descriptor,h)+1)^j))

/-- The fixed affine core and its computed literal execute the gather on the
actual logical payload. The prices depend on the class count, physical row
volume, and a uniform polynomial in the header. -/
theorem gather_command : ∃ M C j : ℕ, ∀ {J : Type} [DecidableEq J] {n b f : ℕ} [NeZero b]
    (ord : J ≃ Fin n) (P G S : Tape) (_ : solid P) (_ : solid G) (_ : solid S) (_ : 2 ≤ b)
    (target control : Spot J) (legal : Lag.early (ranking ord) control target)
    (a : Pinpoint b) (v : Keys P G S J (Block b f) → Tree) env deck base, DeckCap base deck →
    let physical := arrays ord (line b f) P G S
    let h := header f P G S
    let rows := InterchangeAffineMask.pinRows a
    let literal := spec ord b control target rows.1 rows.2
    let source := stripe physical v
    let dest := stripe physical (v ∘ (reflect ord (.gather target control a) legal P G S f).symm)
    let cost := scanPrice M C j (InterchangeAffineMask.colors rows.1 rows.2).length
      literal h physical.count source dest
    BoundedFits env (compile core literal) (pile 0 (.fork (send h) source) deck)
      (pile 0 dest deck) cost (base+cost) cost := by
  obtain ⟨M,C,j,d,ok⟩ := run_native
  refine ⟨M,C,j,?_⟩
  intro J dJ n b f nz ord P G S goodP goodG goodS hb dst ctrl legal a v env deck base hr
  let e := twoStops (p:=b) (j:=f) (P:=P) (G:=G) (B:=S) ord ctrl dst legal
  let native := arrays ord (line b f) P G S
  let z := gather ord P G S goodP goodG goodS hb ctrl dst legal a v
  have fromRows := axisRows_source e a v
  have toRows := axisRows_target e a v
  change z.rows.source.map Prod.snd = native.tab v at fromRows
  change z.rows.target.map Prod.snd = native.tab (v ∘ (reflect ord (.gather dst ctrl a) legal P G S f).symm) at toRows
  have run := ok native.count z (gather_priced ord P G S goodP goodG goodS hb ctrl dst legal a v d)
    env deck base hr
  let ab := InterchangeAffineMask.pinRows a
  have loc : z.static = spec ord b ctrl dst ab.1 ab.2 := rfl
  have hdr : z.layout = header f P G S := rfl
  have colors : z.rows.colors = InterchangeAffineMask.colors ab.1 ab.2 := rfl
  dsimp only
  simp only [input,InterchangeROMColors.Labeled.answer,work,recordVolume,fromRows,toRows,loc,hdr,colors] at run
  simpa only [scanPrice,stripe_eq,size,Nat.mul_assoc] using run

end InterchangeROMAddress.Affine

end NearSquareRoot
end Computability
end OAI
