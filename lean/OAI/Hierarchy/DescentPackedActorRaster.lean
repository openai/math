import OAI.Hierarchy.DescentPackedCensusRAM

namespace OAI
/-! # Occupancy of a physical actor independently of its load and port list -/

namespace Hierarchy.DescentActorRaster
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {U V : Type} [Fintype U] [DecidableEq V] {k a t b M H J w : ℕ}
abbrev Block (k : ℕ) := Fin (2^k)

/-- This row includes isolated vertices and vertices carrying an empty history. -/
def present (home : U→V) (block : U→Block k) (v : V) (x : Block k) : Cell 1 :=
  if ∃u,home u=v ∧ block u=x then 1 else 0

def actorMask (home : U→V) (block : U→Block k) (v : V) : Cell (1*2^k) :=
  encode 1 (2^k) (present home block v)

theorem actor_read (home : U→V) (block : U→Block k) (v : V) (x : Block k) :
    digit 1 x.val (actorMask home block v).val=if ∃u,home u=v ∧ block u=x then 1 else 0 := by
  rw [actorMask,digit_encode]
  by_cases h : ∃u,home u=v ∧ block u=x <;> simp [present,h]

def bit (a : ℕ) : Cell 1 × Cell a ≃ Cell (1+a) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 1 a).symm)

def ticket (x : Option (Cell a)) : Cell (1+a) :=
  match x with
  | none=>bit a (0,0)
  | some i=>bit a (1,i)

def «matches» (q : Cell a) (s : Cell (1+a)) : Bool :=
  let z:=(bit a).symm s
  decide (z.1≠0 ∧ z.2=q)

theorem matches_ticket (q : Cell a) (x : Option (Cell a)) :
    «matches» q (ticket x)=decide (x=some q) := by
  cases x <;> simp [«matches»,ticket]

/-- All candidate old actors and genuine born-party tickets are public-width.
A query reads their short local destination and explicitly ignores each empty
slot. The full raster emits one Boolean per possible surviving coordinate. -/
def raster (a t b : ℕ) (query : Fin b→Cell a) (c : Cell ((1+a)*t)) : Cell (1*b) :=
  let r:=(encode (1+a) t).symm c
  encode 1 b (fun x=>if ∃j,«matches» (query x) (r j)=true then 1 else 0)

def panel (old : Fin t→Option (Cell a)) := encode (1+a) t (ticket ∘ old)

theorem raster_panel (q : Fin b→Cell a) (old : Fin t→Option (Cell a)) :
    raster a t b q (panel old) =
      encode 1 b (fun x=>if ∃j,old j=some (q x) then 1 else 0) := by
  simp [raster,panel,matches_ticket,Function.comp_def]

/-- Reindex all true old sites through an enumerated local candidate panel.
Repeated source records and several tickets choosing a common owner are allowed. -/
theorem raster_occupancy {R : Type} [Fintype R] (q : Block k→Cell a) (old : Fin t→Option (Cell a))
    (home : R→V) (block : R→Block k) (v : V)
    (forward : ∀j x,old j=some (q x)→∃u,home u=v ∧ block u=x)
    (back : ∀u,home u=v→∃j,old j=some (q (block u))) :
    raster a t (2^k) q (panel old)=actorMask home block v := by
  rw [raster_panel]
  apply congrArg (encode 1 (2^k))
  funext x
  have iff : (∃j,old j=some (q x)) ↔ ∃u,home u=v ∧ block u=x := by
    constructor
    · rintro ⟨j,hj⟩;exact forward j x hj
    · rintro ⟨u,hu,rfl⟩;exact back u hu
  simp only [present,iff]

/-- The two fixed tables may be shared by all candidate hosts. Dynamic
input cells carry only local tickets and never use global actor addresses. -/
theorem raster_read (g : Banks) (out : ℕ) (q : Fin b→Cell a)
    (raw : Fin H→Fin J→Fin t→Option (Cell a)) (fit : Fits g ((1+a)*t) (1*b) M H J w out)
    (m : Memory w) (source : PinFrame (M:=M) g (raster a t b q) (fun v j=>panel (raw v j)) m) :
    (program g out H J M w).Exec m
      (image out (H*chunks J M) (DescentSIMDLookup.lookup g) m) (4+H*chunks J M*(2*(DescentSIMDLookup.lookup g).work+4)) ∧
    ∀p : Row H J M,image out (H*chunks J M) (DescentSIMDLookup.lookup g) m (out+(row H J M p).val)=
      ((data (fun v h=>encode 1 b (fun x=>if ∃j,raw v h j=some (q x) then 1 else 0)) p).val:Word w) := by
  constructor
  · have fits : (DescentSIMDLookup.lookup g).Fits w out := by
      simp [DescentSIMDLookup.lookup,Expr.Fits,fit.source,fit.mask,fit.dictionary]
    exact @scan_exec w out (H*chunks J M) (DescentSIMDLookup.lookup g) m fits fit.output
  · intro p
    simpa only [raster_panel] using DescentSixParty.PackedCensus.col_read g out fit (raster a t b q)
      (fun v j=>panel (raw v j)) m source p

end
end Hierarchy.DescentActorRaster

end OAI
