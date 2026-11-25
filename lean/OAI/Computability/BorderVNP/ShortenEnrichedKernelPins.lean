import OAI.Computability.BorderVNP.PackedHistoryNamedReceipt
import OAI.Computability.BorderVNP.ShortenEnrichedStages

/-! # Reindexing a physical stage's occupied rows and histogram wires for the named history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.NamedKernel

open Crossing Cover Cover.Frame Cover.AddressCircuit Epoch Packing Shortening Shortening.Adaptive
open Shortening.PublicRelative Shortening.PublicSegments Shortening.PreparedBins Shortening.StaticRows Physical
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube

/-- The occupied cable directory and the raw table stored at one layer. -/
noncomputable abbrev Pins {D : ℕ} (S : Finset (HyperbolicHost (Cube D))) (l V E w : ℕ) :=
  Fin E ⊕ Raw (ProductSlots (Fintype.card (Cube D)) l ⊕ ↥S) V E w w

/-- Express the same native row pin using its schedule's level, catalog and rectangle sizes. -/
def outputPin {D V E V' E' l l' w : ℕ} {S S' : Finset (HyperbolicHost (Cube D))}
    (hl : l'=l) (hs : S'=S) (hv : V'=V) (he : E'=E) : Pins S' l' V' E' w → Pins S l V E w := by
  cases hl; cases hs; cases hv; cases he
  exact id

/-- Store the literal site and cable numbers in the equal schedule rectangle. -/
def directoryAt {D V E V' E' lev : ℕ} {K : Type*} {P : Type} {bits : P → ℕ}
    {pack : PlacedPack D P bits K (Cube D) lev} (hv : V'=V) (he : E'=E) (dir : Directory pack V E) :
    Directory pack V' E' := by cases hv; cases he; exact dir

/-- The numeric public site address is preserved by a rectangle cast. -/
theorem directoryAt_site {D V E V' E' lev : ℕ} {K : Type*} {P : Type} {bits : P → ℕ}
    {pack : PlacedPack D P bits K (Cube D) lev} (hv : V'=V) (he : E'=E) (dir : Directory pack V E)
    (v : pack.pack.layout.Site) : ((directoryAt hv he dir).sites v).val = (dir.sites v).val := by
  cases hv; cases he; rfl

/-- Reindexing to the scheduled dimensions retains every numerical cable row. -/
theorem directoryAt_cable {D V E V' E' lev : ℕ} {K : Type*} {P : Type} {bits : P → ℕ}
    {pack : PlacedPack D P bits K (Cube D) lev} (hv : V'=V) (he : E'=E) (dir : Directory pack V E)
    (z : pack.pack.layout.Edge) : ((directoryAt hv he dir).cables z).val = (dir.cables z).val := by
  cases hv; cases he; rfl

/-- Dense save reads the same physical row data after the source path's
depth, catalog and rectangle equalities. -/
theorem directoryAt_reads {D V E V' E' lev l w : ℕ} {K : Type*} {P : Type} {bits : P → ℕ}
    {S S' : Finset (HyperbolicHost (Cube D))} {pack : PlacedPack D P bits K (Cube D) lev}
    (hl : lev+1=l) (hs : S'=S) (hv : V'=V) (he : E'=E) (dir : Directory pack V E)
    (y : Pins S l V E w → Bool) (h : dir.dense.Reads S (segmentField (factorEnum D) S hl) y) :
    (directoryAt hv he dir).dense.Reads S' (segmentField (factorEnum D) S' rfl)
      (y ∘ outputPin hl hs hv he) := by
  cases hl; cases hs; cases hv; cases he
  exact h

variable {X Y G T T' : Type} [Fintype X] [Fintype Y] [Fintype G] [Fintype T] [Fintype T']

/-- Relabel the physical guesses and stored rows by their scheduled public
pins. The selected physical computation and guard share their original gates. -/
noncomputable def scheduled (f : Frame (X ⊕ Y) (T ⊕ Unit)) (guess : Y → G) (out : T' → T) :
    Frame (X ⊕ G) (T' ⊕ Unit) :=
  (f.subst (Frame.initial (Sum.map id guess))).select (Sum.map out id)

/-- The complete literal native gate count is preserved. -/
theorem scheduled_size (f : Frame (X ⊕ Y) (T ⊕ Unit)) (guess : Y → G) (out : T' → T) :
    (scheduled f guess out).size = f.size := by simp [scheduled]

/-- A scheduled assignment is read at the native histogram word coordinates. -/
theorem scheduled_eval (f : Frame (X ⊕ Y) (T ⊕ Unit)) (guess : Y → G) (out : T' → T)
    (x : X → Bool) (g : G → Bool) :
    (scheduled f guess out).eval (Sum.elim x g) = (f.eval (Sum.elim x (g ∘ guess))) ∘ Sum.map out id := by
  have hread : (Frame.initial (Sum.map (id : X → X) guess)).eval (Sum.elim x g) = Sum.elim x (g ∘ guess) := by
    funext j
    cases j <;> simp
  funext j
  simp only [scheduled,Frame.select_eval,Frame.subst_eval,hread,Function.comp_apply]

variable {D m b k : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} {bits : P → ℕ}
    {e : PaidIdentity K D m} {B : Fin b → Type} [∀ i, Fintype (B i)] {lev w : ℕ → ℕ}

omit [NeZero D] [∀ i, Fintype (B i)] in
/-- Native count bits use the same index and physical seed as the history codec. -/
theorem fields_at_pin (i : Fin b) (g : Pin (Cube D) B lev e.count w i.val → Bool)
    (a : Seed (Cube D) B lev i) (t : Fin e.count) (j : Fin (w i.val)) :
    (g ∘ pinEquiv (e := e) w i) (a,t,j) = fields (e := e) w i g a t j := rfl

/-- The actual histogram encoded through scheduled pins pulls back to the
very word emitted by the physical branch encoder. -/
theorem word_at_pin (i : Fin b) {child : Fin k → PlacedPack D P bits K (Cube D) (lev i.val)}
    (s : Stage m (B i) (lev (i.val+1)) child) (room : ∀ a, s.matched a < 2^(w i.val)) (hist : s.Index e) :
    let g := (fields (B := B) (I := Cube D) (depth := lev) (e := e) w i).symm
      ((BankCircuit.branches e s.matched room).symm hist).val
    g ∘ pinEquiv (e := e) w i = NamedReceipt.word s room hist := by
  intro g
  funext ⟨a,t,j⟩
  rw [fields_at_pin]
  exact congrFun (congrFun (congrFun ((fields (e := e) w i).apply_symm_apply _) a) t) j

end PackedHistoryCircuit.Normalized.NamedKernel

end BorderVNP
end Computability
end OAI
