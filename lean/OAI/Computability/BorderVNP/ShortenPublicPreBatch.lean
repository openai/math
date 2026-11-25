import OAI.Computability.BorderVNP.ShortenPublicRelativePlacement
import OAI.Computability.BorderVNP.ShortenPublicSegmentStage

/-!
# Assembling the actual pack-site inputs from selected motions and raw site rows

The one-hot choice is rewired by the fixed permutation of candidate numbers.
All old site and common translation wires are copied from the same raw geometry
and motion bank used by the histogram. Only the complete seed table needs
literal gates. Unoccupied old site names may contain arbitrary bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Epoch Catalog Cover Cover.AddressCircuit PublicSegments Crossing
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open scoped Classical

variable {D q : ℕ} {S : Finset (HyperbolicHost (Cube D))} {M Data : Type*} {A : Type}
variable [Fintype M] [Fintype Data]

/-- The actual producer input: one selected candidate and shift per pack,
plus the raw stable site and cable fields of the preceding geometry. -/
abbrev PreInput (M Data : Type*) (q l copies sites edges k w : ℕ) :=
  Motion M q l copies ⊕ Raw Data sites edges k w

/-- Fixed seed metadata for every reserved geometric address, including seeds
whose cable population is zero. -/
noncomputable def seedBits (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D) {l seeds : ℕ}
    (seed : A ≃ Fin seeds) (code : A → Fin pat.bins) (tile : A → Cube D → Deck l)
    (i : Fin seeds) : Fin pat.bins ⊕ ProductSlots q l → Bool :=
  Sum.elim (fun b => decide (b=code (seed.symm i))) (productWires l (tile (seed.symm i) ∘ enum))

/-- Wire interpretation of every prepared row column. No data-dependent
gather occurs at the old site rows. -/
noncomputable def preFields (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D) {d copies sites edges k w seeds : ℕ}
    (motion : M ≃ Fin pat.moves) (field : FieldBit (↥S) (Cube D) (d+2*pat.depth+2*pat.depth) → Data)
    (seed : A ≃ Fin seeds) (code : A → Fin pat.bins) (tile : A → Cube D → Deck (d+2*pat.depth))
    (x : PreInput M Data q (d+2*pat.depth) copies sites edges k w → Bool) :
    BatchPorts q pat S d copies sites seeds → Bool
  | .inl (i,.inl u) => x (.inl (i,.inl (motion.symm u)))
  | .inl (i,.inr j) => x (.inl (i,.inr j))
  | .inr (.inl (r,.inl t)) => x (.inr (.inr (.inl (r,field (.inl t)))))
  | .inr (.inl (r,.inr (i,j))) => x (.inr (.inr (.inl (r,field (.inr (enum i,j))))))
  | .inr (.inr (i,j)) => seedBits enum pat seed code tile i j

/-- Literal seed rows cost one gate per actual seed bit. Every copy bank and
every old site payload is forwarded by a wire. The same circuit accepts all
geometric branches at the chosen dimensions. -/
theorem preBatchPorts_frames (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D)
    (d copies sites edges k w : ℕ) (motion : M ≃ Fin pat.moves)
    (field : FieldBit (↥S) (Cube D) (d+2*pat.depth+2*pat.depth) → Data) {seeds : ℕ}
    (seed : A ≃ Fin seeds) (code : A → Fin pat.bins) (tile : A → Cube D → Deck (d+2*pat.depth)) :
    ∃ f : Frame (PreInput M Data q (d+2*pat.depth) copies sites edges k w) (BatchPorts q pat S d copies sites seeds),
      f.size ≤ seeds*(pat.bins+90*q*(d+2*pat.depth+1)) ∧
      ∀ x, f.eval x = preFields enum pat motion field seed code tile x := by
  let X := PreInput M Data q (d+2*pat.depth) copies sites edges k w
  let Y := Fin seeds × (Fin pat.bins ⊕ ProductSlots q (d+2*pat.depth))
  let lits (j : Y) : Expr X := .const (seedBits enum pat seed code tile j.1 j.2)
  let bank := (Frame.initial (id : X → X)).step lits
  let pin : BatchPorts q pat S d copies sites seeds → X ⊕ Y
    | .inl (i,.inl u) => .inl (.inl (i,.inl (motion.symm u)))
    | .inl (i,.inr j) => .inl (.inl (i,.inr j))
    | .inr (.inl (r,.inl t)) => .inl (.inr (.inr (.inl (r,field (.inl t)))))
    | .inr (.inl (r,.inr (i,j))) => .inl (.inr (.inr (.inl (r,field (.inr (enum i,j))))))
    | .inr (.inr j) => .inr j
  refine ⟨bank.withInput.select pin,?_,?_⟩
  · simp only [Frame.select_size,Frame.withInput_size]
    apply (Frame.step_size_le (Frame.initial id) lits 1 (fun _ => le_rfl)).trans_eq
    simp [Y,ProductSlots,StackFrame.Slots,width]; ring_nf; simp
  · intro x
    funext j
    rcases j with ⟨i,u|u⟩ | ⟨r,t|⟨i,j⟩⟩ | ⟨s,j⟩ <;>
      simp only [Frame.select_eval,pin,Frame.withInput_eval_inl,Frame.withInput_eval_inr,bank,
        Frame.step_eval,lits,Expr.eval,preFields]

/-- Reading a genuine lifted site in the raw table supplies exactly the
normalized tag and modular carry used by the geometric row circuit. -/
theorem siteAtBits_lift {S : Finset (HyperbolicHost (Cube D))} {z : ℕ} (hz : 0 < z)
    (u : HyperbolicHost (Cube D)) (x : SurfaceHost (Cube D) z) (proj : productProjection z u = x)
    (hx : relativeAt z hz x ∈ S) (hu : normalize u ∈ S) :
    siteAtBits hz x hx = Sum.elim (fun t => decide (t=(⟨normalize u,hu⟩ : ↥S)))
      (fun j => deckWires z (carry u j.1 : Deck z) j.2) := by
  subst x
  cases z with
  | zero => omega
  | succ z => rfl

variable {P : Type*} {bits : P → ℕ} {K : Type*} [Field K] {m : ℕ} [NeZero D] [Fintype A]

omit [Fintype M] [Fintype Data] [Field K] [Fintype A] in
/-- At each occupied site the copied input wires are exactly its actual
selected motion, posttranslation, catalog tag and tile. At each seed the
literal bank names the geometric chart and its tile. -/
theorem preFields_reads [DecidableEq M] (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D)
    (N : Pack D P bits K) (bin : N.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    {d lev copies sites edges seeds k w : ℕ} (home : Fin sites → Fin copies)
    (g : CombiningStep.Placement (m := m) N bin perm (Cube D) (SurfaceHost (Cube D) (lev+1)))
    (a : PublicPlacement pat S N bin perm lev g) (old : N.layout.Site ↪ Fin sites) (seed : A ≃ Fin seeds)
    (motion : M ≃ Fin pat.moves) (field : FieldBit (↥S) (Cube D) (d+2*pat.depth+2*pat.depth) → Data)
    (pick : Fin copies → M) (shift : Fin copies → Cube D → Deck (d+2*pat.depth))
    (code : A → Fin pat.bins) (tile : A → Cube D → Deck (d+2*pat.depth))
    (raw : Raw Data sites edges k w → Bool) (hz : 0 < d+2*pat.depth+2*pat.depth)
    (pos : N.layout.Site → SurfaceHost (Cube D) (d+2*pat.depth+2*pat.depth))
    (valid : ∀ v, relativeAt _ hz (pos v) ∈ S) (proj : ∀ v, productProjection _ (a.oldLift v) = pos v)
    (payload : ∀ v j, raw (.inr (.inl (old v,field j))) = siteAtBits hz (pos v) (valid v) j)
    (chosen : ∀ v, motion (pick (home (old v))) = a.copyMotion v)
    (post : ∀ v i, shift (home (old v)) i = (a.oldDeck v i : Deck (d+2*pat.depth)))
    (hc : ∀ s, code s = a.code s) (ht : ∀ s i, tile s i = (a.deck s i : Deck (d+2*pat.depth))) :
    PlacementReads N bin perm enum pat S home g a old seed.toEmbedding
      (preFields enum pat motion field seed code tile (Sum.elim (motionWires enum pick shift) raw)) := by
  constructor
  · intro v
    have hp (t) := congrFun (siteAtBits_lift hz (a.oldLift v) (pos v) (proj v) (valid v) (a.oldType v)) t
    funext j
    rcases j with j | t | ⟨i,j⟩ | ⟨i,j⟩
    · change decide (motion.symm j = pick (home (old v))) = decide (j = a.copyMotion v)
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,← chosen v,motion.symm_apply_eq]
    · exact (payload v (.inl t)).trans (hp (.inl t))
    · change deckWires _ (shift (home (old v)) (enum i)) j = _
      rw [post]
      rfl
    · exact (payload v (.inr (enum i,j))).trans (hp (.inr (enum i,j)))
  · intro s j
    rcases j with b | ⟨i,j⟩
    · change decide (b=code (seed.symm (seed s))) = decide (b=a.code s)
      rw [seed.symm_apply_apply,hc]
    · change deckWires _ (tile (seed.symm (seed s)) (enum i)) j = _
      rw [seed.symm_apply_apply,ht]
      rfl

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
