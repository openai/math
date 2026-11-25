import OAI.Computability.BorderVNP.ShortenPublicSegment
import OAI.Computability.BorderVNP.CoverProductMetadataFrame

/-!
# Boolean circuits for recovering segment tags from ordered site rows

The input gives the two site tags in one-hot form and their canonical product
tile words. The circuit extracts a fixed low window in each coordinate, then
reads a finite table on the two tags and two low residues. No circuit evaluates
a distance or a real-coordinate chart.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Epoch Catalog AddressCircuit StackFrame
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open scoped Classical

/-- One endpoint's normalized site index and product deck address. -/
abbrev FieldBit (Site I : Type*) (l : ℕ) := Site ⊕ I × Slots (width l)

/-- Two public endpoint rows in the stable cable orientation. -/
def pairInput {Site I : Type*} [DecidableEq Site] (l : ℕ) (a b : Site) (x y : I → Deck l) :
    Bool × FieldBit Site I l → Bool := fun z =>
  if z.1 then z.2.elim (fun u => decide (u=a)) (fun i => deckWires l (x i.1) i.2)
  else z.2.elim (fun u => decide (u=b)) (fun i => deckWires l (y i.1) i.2)

private def jointTag {Site I : Type*} (l : ℕ) (u : Site × Site) :
    Expr (Bool × FieldBit Site I l) :=
  .and (.input (true,.inl u.1)) (.input (false,.inl u.2))

/-- A depth-polynomial row circuit reads an arbitrary fixed finite table on
the ordered site tags and their relative low deck displacement. -/
theorem pairLookup_frames {Site I Out : Type*} [Fintype Site] [DecidableEq Site]
    [Fintype I] [Fintype Out] (k : ℕ) :
    ∃ C e, ∀ l (hk : k ≤ l) (read : Site → Site → (I → Deck k) → Out → Bool),
      ∃ f : Frame (Bool × FieldBit Site I l) Out, f.size ≤ C*(l+1)^e ∧ ∀ a b x y,
        f.eval (pairInput l a b x y) = read a b fun i => deckReduction hk ((x i)⁻¹ * y i) := by
  let q := Fintype.card (Bool × I)
  let enum : Fin q ≃ Bool × I := (Fintype.equivFin _).symm
  obtain ⟨P,e,hP⟩ := productMetadataFrames (T := Site × Site) (I := Out) q k
  refine ⟨3*Fintype.card (Site × Site)+P,e,?_⟩
  intro l hk read
  let table (v : Site × Site) (s : Fin q → Deck k) :=
    read v.1 v.2 fun i => (s (enum.symm (true,i)))⁻¹ * s (enum.symm (false,i))
  obtain ⟨get,hsize,heval⟩ := hP l hk table
  let tag : Frame (Bool × FieldBit Site I l) (Site × Site) :=
    (Frame.initial id).step (jointTag l)
  let addr : Frame (Bool × FieldBit Site I l) (Fin q × Slots (width l)) :=
    Frame.initial fun i => ((enum i.1).1,.inr ((enum i.1).2,i.2))
  let joint := Crossing.parallelFrame tag addr
  refine ⟨get.subst joint,?_,?_⟩
  · have ht := Frame.step_size_le (Frame.initial id) (jointTag (I := I) (Site := Site) l) 3 fun _ => le_rfl
    have hs : joint.size ≤ 3*Fintype.card (Site × Site) := by
      simpa [joint,tag,addr,mul_comm] using ht
    rw [Frame.subst_size]
    have one : 1 ≤ (l+1)^e := Nat.one_le_pow _ _ (by omega)
    exact (Nat.add_le_add hs hsize).trans (by
      rw [Nat.add_mul]
      exact Nat.add_le_add_right (by simpa using Nat.mul_le_mul_left (3*Fintype.card (Site × Site)) one) _)
  · intro a b x y
    let s (i : Fin q) := if (enum i).1 then x (enum i).2 else y (enum i).2
    have hj : joint.eval (pairInput l a b x y) = metadataInput l (a,b) s := by
      funext z
      cases z with
      | inl u =>
        simp [joint,tag,Frame.step_eval,jointTag,Expr.eval,pairInput,metadataInput,Prod.ext_iff]
      | inr u =>
        rw [show joint = Crossing.parallelFrame tag addr from rfl,Crossing.parallelFrame_eval_inr]
        change addr.eval (pairInput l a b x y) u = deckWires l (s u.1) u.2
        cases hc : (enum u.1).1 <;> simp [addr,pairInput,s,hc]
    funext j
    rw [Frame.subst_eval,hj,heval]
    simp [table,s]

variable {D : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)

/-- Physical site row in the finite catalog and deck-wire representation. -/
noncomputable def siteBits {d : ℕ} (x : SurfaceHost (Cube D) (d+1)) (hx : relative d x ∈ S) :
    FieldBit (↥S) (Cube D) (d+1) → Bool :=
  Sum.elim (fun u => decide (u=(⟨relative d x,hx⟩ : ↥S)))
    (fun z => deckWires (d+1) (productAddress d x z.1) z.2)

/-- Exactly the two wiresets obtained by following an old cable's source and destination IDs. -/
noncomputable def endpointBits {d : ℕ} (x y : SurfaceHost (Cube D) (d+1))
    (hx : relative d x ∈ S) (hy : relative d y ∈ S) : Bool × FieldBit (↥S) (Cube D) (d+1) → Bool :=
  pairInput (d+1) (⟨relative d x,hx⟩ : ↥S) ⟨relative d y,hy⟩ (productAddress d x) (productAddress d y)

/-- The output row has no tag for a coincident cable and has precisely one
distance-realizing catalog tag for every positive-length short cable. -/
def TypeRow (d : ℕ) (f : Frame (Bool × FieldBit (↥S) (Cube D) (d+1)) B.types) : Prop :=
  (∀ (x : SurfaceHost (Cube D) (d+1)) (hx : relative d x ∈ S),
    f.eval (endpointBits x x hx hx) = fun _ => false) ∧
  ∀ (x y : SurfaceHost (Cube D) (d+1)) (hx : relative d x ∈ S) (hy : relative d y ∈ S),
    x ≠ y → dist x y ≤ 2*h → ∃ t : B.types, Realizes x y t.val.ends ∧
      f.eval (endpointBits x y hx hy) = fun u => decide (u=t)

/-- A shared depth-polynomial circuit reads both endpoint records, including
zero-length cables that must contribute zero to the population. -/
theorem totalTypeRow_frames :
    ∃ k C e, ∀ d, k ≤ d+1 → ∃ f, f.size ≤ C*(d+2)^e ∧ TypeRow B d f := by
  obtain ⟨k,valid⟩ := exists_total_lookup_level B
  obtain ⟨C,e,frames⟩ := pairLookup_frames (Site := ↥S) (I := Cube D) (Out := ↥B.types) k
  refine ⟨k,C,e,?_⟩
  intro d hk
  let read (a b : ↥S) (disp : Cube D → Deck k) (t : B.types) := decide (lookup B k (a.val,b.val,disp) = some t)
  obtain ⟨f,hs,hf⟩ := frames (d+1) hk read
  refine ⟨f,hs,?_,?_⟩
  · intro x hx
    rw [endpointBits,hf]
    funext u
    change decide (lookup B k (endpointKey hk x x) = some u) = false
    simp [(valid hk).1 x]
  intro x y hx hy hn hxy
  obtain ⟨t,ht,hr⟩ := (valid hk).2 x y hx hy hn hxy
  refine ⟨t,hr,?_⟩
  rw [endpointBits,hf]
  funext u
  change decide (lookup B k (endpointKey hk x y) = some u) = decide (u=t)
  simp [ht,eq_comm]

/-- The tag recovery circuit supplies a genuine catalog realization of every
active ordered cable from the two words obtained by the public endpoint join. -/
theorem geometricLookup_frames :
    ∃ k C e, ∀ d, k ≤ d+1 → ∃ f : Frame (Bool × FieldBit (↥S) (Cube D) (d+1)) B.types,
      f.size ≤ C*(d+2)^e ∧ ∀ (x y : SurfaceHost (Cube D) (d+1))
      (hx : relative d x ∈ S) (hy : relative d y ∈ S), x ≠ y → dist x y ≤ 2*h →
      ∃ t : B.types, Realizes x y t.val.ends ∧ f.eval (endpointBits x y hx hy) = fun u => decide (u=t) := by
  obtain ⟨k,C,e,frames⟩ := totalTypeRow_frames B
  refine ⟨k,C,e,?_⟩
  intro d hd
  obtain ⟨f,hf,he⟩ := frames d hd
  exact ⟨f,hf,he.2⟩

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
