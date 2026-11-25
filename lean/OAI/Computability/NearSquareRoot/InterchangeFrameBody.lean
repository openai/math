import OAI.Computability.NearSquareRoot.InterchangeFrame
import OAI.Computability.NearSquareRoot.InterchangeLeaf

/-! # Physical composition of the leading, middle, and trailing interchanges -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeFrame

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  NearSquareRoot.InterchangeAddress

variable {I X : Type} {r : Regime I} {l : I → ℕ} {job : Job X}
    {account : I → List X → Prop} {good : I → Tree → Prop}
    {A E : I → Type} {s : (i : I) → Series (A i)} {u : (i : I) → Series (E i)}

/-- The fixed physical program receives the common parent descriptor and
the serialized row, and returns the serialized row with the given reindexing. -/
def Program (job : Job X) (r : Regime I) (l : I → ℕ) (account : I → List X → Prop)
    (good : I → Tree → Prop) {A : I → Type} (s : (i : I) → Series (A i))
    (action : (i : I) → A i → A i) : Prop :=
  ∀ v : (i : I) → A i → Tree, Manifest A l v → (∀ i a, good i (v i a)) →
    ∃ uses : I → List X, (∀ i, account i (uses i)) ∧ Quest job r (fun i => (s i).count) l uses
      (together r.header (stackRun s v)) (stackRun s fun i => v i ∘ action i)

namespace Program

theorem align {g : (i : I) → E i → E i} {f : (i : I) → A i → A i}
    (view : ∀ i, Adopt (s i) (u i)) (correct : ∀ i a, (view i).cast (f i a) = g i ((view i).cast a))
    (h : Program job r l account good u g) : Program job r l account good s f := by
  intro v hv hg
  let w i := v i ∘ (view i).cast.symm
  have data : stackRun u w = stackRun s v := by
    funext i
    rw [stackRun,(view i).packet]
    apply congrArg (stripe _)
    funext a
    exact congrArg (v i) ((view i).cast.symm_apply_apply a)
  have out : stackRun u (fun i => w i ∘ g i) = stackRun s (fun i => v i ∘ f i) := by
    funext i
    rw [stackRun,(view i).packet]
    apply congrArg (stripe _)
    funext a
    exact congrArg (v i) (by
      rw [← correct,(view i).cast.symm_apply_apply])
  have same : (fun i => (s i).count) = fun i => (u i).count := funext fun i => (view i).cost
  rw [same,← data,← out]
  exact h w (hv.shift fun i => (view i).cast.symm) (fun i a => hg i _)

theorem chain {g f : (i : I) → A i → A i} {first second : I → List X → Prop}
    (hs : Station r s) (p : Program job r l first good s f)
    (q : Program job r l second good s g)
    (accounting : ∀ i a b, first i a → second i b → account i (a ++ b)) :
    Program job r l account good s (fun i => f i ∘ g i) := by
  intro v hv hg
  let after i := v i ∘ f i
  let packet := stackRun s v
  have old := hv.lives hs
  have next := (hv.shift f).lives hs
  have key := Drive.fetch hs.1 old
  obtain ⟨left, hl, runl⟩ := p v hv hg
  obtain ⟨right, hr, runr⟩ := q after (hv.shift f) (fun i a => hg i _)
  refine ⟨fun i => left i ++ right i,fun i => accounting i _ _ (hl i) (hr i),?_⟩
  have parked := (runl.pack r.header).hand (key.again.twice key)
  have recover := Rip.split (Rip.alivePair next key.idle)
  exact (parked.transfer (recover.2.twice recover.1)).seam runr

/-- A bounded end-piece costs zero recursive calls. The axis supplies a
byte-compatible view of the actual prefix, field, gap, field, suffix encoding. -/
theorem bounded {b : ℕ} [NeZero b] (q : ℕ) (hb : 2 ≤ b)
    {f : I → ℕ} {P G B : I → Dims.Tape} (axis : ∀ i, Axis (s i) (P i) (line b (f i))
      (G i) (line b (f i)) (B i)) (op : (i : I) → A i → A i)
    (correct : ∀ i a, (axis i).view.cast (op i a) = swapper _ _ _ ((axis i).view.cast a))
    (hf : r.Has (tally ∘ f)) (bound : ∀ i, f i ≤ q)
    (hp : Told r P) (hg : Told r G) (hs : Told r B) :
    Program job r l (fun _ a => a = []) good s op := by
  intro v hv _
  refine ⟨fun _ => [],fun _ => rfl,Quest.entry ?_⟩
  exact Request.bounded_axis_fleet q hb s P G B f l axis hf hp hg hs bound op correct v hv

private theorem station_of_view (view : ∀ i, Adopt (s i) (u i)) (hs : Station r u) :
    Station r s := by
  unfold Station at *
  simpa only [(view _).cost] using hs

end Program

variable {J : Type} {b n : ℕ} [NeZero b]
    (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (h f t : I → ℕ)

/-- The direct leading and remainder swaps surround the central program.
Its complete ledger is carried through unchanged. The two short
fields need only be bounded by a fixed constant. -/
theorem assemble (hb : 2 ≤ b) (q : ℕ) (hhq : ∀ i, h i ≤ q) (htq : ∀ i, t i ≤ q)
    (hh : r.Has (tally ∘ h)) (hf : r.Has (tally ∘ f)) (ht : r.Has (tally ∘ t))
    (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (body : Program job r l account good
      (fun i => arrays ord (line b (f i)) (pre b (h i) (P i))
        (gap b (h i) (t i) (G i)) (post b (t i) (B i)))
      (fun _ => swapper _ _ _)) :
    Program job r l account good
      (fun i => stock b (P i) (G i) (B i) (width (n:=n) (h i) (f i) (t i)))
      (fun _ => swapper _ _ _) := by
  let s i := expanded ord b (h i) (f i) (t i) (P i) (G i) (B i)
  let root i := parent ord b (h i) (f i) (t i) (P i) (G i) (B i)
  let mid i := axis ord b (h i) (f i) (t i) (P i) (G i) (B i)
  let a i := leading (J:=J) b (h i) (f i) (t i) (P i) (G i) (B i)
  let v i := center (J:=J) b (h i) (f i) (t i) (P i) (G i) (B i)
  let z i := trailing (J:=J) b (h i) (f i) (t i) (P i) (G i) (B i)
  have th := Told.carrier hb h hh
  have tf := (Told.carrier hb f hf).stacked n
  have tt := Told.carrier hb t ht
  have side₁ := Told.nil.append (tf.append tt)
  have side₂ := th.append (tf.append Told.nil)
  have A : Program job r l (fun _ q => q = []) good s a :=
    Program.bounded q hb (fun i => leadingAxis ord b (h i) (f i) (t i) (P i) (G i) (B i)) a
      (fun i => leading_cast ord b (h i) (f i) (t i) (P i) (G i) (B i)) hh hhq (hp.append Told.nil) (side₁.append (hg.append Told.nil))
      (side₁.append hs)
  have V : Program job r l account good s v :=
    Program.align (fun i => (mid i).view) (fun i => center_cast ord b (h i) (f i) (t i) (P i) (G i) (B i)) body
  have Z : Program job r l (fun _ q => q = []) good s z :=
    Program.bounded q hb (fun i => trailingAxis ord b (h i) (f i) (t i) (P i) (G i) (B i)) z
      (fun i => trailing_cast ord b (h i) (f i) (t i) (P i) (G i) (B i)) ht htq (hp.append side₂) (Told.nil.append (hg.append side₂))
      (Told.nil.append hs)
  have st : Station r s := Program.station_of_view (fun i => (mid i).view)
    (layoutRows_station ord _ _ _ f hb hf (hp.append th) (tt.append (hg.append th)) (tt.append hs))
  have first : Program job r l account good s (fun i => a i ∘ v i) :=
    A.chain st V (fun _ _ _ h rest => by simpa only [h,List.nil_append] using rest)
  have full : Program job r l account good s (fun i => (a i ∘ v i) ∘ z i) :=
    first.chain st Z (fun _ _ _ rest h => by simpa only [h,List.append_nil] using rest)
  apply Program.align (fun i => (root i).back) _ full
  intro i k
  apply (root i).cast.injective
  have e := parent_cast ord b (h i) (f i) (t i) (P i) (G i) (B i) ((root i).cast.symm k)
  simpa only [root,Adopt.back,Equiv.apply_symm_apply,Function.comp_apply,a,v,z] using e.symm


end InterchangeFrame

end NearSquareRoot
end Computability
end OAI
