import OAI.Computability.NearSquareRoot.InterchangeAddress
import OAI.Computability.IntegerMultiplication.Loom.Rotor
import OAI.Computability.IntegerMultiplication.Loom.Fare

/-!
# Charged calls of the address program

Each P192 pivot issues exactly one call to the interchange of two fields at
the supplied digit width. Its query includes the new prefix, gap, and suffix
descriptors. The reindexing through the two chosen fields preserves the
physical stream order, so preparing and returning the payload involves no
implicit array permutation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port
  IntegerMultiplication.Adic IntegerMultiplication.Loom

/-- A recursive request contains one stream. Its record bound is a proof
parameter; the shape and field width are sent to the program explicitly. -/
structure Request (b : ℕ) where
  before : Dims.Tape
  between : Dims.Tape
  after_ : Dims.Tape
  width : ℕ
  recordWidth : ℕ
  contents : SpanKey before between after_ (Block b width) → Tree

namespace Request

abbrev rows {b} (a : Request b) := stock b a.before a.between a.after_ a.width
abbrev header {b} (a : Request b) :=
  send (tally a.width, shape a.before, shape a.between, shape a.after_)

abbrev job (b : ℕ) : Job (Request b) where
  issue a := Tree.fork a.header (stripe a.rows a.contents)
  reply a := stripe a.rows (a.contents ∘ swapper _ _ _)

end Request

variable {I J : Type} [DecidableEq J] {b n : ℕ} [NeZero b]
    {r : Regime I} {l : I → ℕ} (ord : J ≃ Fin n)
    (P G B : I → Dims.Tape) (f : I → ℕ)

abbrev countRows (i : I) := (layoutRows (b:=b) ord P G B f i).count
abbrev allowed {b : ℕ} (f N l : I → ℕ) (i : I) (a : Request b) :=
  a.width = f i ∧ a.rows.count = N i ∧ a.recordWidth = l i

/-- A costed program with the parent header attached on input. -/
abbrev Charged (budget : ℕ) (input output : I → Tree) :=
  Hopto (Request.job b) r (countRows (b:=b) ord P G B f) l
    (allowed f (countRows (b:=b) ord P G B f) l) budget (together r.header input) output

/-- The child payload invariant can be chosen separately for every input.
This allows a recursive caller to restrict the query space to packed rows of
the correct finite alphabet and payload length. -/
abbrev ChargedGood (good : I → Tree → Prop) (budget : ℕ) (input output : I → Tree) :=
  Hopto (Request.job b) r (countRows (b:=b) ord P G B f) l
    (fun i a => allowed f (countRows (b:=b) ord P G B f) l i a ∧ ∀ k, good i (a.contents k))
    budget (together r.header input) output

/-- Every dimension of the recursive call is inherited from the three
spectator tapes or is one of the newly exposed radix digits. -/
def inherited (b : ℕ) (P G B : Dims.Tape) (a : Request b) : Prop :=
  ∀ k ∈ a.before ++ a.between ++ a.after_, k = b ∨ k ∈ P ++ G ++ B

abbrev ChargedTyped (good : I → Tree → Prop) (budget : ℕ) (input output : I → Tree) :=
  Hopto (Request.job b) r (countRows (b:=b) ord P G B f) l
    (fun i a => (allowed f (countRows (b:=b) ord P G B f) l i a ∧ ∀ k, good i (a.contents k))
       ∧ inherited b (P i) (G i) (B i) a)
    budget (together r.header input) output

theorem source_radix (k w b s : ℕ) (hk : k ∈ Rack (field b w) s) : k = b := by
  rw [rack_eq] at hk
  generalize s * w = a at hk
  induction a with
  | zero => exact False.elim (List.not_mem_nil hk)
  | succ a ih => exact (List.mem_cons.mp hk).elim id ih

private theorem pivot (good : I → Tree → Prop) {r : Regime I} (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (x y : J)
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (hv : Manifest _ l v)
    (hgood : ∀ i k, good i (v i k)) :
    ChargedTyped (r:=r) (l:=l) ord P G B f (b:=b) good 1 (stackRun (layoutRows ord P G B f) v)
      (stackRun (layoutRows ord P G B f)
        (fun i => v i ∘ (reflect ord (.pivot x y) trivial (P i) (G i) (B i) (f i)).symm)) := by
  let D i := field b (f i)
  let L i := preamble ord (P i) (G i) (D i) (false,x)
  let M i := silence ord (G i) (D i) (false,x) (true,y)
  let S i := appendix ord (G i) (B i) (D i) (true,y)
  let axis (i : I) := twoStops ord (false,x) (true,y) (Or.inl ⟨rfl,rfl⟩)
    (p:=b) (j:=f i) (P:=P i) (G:=G i) (B:=B i)
  let child (i : I) : Request b :=
    ⟨L i, M i, S i, f i, l i, v i ∘ (axis i).view.cast.symm⟩
  have st := layoutRows_station ord P G B f hb hf hp hg hs
  have hv0 := hv.lives st
  have hfi := Told.carrier hb f hf
  have tag : r.Small (fun i => (child i).header) :=
    hf.pair ((hfi.stair ord hp hg (false,x)).shape.pair
      ((hfi.corridor ord hg (false,x) (true,y)).shape.pair (hfi.lounge ord hg hs (true,y)).shape))
  let data := stackRun (layoutRows ord P G B f) v
  have pre (i : I) : stripe (child i).rows (child i).contents = data i := by
    rw [(axis i).view.packet]
    apply congrArg (stripe _)
    funext z
    exact congrArg (v i) ((axis i).view.cast.symm_apply_apply z)
  let ans i := v i ∘ (reflect ord (.pivot x y) trivial (P i) (G i) (B i) (f i)).symm
  have post (i : I) : (Request.job b).reply (child i) =
      stripe (layoutRows ord P G B f i) (ans i) := by
    unfold Request.job
    dsimp only
    rw [(axis i).view.packet]
    rfl
  have prep : Drive r (countRows (b:=b) ord P G B f) l data
      ((Request.job b).issue ∘ child) := by
    have := (Drive.fetch st.1 hv0).chain (Rip.header st.1 tag)
    have g := this.twice (Drive.self st.1 hv0)
    have issue_eq : (Request.job b).issue ∘ child =
        together (fun i => (child i).header) data := by
      funext i
      exact congrArg (Tree.fork (child i).header) (pre i)
    rwa [issue_eq]
  refine ⟨fun i => [child i], ?_, by simp, ?_⟩
  · intro i a ha
    obtain rfl := List.mem_singleton.mp ha
    refine ⟨⟨⟨rfl,(axis i).view.cost.symm,rfl⟩, fun k => hgood i _⟩,?_⟩
    intro k hk
    change k ∈ (L i ++ M i) ++ S i at hk
    simp only [L,M,S,preamble_false,silence_false_true,appendix_true,List.mem_append] at hk
    simp only [List.mem_append]
    rcases hk with (((hp | h₁) | h₂ | hg | h₃) | h₄ | hs)
    · exact .inr (.inl (.inl hp))
    · exact .inl (source_radix k _ b _ h₁)
    · exact .inl (source_radix k _ b _ h₂)
    · exact .inr (.inl (.inr hg))
    · exact .inl (source_radix k _ b _ h₃)
    · exact .inl (source_radix k _ b _ h₄)
    · exact .inr (.inr hs)
  · have reply_eq : (Request.job b).reply ∘ child = stackRun (layoutRows ord P G B f) ans :=
      funext post
    have h := (Quest.board (j:=Request.job b) child (l:=l) (r:=r) st.1).hand prep
    rw [reply_eq] at h
    exact h

/-- Execute any legal finite address program. The number of recursive
requests is at most its pivot price; every request has exactly the same
number of records and record width as the input to this stage. -/
theorem execute_charged_typed (good : I → Tree → Prop) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (ops : List (Lag J b))
    (legal : ∀ a ∈ ops, a.legal (ranking ord))
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (hv : Manifest _ l v)
    (hgood : ∀ i k, good i (v i k)) :
    ChargedTyped (r:=r) (l:=l) ord P G B f (b:=b) good (ops.map Lag.prices).sum
      (stackRun (layoutRows ord P G B f) v)
      (stackRun (layoutRows ord P G B f) (fun i => v i ∘
        (recreation ord (P i) (G i) (B i) (f i) ops legal).symm)) := by
  have st := layoutRows_station ord P G B f hb hf hp hg hs
  induction ops generalizing v with
  | nil => exact Hopto.tarry (Fleet.keep hv st)
  | cons a rest ih =>
    let ha := legal a List.mem_cons_self
    let e i := reflect ord a ha (P i) (G i) (B i) (f i)
    let after i := v i ∘ (e i).symm
    let data := stackRun (layoutRows (b:=b) ord P G B f)
    have hafter : Manifest _ l after := hv.shift (fun i => (e i).symm)
    have head : ChargedTyped (r:=r) (l:=l) ord P G B f (b:=b) good a.prices (data v) (data after) := by
      by_cases h : a.prices = 0
      · rw [h]
        exact Hopto.tarry (instruction ord P G B f hb hf hp hg hs a ha h v hv)
      · cases a with
        | width => contradiction
        | gather => contradiction
        | pivot x y => exact pivot ord P G B f good hb hf hp hg hs x y v hv hgood
    have tail := ih (fun a h => legal a (List.mem_cons_of_mem _ h)) after hafter (fun i k => hgood i _)
    let hh := Drive.started (r:=r) (l:=l) st.1
    have start := Rip.alivePair hh (hv.lives st)
    have header : ChargedTyped (b:=b) (r:=r) (l:=l) ord P G B f good 0 (data v) r.header :=
      Hopto.tarry (Drive.fetch st.1 (hv.lives st))
    have both := header.doubleg head start hh (hafter.lives st)
    have all := both.chain tail
    simpa only [ChargedTyped, Nat.cast_zero, zero_add, List.map_cons, List.sum_cons, Nat.cast_add, data, after, e, recreation,
      Function.comp_def, Equiv.symm_trans_apply] using all

/-- The same program restricted to a specified payload representation. -/
theorem execute_charged_good (good : I → Tree → Prop) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (ops : List (Lag J b))
    (legal : ∀ a ∈ ops, a.legal (ranking ord))
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (hv : Manifest _ l v)
    (hgood : ∀ i k, good i (v i k)) :
    ChargedGood (r:=r) (l:=l) ord P G B f (b:=b) good (ops.map Lag.prices).sum
      (stackRun (layoutRows ord P G B f) v)
      (stackRun (layoutRows ord P G B f) (fun i => v i ∘
        (recreation ord (P i) (G i) (B i) (f i) ops legal).symm)) := by
  obtain ⟨uses, ok, cost, run⟩ := execute_charged_typed ord P G B f good
    hb hf hp hg hs ops legal v hv hgood
  exact ⟨uses, fun i a h => (ok i a h).1, cost, run⟩

/-- The unrestricted-payload form of the costed instruction sequence. -/
theorem execute_charged (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (ops : List (Lag J b))
    (legal : ∀ a ∈ ops, a.legal (ranking ord))
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (hv : Manifest _ l v) :
    Charged (r:=r) (l:=l) ord P G B f (b:=b) (ops.map Lag.prices).sum
      (stackRun (layoutRows ord P G B f) v)
      (stackRun (layoutRows ord P G B f) (fun i => v i ∘
        (recreation ord (P i) (G i) (B i) (f i) ops legal).symm)) := by
  obtain ⟨uses, ok, cost, run⟩ := execute_charged_good ord P G B f (fun _ _ => True)
    hb hf hp hg hs ops legal v hv (fun _ _ => trivial)
  exact ⟨uses, fun i a h => (ok i a h).1, cost, run⟩

end InterchangeAddress

end NearSquareRoot
end Computability
end OAI
