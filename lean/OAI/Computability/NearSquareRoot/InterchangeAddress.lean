import OAI.Computability.IntegerMultiplication.Loom.Horizon
import OAI.Computability.NearSquareRoot.InterchangeTriangular

/-!
# Tape execution of triangular address changes at arbitrary widths

The selected fields can have any common width (including a width supplied
by the parent call). The header supplies the three spectator shapes and
width, in P192's tree representation. P192's `Fleet` budget charges the
number of records times their width plus a polynomial in the header scale
per record. This term is retained for subsequent payload amortization.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port
  IntegerMultiplication.Adic IntegerMultiplication.Loom

variable {I J : Type} [DecidableEq J] {b n : ℕ} [NeZero b]
    {r : Regime I} {l : I → ℕ} (ord : J ≃ Fin n)
    (P G B : I → Dims.Tape) (f : I → ℕ)

abbrev domain (i : I) := Keys (P i) (G i) (B i) J (Block b (f i))
abbrev layoutRows (i : I) := arrays ord (line b (f i)) (P i) (G i) (B i)

omit [DecidableEq J] [NeZero b] in
theorem layoutRows_station (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) :
    Station r (layoutRows (b:=b) ord P G B f) := by
  have u := (Told.carrier hb f hf).stacked n
  have hts : Station r (fun i => threads (line b (f i)) ord) := by
    have eq (i : I) : (threads (line b (f i)) ord).count =
        (Dims.layout (Rack (field b (f i)) n)).count :=
      (undye (line b (f i)) ord (Adopt.same _)).cost
    unfold Station
    simp_rw [eq]
    exact u.station
  exact hp.station.product (hts.product (hg.station.product (hts.product hs.station)))

theorem instruction (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (a : Lag J b)
    (ha : a.legal (ranking ord)) (ha0 : a.prices = 0)
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (hv : Manifest _ l v) :
    Fleet r l (layoutRows ord P G B f) (layoutRows ord P G B f) v
      (fun i => v i ∘ (reflect ord a ha (P i) (G i) (B i) (f i)).symm) := by
  have hfield := Told.carrier hb f hf
  cases a with
  | width s diag =>
    exact sizeUp hb f (fun i => oneStop ord s (P:=(P i)) (G:=(G i)) (B:=(B i))) diag hf
      (hfield.stair ord hp hg s) (hfield.lounge ord hg hs s) _ hv
  | gather s t sub =>
    exact shiftUp hb f (fun i => twoStops ord t s ha (P:=(P i)) (G:=(G i)) (B:=(B i))) sub hf
      (hfield.stair ord hp hg t) (hfield.corridor ord hg t s) (hfield.lounge ord hg hs s) _ hv
  | pivot => contradiction

/-- Lower triangular instruction sequences require only fixed nonrecursive
stack programs for arbitrary `f` and varying spectator ranges. -/
theorem execute_free (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (program : List (Lag J b))
    (legal : ∀ a ∈ program, a.legal (ranking ord) ∧ a.prices = 0)
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (hv : Manifest _ l v) :
    Fleet r l (layoutRows ord P G B f) (layoutRows ord P G B f) v
      (fun i => v i ∘ (recreation ord (P i) (G i) (B i) (f i) program
        (fun a h => (legal a h).1)).symm) := by
  induction program generalizing v with
  | nil =>
    exact Fleet.keep hv (layoutRows_station ord P G B f hb hf hp hg hs)
  | cons a rest ih =>
    let h := legal a List.mem_cons_self
    let e i := reflect ord a h.1 (P i) (G i) (B i) (f i)
    have head := instruction ord P G B f hb hf hp hg hs a h.1 h.2 v hv
    have tail := ih (fun a h => legal a (List.mem_cons_of_mem _ h))
      (fun i => v i ∘ (e i).symm) (hv.shift (fun i => (e i).symm))
    exact Fleet.chain head tail (fun _ => rfl)

/-- The compiled address permutation has both an exact fieldwise identity
and a certificate for moving every input record to its destination. -/
theorem execute_triangular {d : ℕ} (slot : Fin d → Spot J)
    (diag : Fin d → Span b) (sub : Fin d → Fin d → Pinpoint b)
    (hinj : Function.Injective slot)
    (hord : ∀ i j, i < j → Lag.early (ranking ord) (slot i) (slot j))
    (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) :
    ∃ perm : (i : I) → Equiv.Perm (domain (J:=J) (b:=b) P G B f i),
      (∀ i x, watcher (perm i x) = watcher x ∧
        (∀ k, hear (chase (perm i x)) (slot k) =
          InterchangeTriangular.rowValue slot diag sub (f i) (chase x) k) ∧
        (∀ a, (∀ k, a ≠ slot k) → hear (chase (perm i x)) a = hear (chase x) a)) ∧
      ∀ v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree, Manifest _ l v →
        Fleet r l (layoutRows ord P G B f) (layoutRows ord P G B f) v
          (fun i => v i ∘ (perm i).symm) := by
  obtain ⟨ops, hleg, heval⟩ := InterchangeTriangular.compile slot diag sub (ranking ord) hinj hord
  let perm i := recreation ord (P i) (G i) (B i) (f i) ops (fun a ha => (hleg a ha).1)
  refine ⟨perm, ?_, execute_free ord P G B f hb hf hp hg hs ops hleg⟩
  intro i x
  have h := fore ord ops (fun a ha => (hleg a ha).1) x
  have hd := congrArg Prod.fst h
  have hw := congrArg Prod.snd h
  change chase (perm i x) = _ at hd
  refine ⟨hw, ?_⟩
  rw [hd]
  exact heval (f i) (chase x)

end InterchangeAddress

end NearSquareRoot
end Computability
end OAI
