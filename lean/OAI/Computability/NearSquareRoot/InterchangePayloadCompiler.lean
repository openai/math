import OAI.Computability.NearSquareRoot.InterchangePayloadBank
import OAI.Computability.NearSquareRoot.InterchangePayloadSeed
import OAI.Computability.NearSquareRoot.InterchangeBankRun
import OAI.Computability.NearSquareRoot.InterchangeMatrixGood

/-!
# The script compiler on arrays with a packed payload axis

Each address move in a script induces the product of its record permutation
with the identity on payload positions. Its P192 requests contain valid
packed records. Pointwise tables include nullary operations, using the
payload ruler supplied by the same parent descriptor.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayloadBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeBank

variable {I A B F H Y M : Type} {X D : I → Type} {r : Regime I} {l : I → ℕ}
    {job : Job Y} {zone : I → Y → Prop}

theorem table [Finite A] [Finite F]
    (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (widthReady : Rip r (fun i => (records i).count) l r.header (fun i => send (tally (payload i).count)))
    (rows : Series A) (out : Series B) (src : F → Tree) (dst : H → Tree)
    (inj : Function.Injective src) (v : (i:I) → A → X i × D i → F)
    (τ : (A → F) → B → H) :
    Drive r (fun i => (records i).count) l (render records payload rows src v)
      (render records payload out dst (fun i b k => τ (fun a => v i a k) b)) := by
  by_cases hn : Nonempty A
  · exact table_nonempty records hs payload h rows out src dst inj v τ
  let z : A → F := fun a => (hn ⟨a⟩).elim
  have eq (i : I) (k : X i × D i) : (fun a => v i a k) = z := funext fun a => (hn ⟨a⟩).elim
  simp_rw [eq]
  exact InterchangePayload.constantRows records payload hs (fun _ => le_rfl) h widthReady out
    (dst ∘ τ z) _ (alive records hs payload h rows src v)

/-- Lift an address move to a stream of contiguous, unpermuted payloads. -/
def withPayload (D : I → Type) (θ : (i:I) → M → Equiv.Perm (X i)) (i : I) (m : M) :
    Equiv.Perm (X i × D i) := (θ i m).prodCongr (Equiv.refl _)

/-- Instance of the finite-script compiler with one charged move per
physical row. Semantic points include the payload coordinate. -/
def compiler [Finite F] (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (widthReady : Rip r (fun i => (records i).count) l r.header (fun i => send (tally (payload i).count)))
    (src : F → Tree) (inj : Function.Injective src)
    (θ : (i:I) → M → Equiv.Perm (X i)) (price : M → ℕ)
    (single : ∀ m (x : (i:I) → X i → Tree), Manifest X l x →
      (∀ i a, Good payload src i (x i a)) →
      Hopto job r (fun i => (records i).count) l zone (price m)
        (together r.header (stackRun records x)) (stackRun records (fun i => x i ∘ (θ i m).symm))) :
    Compiler r (fun i => (records i).count) l job zone F (withPayload D θ) price 1 where
  render rows x := render records payload rows src x
  positive := hs.1
  alive rows x := alive records hs payload h rows src x
  pointwise rows out x τ := table records hs payload h widthReady rows out src src inj x τ
  route rows out x sel moves := by
    simpa [withPayload, Prod.map] using
      (route records hs payload h src θ price single rows out x sel moves)

variable {J : Type} [DecidableEq J] {p n : ℕ} [NeZero p]

/-- Instantiate the compiler with actual legal address instructions.
The complete request zone certifies the correct field width, row count,
record-width bound, payload delimiter structure and alphabet. -/
noncomputable def programCompiler [Finite F] (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f : I → ℕ)
    (hp : 2 ≤ p) (hf : r.Has (tally ∘ f)) (hP : Told r P) (hG : Told r G) (hB : Told r B)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (widthReady : Rip r (countRows (b:=p) ord P G B f) l r.header (fun i => send (tally (payload i).count)))
    (src : F → Tree) (inj : Function.Injective src)
    (ops : M → List (Lag J p)) (legal : ∀ m a, a ∈ ops m → a.legal (ranking ord)) :
    Compiler r (countRows (b:=p) ord P G B f) l (Request.job p)
      (fun i q => allowed f (countRows (b:=p) ord P G B f) l i q ∧ ∀ k, Good payload src i (q.contents k))
      F (withPayload D (fun i m => recreation ord (P i) (G i) (B i) (f i) _ (legal m)))
      (fun m => ((ops m).map Lag.prices).sum) 1 :=
  compiler (layoutRows (b:=p) ord P G B f) (layoutRows_station ord P G B f hp hf hP hG hB)
    payload h widthReady src inj _ _ (fun m =>
      execute_charged_good ord P G B f (Good payload src) hp hf hP hG hB (ops m) (legal m))

end InterchangePayloadBank

end NearSquareRoot
end Computability
end OAI
