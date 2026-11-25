import OAI.Computability.NearSquareRoot.SynchronizedBatchMatching
import OAI.Computability.NearSquareRoot.SynchronizedRoutingProgram
import OAI.Computability.IntegerMultiplication.Param.Base
import OAI.Computability.NearSquareRoot.SynchronizedPlacementTape

/-! # Preparing the full routing tables of a borrowing batch from its dimensions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RoutingTable

open SynchronizedBorrowing IntegerMultiplication Code Staff Strip

/-- Start and size of batch, occupied and Fourier lengths, physical fiber count and row padding. -/
abbrev Dimensions := PlacementTape.Shape × Tally × Tally

def dimensions (b a c r : ℕ) (j : Fin 15) : Dimensions :=
  (((tally (first b j),tally (size b j)), (tally a,tally r)), tally b,tally c)

private def input (X : Type) [Codec X] : Regime X := ⟨Code.size,send,Dom.base _⟩

private theorem param {X : Type} [Codec X] (f : X → Tally) (F : Easy f) :
    Realizes (input X) (fun x => (f x).length) := by
  have h : (input X).Has id := (input X).self
  simpa only [Realizes,Function.comp_def,id_eq,recover_tally] using h.ez F

/-- Read an endpoint to put in the active list, from its side and compact pair label. -/
def readEndpoint (side : ℕ) (x : Dimensions × Tally) : Tally :=
  let p := x.1.1
  let r := p.2.2.length
  tally (endpointValue p.1.1.length p.1.2.length p.2.1.length x.1.2.2.length r side
    (x.2.length/r) (x.2.length%r))

private theorem readEndpoint_poly (side : ℕ) : Poly (readEndpoint side) := by
  let X := Dimensions × Tally
  have S := param (fun x : X => x.1.1.1.1) (by fun_prop)
  have V := param (fun x : X => x.1.1.1.2) (by fun_prop)
  have A := param (fun x : X => x.1.1.2.1) (by fun_prop)
  have R := param (fun x : X => x.1.1.2.2) (by fun_prop)
  have C := param (fun x : X => x.1.2.2) (by fun_prop)
  have I := param (fun x : Dimensions × Tally => x.2) Easy.snd
  have raw := physicalRank_realizes S V A R (I.dividing R) (((Realizes.fix side).times R).plus (I.rem R))
  exact (raw.rem A).plus ((A.plus C).times (raw.dividing A))

def prepareHeader (x : Dimensions) : Header :=
  let s := x.1
  (tally (x.2.1.length*(s.2.1.length+x.2.2.length)),
    (Iter.lineup (tally (s.1.2.length*s.2.2.length))).map fun i => (readEndpoint 0 (x,i),readEndpoint 1 (x,i)))

theorem prepareHeader_poly : Poly prepareHeader := by
  have B := param (fun x : Dimensions => x.2.1) (by fun_prop)
  have A := param (fun x : Dimensions => x.1.2.1) (by fun_prop)
  have C := param (fun x : Dimensions => x.2.2) (by fun_prop)
  have V := param (fun x : Dimensions => x.1.1.2) (by fun_prop)
  have R := param (fun x : Dimensions => x.1.2.2) (by fun_prop)
  have plen : Poly (fun x : Dimensions => tally (x.1.1.2.length*x.1.2.2.length)) := V.times R
  have slen : Poly (fun x : Dimensions => tally (x.2.1.length*(x.1.2.1.length+x.2.2.length))) :=
    B.times (A.plus C)
  exact slen.pair ((Code.Poly.identity.pair (plen.compose Iter.poly_line)).compose
    (Poly.push default [] ((readEndpoint_poly 0).pair (readEndpoint_poly 1))))

theorem prepareHeader_correct {b a c r : ℕ} (hr : 2*r ≤ 8*a) (har : a ≤ r) (j : Fin 15) :
    prepareHeader (dimensions b a c r j) =
      header (b*(a+c)) (activePairs (batchEndpoints hr har j)) := by
  unfold prepareHeader dimensions header activePairs
  simp only [tally_length,Iter.lined,List.map_ofFn,Function.comp_def,Prod.map_apply]
  congr 1
  apply congrArg List.ofFn
  funext i
  obtain ⟨⟨v,t⟩,rfl⟩ := finProdFinEquiv.surjective i
  have value (u : Fin 2) :
      readEndpoint u.val (dimensions b a c r j, tally (finProdFinEquiv (v,t)).val) =
        encodeAddress (batchEndpoints (c := c) hr har j (u,finProdFinEquiv (v,t))) := by
    unfold readEndpoint dimensions encodeAddress
    simp only [tally_length,batchEndpoints_val]
    change tally (endpointValue _ _ _ _ _ _ ((t.val + r*v.val)/r) ((t.val+r*v.val)%r)) = _
    rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt t.isLt),Nat.div_eq_of_lt t.isLt,Nat.zero_add,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt t.isLt]
  exact Prod.ext (value 0) (value 1)

/-- Uniform algorithm for the forward and inverse routing tables. Only six scalar parameters
are supplied on the input tape, regardless of the number of active or unused cells. -/
theorem batchRouting_machine :
    PolyTreeMachine size send (fun x : Dimensions => send (bothTables (prepareHeader x))) :=
  polyTreeMachine_of_BT ((prepareHeader_poly.compose bothTables_poly).on (Dom.base _)) (Dom.base _)

theorem dimensions_size (b a c r : ℕ) (j : Fin 15) (hb : 0 < b) (ha : 0 < a)
    (hr : 2*r ≤ 8*a) : Code.size (dimensions b a c r j) ≤ 32*(b*(a+c)+1) := by
  have h₁ := batchFits b j
  have hn : a+c ≤ b*(a+c) := Nat.le_mul_of_pos_left _ hb
  have hn' : b ≤ b*(a+c) := Nat.le_mul_of_pos_right _ (by omega)
  simp only [dimensions,size_prod,size_tally,tally_length]
  omega

/-- Every valid block has at most seven short axes. When each axis width is at most
20 ceiling binary logarithms, both tables are generated at polynomial cost in the
global address width by a single finite machine. -/
theorem batchRouting_width {I : Type} (k b a c r : I → ℕ) (j : I → Fin 15)
    (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i) (hr : ∀ i, 2*r i ≤ 8*a i)
    (hn : ∀ i, b i*(a i+c i) ≤ 2^(140*Nat.clog 2 (k i))) :
    let dim i := dimensions (b i) (a i) (c i) (r i) (j i)
    PolyTreeMachine k (fun i => send (dim i)) (fun i => send (bothTables (prepareHeader (dim i)))) := by
  let n i := b i*(a i+c i)
  have hnd : Dom k n := by
    refine ⟨140,2^140,fun i => (hn i).trans ?_⟩
    rw [Nat.mul_comm 140, pow_mul, ← Nat.mul_pow]
    exact Nat.pow_le_pow_left (Param.logBound _) _
  have hs := ((Dom.const k 32).mul (hnd.add (Dom.const k 1))).mono
    (fun i => dimensions_size (b i) (a i) (c i) (r i) (j i) (hb i) (ha i) (hr i))
  exact polyTreeMachine_of_BT ((prepareHeader_poly.compose bothTables_poly).on hs) hs

end ShortFourier.RoutingTable

end NearSquareRoot
end Computability
end OAI
