import OAI.Computability.NearSquareRoot.PhysicalWalshGatherPermutation
import OAI.Computability.NearSquareRoot.PhysicalWalshGatherProgram
import OAI.Computability.NearSquareRoot.BoundedProgram
import OAI.Computability.IntegerMultiplication.Code.Filter
import OAI.Computability.IntegerMultiplication.Strip.Header

/-! # Generating both position tables for a selected-bit mask

The unary header lists one destination position for each source bit.
Its inverse is read directly from a stable partition of the source ordinals.
Both tables use the increasing, least-significant-first order of mask bits.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherMask

open IntegerMultiplication Code Controlled.Reflections

/-- Unary count of occurrences of the tag in the specified prefix. -/
def countWord (b : Bool) (mask : List Bool) : Tally := ruler (mask.filter (· == b))

theorem countWord_eq (b : Bool) (mask : List Bool) : countWord b mask = tally (mask.count b) := by
  rw [← recover_tally (countWord b mask)]
  simp only [countWord,ruler_length,List.count_eq_countP,List.countP_eq_length_filter]

@[fun_prop] theorem poly_countWord (b : Bool) : Poly (countWord b) :=
  (Poly.filter (· == b) (Easy.finite _).poly).compose ((Easy.ruler Easy.identity).poly)

/-- Destination of one physical position in the stable gather. -/
def rankWord (p : List Bool × Tally) : Tally :=
  let before := (cutLists (p.2,p.1)).1
  bif Iter.pick false p then countWord true before else countWord true p.1 ++ countWord false before

@[fun_prop] theorem poly_rankWord : Poly rankWord := by
  have pre : Easy (fun p : List Bool × Tally => (cutLists (p.2,p.1)).1) :=
    (easy_cut Easy.exchange).fstCompose
  exact Poly.choose (Iter.facile false).poly (pre.poly.compose (poly_countWord true))
    (((Easy.fst.poly.compose (poly_countWord true)).pair (pre.poly.compose (poly_countWord false))).compose
      Easy.append.poly)

def ordinals (mask : List Bool) : List Tally := Iter.lineup (ruler mask)

@[fun_prop] theorem poly_ordinals : Poly ordinals := (Easy.ruler Easy.identity).poly.compose Iter.poly_line

theorem ordinals_eq (mask : List Bool) : ordinals mask = (List.finRange mask.length).map (fun i => tally i.val) := by
  simp [ordinals,Iter.lineup,List.ofFn_eq_map]

/-- Forward table obtained by an increasing scan of all source positions. -/
def forward (mask : List Bool) := polyPush rankWord (mask,ordinals mask)

@[fun_prop] theorem poly_forward : Poly forward :=
  (Poly.identity.pair poly_ordinals).compose (Poly.push [] [] poly_rankWord)

/-- The inverse permutation lists the original positions of the marked bits
followed by the original positions of the unmarked bits. -/
def backward (mask : List Bool) :=
  let tagged := zipFair false ([] : Tally) (mask,ordinals mask)
  Ribbon.read true tagged ++ Ribbon.read false tagged

@[fun_prop] theorem poly_backward : Poly backward := by
  have pairs := (Poly.identity.pair poly_ordinals).compose (easy_zip false ([] : Tally)).poly
  exact ((pairs.compose (Ribbon.easyRead true Easy.identity).poly).pair
    (pairs.compose (Ribbon.easyRead false Easy.identity).poly)).compose Easy.append.poly

private theorem rank_value (mask : List Bool) (i : Fin mask.length) :
    rankWord (mask,tally i.val) = tally (if mask.get i then (mask.take i.val).count true
      else mask.count true + (mask.take i.val).count false) := by
  unfold rankWord
  rw [Iter.search _ _ _ i.isLt]
  simp only [cutLists,tally_length,countWord_eq,Strip.Dims.mergeTally]
  change (bif mask.get i then _ else _) = _
  cases mask.get i <;> rfl

private theorem read_ordinals {K : Type} (mask : K → Bool) (address : K → Tally) (b : Bool) (l : List K) :
    Ribbon.read b (l.map (fun i => (mask i,address i))) = (l.filter (fun i => mask i == b)).map address := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases h : mask x <;> cases b <;> simpa [Ribbon.read,Ribbon.keep,h] using ih

private theorem backward_partition (mask : List Bool) :
    backward mask = (((List.finRange mask.length).filter mask.get) ++
      ((List.finRange mask.length).filter (fun i => !(mask.get i)))).map (fun i => tally i.val) := by
  have restore : (List.finRange mask.length).map mask.get = mask := by rw [← List.ofFn_eq_map,List.ofFn_get]
  have zip := fair mask.get (fun i => tally i.val) (List.finRange mask.length) false ([] : Tally)
  rw [restore,← ordinals_eq] at zip
  simp [backward,zip,read_ordinals]
  rfl

theorem forward_eq (mask : List Bool) : forward mask = table (perm mask) := by
  rw [forward,polyPush,ordinals_eq,List.map_map,table,List.ofFn_eq_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_def,rank_value,forward_rank]

theorem backward_eq (mask : List Bool) : backward mask = table (perm mask).symm := by
  rw [backward_partition,table]
  exact (inverse_list mask (fun i => tally i.val)).symm

/-- Both exact, mutually inverse tables are physically computable from one
mask by a fixed polynomial-time program. -/
theorem tables_poly : Poly (fun mask : List Bool => (table (perm mask),table (perm mask).symm)) := by
  simpa only [forward_eq,backward_eq] using poly_forward.pair poly_backward

theorem tables_has {I : Type} {r : Strip.Regime I} {mask : I → List Bool} (hm : r.Has mask) :
    r.Has (fun i => (table (perm (mask i)),table (perm (mask i)).symm)) := hm.thenDo tables_poly

/-- Encode both rulers and both tables in the form consumed by the physical
forward, grouped Walsh, and reverse permutation composition. -/
theorem control_poly : Poly (fun mask : List Bool => GatherProgram.control (mask.count true) (perm mask)) := by
  have H := (((Easy.ruler (Easy.identity (X := List Bool))).poly.pair (poly_countWord true)).pair tables_poly)
  have E (mask : List Bool) : ruler mask = tally mask.length := by simp [ruler,tally]
  simpa only [E,id_eq,countWord_eq,GatherProgram.control] using H

/-- The concrete header generator has a clock and arena polynomial in
the mask length, including the time to emit both tables. -/
theorem control_bounded : ∃ d C : ℕ,
    let budget (mask : List Bool) := C*(mask.length+1)^d
    Space.BoundedTask budget budget send
      (fun mask => send (GatherProgram.control (mask.count true) (perm mask))) := by
  have width : Dom List.length (size (X := List Bool)) := by
    refine ⟨1,2,fun mask => ?_⟩
    rw [Bits.size_word,pow_one]
    omega
  obtain ⟨b,hb,cmd⟩ := control_poly.on (q := id) width
  obtain ⟨d,C,h⟩ := width.add hb
  refine ⟨d,C,(Space.BoundedTask.of_time cmd).mono (fun m => ?_) (fun m => h m)⟩
  exact (Nat.le_add_left (b m) (size m)).trans (h m)

/-- Even the total cost of constructing the controller fits the original
record volume, uniformly over all selected sets. -/
theorem control_volume : Space.BoundedTask (fun mask : List Bool => Odd.volume mask.length)
    (fun mask => Odd.volume mask.length) send
    (fun mask => send (GatherProgram.control (mask.count true) (perm mask))) := by
  obtain ⟨d,C,h⟩ := control_bounded
  obtain ⟨D,hD⟩ := polynomial_le_multiple_array_length d
  have b (mask : List Bool) : C*(mask.length+1)^d+1 ≤ (C*D+1)*(Odd.volume mask.length+1) := by
    have e := Nat.mul_le_mul_left C (hD mask.length)
    rw [← Nat.mul_assoc] at e
    have f : 2^mask.length ≤ Odd.volume mask.length := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have g := e.trans (Nat.mul_le_mul_left (C*D) f)
    rw [Nat.succ_mul,Nat.mul_add,Nat.mul_one]
    omega
  exact h.bound (C*D+1) (C*D+1) b b

end PhysicalWalsh.GatherMask

end NearSquareRoot
end Computability
end OAI
