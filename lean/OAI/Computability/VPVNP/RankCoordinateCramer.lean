import OAI.Computability.VPVNP.RankCoordinateDimension
import OAI.Computability.VPVNP.RankQueryStackInterpretation
import OAI.Computability.VPVNP.RankQueryStackEngineSpace
import OAI.Computability.VPVNP.SliceArithmeticEncoding
import OAI.Computability.VPVNP.SliceArithmeticInverseCall

/-! # Two top-degree determinant queries for a greedy coordinate

Appendix D.2 obtains a coordinate from a nonsingular minor and the minor with
one row replaced. Their top pencil coefficients have the same sign. Division
can therefore use the scalar returned by each Schur computation directly,
including in characteristic two.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate

open Polynomial SliceArithmetic RAMTape UniversalCountStack

variable {r n m : ℕ}

/-- The Schur evaluator for the outer top coefficient of a constant matrix. -/
def topPencil {R : Type*} [CommRing R] (A : Matrix (Fin r) (Fin r) R) : R :=
  SchurKey.compute (fun i j z => if z = 0 then A i j else 0) r 0

/-- The Schur output differs from the determinant by the same sign at every
matrix of the given order. -/
theorem sign_mul_topPencil {R : Type*} [CommRing R] (A : Matrix (Fin r) (Fin r) R) :
    (-1 : R)^r * topPencil A = A.det := by
  nontriviality R
  let M := A.map C
  have entries (i j : Fin r) (z : ℕ) : (if z = 0 then A i j else 0) = (M i j).coeff z := by
    simp [M, coeff_C]
  rw [topPencil, SchurKey.compute_correct M _ entries]
  have htop : M.charpolyRev.coeff r = M.charpoly.coeff 0 := by
    rw [← M.reverse_charpoly, coeff_reverse, M.charpoly_natDegree_eq_dim, Fintype.card_fin]
    simp
  rw [htop]
  have hs := M.det_eq_sign_charpoly_coeff
  rw [Fintype.card_fin, ← show C ((-1 : R)^r) = (-1 : R[X])^r by simp] at hs
  have h := congrArg (fun z : R[X] => z.coeff 0) hs
  rw [coeff_C_mul] at h
  change (C.mapMatrix A).det.coeff 0 = _ at h
  rw [← C.map_det, coeff_C_zero] at h
  exact h.symm

/-- Two machine outputs can be divided without correcting either sign. This
also holds after mapping the executable scalar ring into the advised field. -/
theorem topPencil_div_map {R K : Type*} [CommRing R] [Field K] (f : R →+* K)
    (N D : Matrix (Fin r) (Fin r) R) :
    f (topPencil N) / f (topPencil D) = (N.map f).det / (D.map f).det := by
  have hn := congrArg f (sign_mul_topPencil N)
  have hd := congrArg f (sign_mul_topPencil D)
  simp only [map_mul, map_pow, map_neg, map_one, RingHom.map_det] at hn hd
  change _ = (f.mapMatrix N).det / (f.mapMatrix D).det
  rw [← hn, ← hd, mul_div_mul_left _ _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))]

/-- The canonical numerator for a selected-row representation. -/
def replacedMinor {K : Type*} (B : Matrix (Fin r) (Fin m) K) (cols : Fin r → Fin m)
    (target : Fin m → K) (i : Fin r) := (B.submatrix id cols).updateRow i (target ∘ cols)

/-- Packed-ring queries for the two minors produce the scalar appearing in the
greedy coordinate formula. -/
theorem topPencil_div_rowCoordinate {R K : Type*} [CommRing R] [Field K] (f : R →+* K)
    (N D : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin r) (Fin m) K) (cols : Fin r → Fin m)
    (target : Fin m → K) (i : Fin r) (hn : N.map f = replacedMinor B cols target i)
    (hd : D.map f = B.submatrix id cols) :
    f (topPencil N) / f (topPencil D) = rowCoordinateQuery squareDetQuery B cols target i := by
  rw [topPencil_div_map, hn, hd, rowCoordinateQuery, squareDetQuery_eq, squareDetQuery_eq]
  rfl

namespace Cramer

/-- Keep the numerator outside the inverse's entire workspace. A second external
stack is used temporarily to copy it into the multiplier's query operand. -/
inductive Extra where
  | numerator | scratch
  deriving DecidableEq

instance : Fintype Extra := ⟨{.numerator, .scratch}, by intro i; cases i <;> simp⟩

/-- Stack ports for inversion and multiplication together with the numerator, denominator, and
copying workspace. -/
abbrev Port := InverseCall.Port ⊕ Extra

private def mulPort (i : MultiplyCall.Port) : Port := .inl (.inl i)

private theorem mulPort_injective : Function.Injective mulPort :=
  Sum.inl_injective.comp Sum.inl_injective

/-- Boundary of the quotient operation. The input denominator and numerator
are kept on distinct read-only ports. The output is the multiplier accumulator. -/
def frame (p e w : ℕ) (cb denominator numerator acc : List Bool) : Stacks Port :=
  Sum.elim (InverseCall.frame p e w cb denominator (p^e - 2).bits.reverse [] acc [])
    fun extra => match extra with | .numerator => numerator | .scratch => []

/-- Pack the extension-field coefficient vector as fixed-width binary limbs for the quotient
routine. -/
abbrev digits {p e : ℕ} (w : ℕ) (a : Vector p e) := SliceArithmeticRound.packed w (List.ofFn a)

private def copyNumerator : FiniteRoutine Port :=
  SuccessorFields.prependCopy (.inr .numerator) (mulPort (.inr .query)) (.inr .scratch)

/-- Invert the denominator in the polynomial basis and multiply by the saved numerator. -/
def quotientCall (inv : FiniteRoutine InverseCall.Port) : FiniteRoutine Port :=
  ((inv.onPorts Sum.inl).followedBy copyNumerator).followedBy (MultiplyCall.machine.onPorts mulPort)

/-- Only the inverse, one operand copy, and one multiplication are charged here. -/
def quotientClock (e w inverseClock : ℕ) := inverseClock + (5*(e*w)+2) + MultiplyCall.callCap e w

variable {p e w : ℕ} [NeZero p]

/-- Install an inverse run in the quotient bank and perform the remaining
arithmetic by the literal finite multiplication machine. -/
theorem quotientCall_runs (inv : FiniteRoutine InverseCall.Port) (he : 0 < e)
    (hw : Word.workingWidth p ≤ w) (c num den : Vector p e) {it : ℕ}
    (hinv : inv.Runs it
      (InverseCall.frame p e w (digits w c) (digits w den) (p^e-2).bits.reverse [] [] [])
      (InverseCall.frame p e w (digits w c) (digits w den) (p^e-2).bits.reverse []
        (digits w (inverse c den)) [])) :
    ∃ t ≤ quotientClock e w it, (quotientCall inv).Runs t
      (frame p e w (digits w c) (digits w den) (digits w num) [])
      (frame p e w (digits w c) (digits w den) (digits w num) (digits w (mul c num (inverse c den)))) := by
  let f (acc : List Bool) := frame p e w (digits w c) (digits w den) (digits w num) acc
  let ib := digits w (inverse c den)
  let nb := digits w num
  let staged := Function.update (f ib) (mulPort (.inr .query)) nb
  have start : (inv.onPorts Sum.inl).Runs it (f []) (f ib) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective hinv (fun _ => rfl) (fun _ => rfl)
    rintro (k | k) hout
    · exact (hout k rfl).elim
    · rfl
  have copied : copyNumerator.Runs (5*(e*w)+2) (f ib) staged := by
    have h := SuccessorFields.prependCopy_runs (K := Port) (.inr .numerator) (mulPort (.inr .query))
      (.inr .scratch) (by decide) (by decide) (by decide) (f ib) rfl
    change copyNumerator.Runs (5*nb.length+2) (f ib) (Function.update (f ib) (mulPort (.inr .query))
      (nb ++ [])) at h
    simpa only [staged, List.append_nil, nb, digits, SliceArithmeticRound.packed_length, List.length_ofFn]
      using h
  obtain ⟨m, hm, hmul⟩ := MultiplyCall.machine_runs he hw c num (inverse c den)
  have finish : (MultiplyCall.machine.onPorts mulPort).Runs m staged (f (digits w (mul c num (inverse c den)))) := by
    apply FiniteRoutine.runs_onPorts_framed _ mulPort_injective hmul
    · rintro (k | k)
      · rfl
      · cases k <;> rfl
    · rintro (k | k) <;> rfl
    · rintro ((k | k) | k) hout
      · exact (hout k rfl).elim
      · rfl
      · rfl
  exact ⟨_, by unfold quotientClock; omega, (start.followedBy copied).followedBy finish⟩


section Field

variable {q deg width : ℕ} [Fact q.Prime] [NeZero deg] (c : Vector q deg)
variable [Fact (Irreducible (modulus c))]

/-- Native result of the two top pencil computations and the quotient call. -/
def minorQuotient (N D : Matrix (Fin r) (Fin r) (Scalar c)) : Vector q deg :=
  mul c (topPencil N).digits (inverse c (topPencil D).digits)

theorem minorQuotient_value (N D : Matrix (Fin r) (Fin r) (Scalar c)) :
    value (modulus c) (minorQuotient c N D) =
      (N.map (Scalar.interpretation c)).det / (D.map (Scalar.interpretation c)).det := by
  rw [minorQuotient, value_mul, value_inverse, ← div_eq_mul_inv]
  exact topPencil_div_map (Scalar.interpretation c) N D

theorem minorQuotient_rowCoordinate (N D : Matrix (Fin r) (Fin r) (Scalar c))
    (B : Matrix (Fin r) (Fin m) (AdjoinRoot (modulus c))) (cols : Fin r → Fin m)
    (target : Fin m → AdjoinRoot (modulus c)) (i : Fin r)
    (hN : N.map (Scalar.interpretation c) = replacedMinor B cols target i)
    (hD : D.map (Scalar.interpretation c) = B.submatrix id cols) :
    value (modulus c) (minorQuotient c N D) = rowCoordinateQuery squareDetQuery B cols target i := by
  rw [minorQuotient, value_mul, value_inverse, ← div_eq_mul_inv]
  exact topPencil_div_rowCoordinate (Scalar.interpretation c) N D B cols target i hN hD

variable [DecidableEq (AdjoinRoot (modulus c))]

/-- Specialization to the two matrices selected by the greedy scans. -/
theorem minorQuotient_greedy (A : Matrix (Fin n) (Fin m) (AdjoinRoot (modulus c)))
    (target : Fin m → AdjoinRoot (modulus c)) (i : Fin (rankQuery A))
    (N D : Matrix (Fin (rankQuery A)) (Fin (rankQuery A)) (Scalar c))
    (hN : N.map (Scalar.interpretation c) = replacedMinor (greedyRowBasis A)
      (coordinateColumns _ (greedyRowBasis_fullRank A)) target i)
    (hD : D.map (Scalar.interpretation c) = (greedyRowBasis A).submatrix id
      (coordinateColumns _ (greedyRowBasis_fullRank A))) :
    value (modulus c) (minorQuotient c N D) = greedyCoordinateQuery A target i :=
  minorQuotient_rowCoordinate c N D _ _ target i hN hD

/-- The monomial-basis ordinal is offset past the independent equation rows. -/
theorem minorQuotient_suffix {w : ℕ} (W : Matrix (Fin w) (Fin m) (AdjoinRoot (modulus c)))
    (M : Matrix (Fin n) (Fin m) (AdjoinRoot (modulus c))) (target : Fin m → AdjoinRoot (modulus c))
    (i : Fin (suffixDimension W M)) (N D : Matrix (Fin (rankQuery (appendRows W M)))
      (Fin (rankQuery (appendRows W M))) (Scalar c))
    (hN : N.map (Scalar.interpretation c) = replacedMinor (greedyRowBasis (appendRows W M))
      (coordinateColumns _ (greedyRowBasis_fullRank _)) target (combinedOrdinal W M i))
    (hD : D.map (Scalar.interpretation c) = (greedyRowBasis (appendRows W M)).submatrix id
      (coordinateColumns _ (greedyRowBasis_fullRank _))) :
    value (modulus c) (minorQuotient c N D) = greedyCoordinateQuery (appendRows W M) target
      (combinedOrdinal W M i) :=
  minorQuotient_greedy c _ target _ N D hN hD

end Field

variable {q deg width : ℕ} [Fact q.Prime] [NeZero deg]

/-- Concrete finite quotient program, with the inverse obtained by binary powering. -/
def divide : FiniteRoutine Port := quotientCall InverseCall.machine

/-- Clock bound for the finite-field division, including inversion and multiplication at the
stated degree and width. -/
def divideClock (e w : ℕ) := quotientClock e w (InverseCall.callCap e w)

theorem divideClock_le (e w : ℕ) : divideClock e w ≤ 7100*(e+1)^3*(w+1)^3 := by
  have inv := InverseCall.callCap_le e w
  have mul := MultiplyCall.callCap_le e w
  unfold divideClock quotientClock
  calc
    _ ≤ 5000*(e+1)^3*(w+1)^3 + (5*(e*w)+2) + 2000*(e+1)^2*(w+1)^2 := by omega
    _ ≤ _ := by ring_nf; omega

/-- Division by the determinant takes polynomial time and preserves both input
scalars and all advised field data. -/
theorem divide_runs (hw : Word.workingWidth q ≤ width) (c num den : Vector q deg) :
    ∃ t ≤ divideClock deg width, divide.Runs t (frame q deg width (digits width c) (digits width den)
      (digits width num) []) (frame q deg width (digits width c) (digits width den) (digits width num)
        (digits width (mul c num (inverse c den)))) := by
  obtain ⟨it, hi, hinv⟩ := InverseCall.machine_runs (NeZero.pos deg) hw c den
  obtain ⟨t, ht, h⟩ := quotientCall_runs InverseCall.machine (NeZero.pos deg) hw c num den hinv
  exact ⟨t, ht.trans (by unfold divideClock quotientClock; omega), h⟩

omit [NeZero deg] in
/-- At a clean field boundary every live limb buffer and the exponent advice
have polynomial length. -/
theorem frame_length (hw : Word.workingWidth q ≤ width) (c num den : Vector q deg) (k : Port) :
    (frame q deg width (digits width c) (digits width den) (digits width num) [] k).length ≤
      (deg+1)*(width+1) := by
  have hexp : (q^deg-2).bits.length ≤ deg*width := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    calc
      q ^ deg - 2 < q ^ deg := by have := Nat.pow_pos (Fact.out : q.Prime).pos (n := deg); omega
      _ ≤ (2 ^ width) ^ deg := Nat.pow_le_pow_left (Word.modulus_lt hw).le _
      _ = 2 ^ (deg*width) := by rw [← pow_mul, Nat.mul_comm]
  rcases k with ((inner | ext) | extra) | extra
  · exact Nat.zero_le _
  · cases ext <;> simp [frame, InverseCall.frame, MultiplyCall.clean, MultiplyCall.external, digits] <;> nlinarith
  · cases extra <;> simp [frame, InverseCall.frame, digits] <;> nlinarith
  · cases extra <;> simp [frame, digits]; nlinarith

/-- Concrete Cramer program consuming the two determinant subqueries. -/
def machine (den num : FiniteRoutine Port) := (den.followedBy num).followedBy divide

theorem machine_runs (den num : FiniteRoutine Port) (c : Vector q deg) (hw : Word.workingWidth q ≤ width)
    (N D : Matrix (Fin r) (Fin r) (Scalar c)) {initial middle : Stacks Port} {cap nd nn : ℕ}
    (first : den.BoundedRun cap nd initial middle)
    (second : num.BoundedRun cap nn middle (frame q deg width (digits width c)
      (digits width (topPencil D).digits) (digits width (topPencil N).digits) []))
    (room : (deg+1)*(width+1) + divideClock deg width ≤ cap) :
    ∃ t ≤ nd + nn + divideClock deg width, (machine den num).BoundedRun cap t initial
      (frame q deg width (digits width c) (digits width (topPencil D).digits)
        (digits width (topPencil N).digits) (digits width (minorQuotient c N D))) := by
  obtain ⟨t, ht, h⟩ := divide_runs hw c (topPencil N).digits (topPencil D).digits
  have bounded := spaceRun_of_steps h fun k => (Nat.add_le_add (frame_length hw c _ _ k) ht).trans room
  exact ⟨_, Nat.add_le_add_left ht _, (first.followedBy second).followedBy bounded⟩


namespace SchurPair

/-- Separate frame stacks for the two root calls, and a bank for their field
arithmetic. The quotient reads the two engine result ports directly. -/
abbrev Host (K L : Type) := Engine.Port K ⊕ (Engine.Port L ⊕ Port)

instance {K L : Type} [DecidableEq K] [DecidableEq L] : DecidableEq (Host K L) := by
  letI : DecidableEq Port := inferInstance
  letI : DecidableEq (Engine.Port L ⊕ Port) := inferInstance
  exact inferInstanceAs (DecidableEq (Engine.Port K ⊕ (Engine.Port L ⊕ Port)))

/-- Combine the denominator engine, numerator engine, and quotient arithmetic into one disjoint
physical bank. -/
def host {K L : Type} (d : Stacks (Engine.Port K)) (n : Stacks (Engine.Port L)) (q : Stacks Port) :
    Stacks (Host K L) := Sum.elim d (Sum.elim n q)

/-- Wire the denominator and numerator to the actual output stacks of their
Schur engines. All other quotient ports have their own storage. -/
def quotientPort {K L : Type} : Port → Host K L
  | .inl (.inr .base) => .inl .result
  | .inr .numerator => .inr (.inl .result)
  | j => .inr (.inr j)

private theorem quotientPort_injective {K L : Type} :
    Function.Injective (quotientPort (K := K) (L := L)) := by
  rintro ((a | a) | a) ((b | b) | b) h
  all_goals try cases a <;> cases b <;> simp_all [quotientPort]

private def leftPort {K L : Type} (k : Engine.Port K) : Host K L := .inl k
private def rightPort {K L : Type} (k : Engine.Port L) : Host K L := .inr (.inl k)

/-- Run the two Schur determinant engines and divide their returned coefficients to obtain the
Cramer coordinate. -/
def query {K L : Type} (a : Engine.Actions K) (b : Engine.Actions L) : FiniteRoutine (Host K L) :=
  ((((FiniteRoutine.ofRoutine (Engine.routine a)).onPorts leftPort).followedBy
    ((FiniteRoutine.ofRoutine (Engine.routine b)).onPorts rightPort))).followedBy
    (divide.onPorts quotientPort)

private theorem quotient_frame {K L : Type} (d : Stacks (Engine.Port K)) (n : Stacks (Engine.Port L))
    (cb acc : List Bool) (q e w : ℕ) (i : Port) :
    host d n (frame q e w cb [] [] acc) (quotientPort i) = frame q e w cb (d .result) (n .result) acc i := by
  rcases i with ((k | k) | k) | k
  · rfl
  · cases k <;> rfl
  · cases k <;> rfl
  · cases k <;> rfl

private theorem quotient_outside {K L : Type} (d : Stacks (Engine.Port K)) (n : Stacks (Engine.Port L))
    (q e w : ℕ) (cb a b : List Bool) (i : Host K L) (outside : ∀ k, quotientPort k ≠ i) :
    host d n (frame q e w cb [] [] a) i = host d n (frame q e w cb [] [] b) i := by
  rcases i with k | k | ((k | k) | k) | k
  · rfl
  · rfl
  · rfl
  · cases k <;> first | rfl | exact (outside (.inl (.inl (.inr .acc))) rfl).elim
  · cases k <;> rfl
  · cases k <;> rfl

/-- Run both literal determinant engines. At the boundary their returned
scalars are already located at the inverse's base and the multiplier's
numerator, so no field-element copy from the engine output is required. -/
theorem query_runs {K L : Type} [DecidableEq K] [DecidableEq L]
    (a : Engine.Actions K) (b : Engine.Actions L) (c : Vector q deg) (hw : Word.workingWidth q ≤ width)
    (N D : Matrix (Fin r) (Fin r) (Scalar c)) {d₀ d₁ : Stacks (Engine.Port K)}
    {n₀ n₁ : Stacks (Engine.Port L)} {cap td tn : ℕ}
    (hd : (FiniteRoutine.ofRoutine (Engine.routine a)).BoundedRun cap td d₀ d₁)
    (hn : (FiniteRoutine.ofRoutine (Engine.routine b)).BoundedRun cap tn n₀ n₁)
    (hD : d₁ .result = digits width (topPencil D).digits)
    (hN : n₁ .result = digits width (topPencil N).digits)
    (room : (deg+1)*(width+1) + divideClock deg width ≤ cap) :
    ∃ t ≤ td+tn+divideClock deg width, (query a b).BoundedRun cap t
      (host d₀ n₀ (frame q deg width (digits width c) [] [] []))
      (host d₁ n₁ (frame q deg width (digits width c) [] [] (digits width (minorQuotient c N D)))) := by
  let blank := frame q deg width (digits width c) [] [] []
  have blank_cap (k : Port) : (blank k).length ≤ cap := by
    have h := frame_length hw c (topPencil N).digits (topPencil D).digits k
    apply (le_trans ?_ h).trans ((Nat.le_add_right _ _).trans room)
    rcases k with ((j | j) | j) | j
    · exact le_rfl
    · cases j <;> exact le_rfl
    · cases j <;> first | exact le_rfl | exact Nat.zero_le _
    · cases j <;> first | exact le_rfl | exact Nat.zero_le _
  have dcap (i : Host K L) : (host d₀ n₀ blank i).length ≤ cap := by
    rcases i with k | k | k
    · exact hd.initial_cap k
    · exact hn.initial_cap k
    · exact blank_cap k
  have left := hd.onPorts (ports := leftPort) Sum.inl_injective (host d₀ n₀ blank) (fun i _ => dcap i)
  have left_eq (d : Stacks (Engine.Port K)) : installStacks leftPort (host d₀ n₀ blank) d = host d n₀ blank := by
    refine installStacks_frame (ports := leftPort) (base := host d₀ n₀ blank) (target := host d n₀ blank)
      Sum.inl_injective (fun _ => rfl) ?_
    rintro (k | k) h
    · exact (h k rfl).elim
    · rfl
  rw [left_eq, left_eq] at left
  have rinj : Function.Injective (rightPort (K := K) (L := L)) := Sum.inr_injective.comp Sum.inl_injective
  have right := hn.onPorts (ports := rightPort) rinj (host d₁ n₀ blank) (fun i _ => left.final_cap i)
  have right_eq (n : Stacks (Engine.Port L)) : installStacks rightPort (host d₁ n₀ blank) n = host d₁ n blank := by
    refine installStacks_frame (base := host d₁ n₀ blank) (target := host d₁ n blank) rinj (fun _ => rfl) ?_
    rintro (k | k | k) h
    · rfl
    · exact (h k rfl).elim
    · rfl
  rw [right_eq, right_eq] at right
  obtain ⟨t, ht, divRun⟩ := divide_runs hw c (topPencil N).digits (topPencil D).digits
  have bound := spaceRun_of_steps divRun fun k => (Nat.add_le_add (frame_length hw c _ _ k) ht).trans room
  have last := FiniteRoutine.BoundedRun.onPorts quotientPort_injective (host d₁ n₁ blank) bound
    (fun i _ => right.final_cap i)
  have heq (acc : List Bool) : installStacks quotientPort (host d₁ n₁ blank)
      (frame q deg width (digits width c) (digits width (topPencil D).digits) (digits width (topPencil N).digits) acc) =
        host d₁ n₁ (frame q deg width (digits width c) [] [] acc) := by
    apply installStacks_frame quotientPort_injective
    · intro i
      rw [← hD, ← hN]
      exact quotient_frame d₁ n₁ _ acc _ _ _ i
    · exact fun i outside => quotient_outside d₁ n₁ q deg width _ acc [] i outside
  rw [heq, heq] at last
  exact ⟨_, Nat.add_le_add_left ht _, (left.followedBy right).followedBy last⟩

/-- Scalar entry oracle for the constant coefficient matrix of a pencil. -/
def constantEntries {R : Type*} [Zero R] (M : Matrix (Fin r) (Fin r) R) : Entry r R :=
  fun i j z => if z = 0 then M i j else 0

/-- Depth allowance for a top-degree Schur query on an `r` by `r` minor. -/
abbrev depth (r : ℕ) := Nat.clog 2 r + 4 + Nat.clog 2 r
/-- Bound the determinant's instruction count using its descriptor-tree arity, depth, and
per-step cost. -/
abbrev clock (r addr width deg budget descTime : ℕ) :=
  (5 + 6*SchurKey.arityBound r r 0)^(depth r + 1)*Engine.boundedStepTime descTime budget addr width deg + 1
/-- Bound the peak stack height of the determinant engine, including suspended frames and the
entry reader. -/
abbrev space (r addr width deg budget auxBound descSpace : ℕ) :=
  Engine.boundedSpace descSpace auxBound (depth r) budget addr width deg

/-- Initialize a determinant query at its top-degree root with an empty stack of suspended
frames. -/
abbrev entryBank {K : Type} (c : Vector q deg) (r addr width : ℕ) (aux : Stacks K) :=
  Engine.atControl (c := c) addr width (.enter (SchurKey.root (n := r) (Fin.last r) (Fin.last 0))) [] aux

/-- The determinant engine's return configuration holds its scalar answer and an empty stack of
frames. -/
abbrev resultBank {K : Type} (c : Vector q deg) (r addr width : ℕ) (v : Scalar c) (aux : Stacks K) :=
  Engine.atControl addr width (.returned v) ([] : List (Engine.F r r 0 c)) aux

/-- Install the bounded Schur engine at the top pencil coefficient. Its result is
already encoded at the limb width used by the field arithmetic routines. -/
theorem topPencil_runs {K : Type} [DecidableEq K] (c : Vector q deg)
    (M : Matrix (Fin r) (Fin r) (Scalar c)) (actions : Engine.Actions K)
    {addr width budget auxBound descTime descSpace : ℕ} {ready : Stacks K → Prop} {pending : SchurKey r r 0 → Stacks K → Prop}
    (spec : Engine.Contracts actions (SchurKey.program (U := r) (Z := 0) (constantEntries M))
      addr width budget (SchurKey.arityBound r r 0) ready pending descTime)
    (desc : Engine.DescribeBounded actions (SchurKey.program (U := r) (Z := 0) (constantEntries M))
      addr width descTime descSpace (depth r) ready)
    (bound : ∀ s, ready s → ∀ k, (s k).length ≤ auxBound) (aux : Stacks K) (ha : ready aux) :
    ∃ t ≤ clock r addr width deg budget descTime, ∃ out, ready out ∧
      (FiniteRoutine.ofRoutine (Engine.routine actions)).BoundedRun (space r addr width deg budget auxBound descSpace) t
        (entryBank c r addr width aux) (resultBank c r addr width (topPencil M) out) := by
  have he (i j : Fin r) (z : ℕ) : constantEntries M i j z = (M.map C i j).coeff z := by
    simp [constantEntries, coeff_C, Matrix.map_apply]
  obtain ⟨t, ht, out, ho, run⟩ := Engine.eval_root_bounded spec desc bound (M.map C) he (Fin.last r) (Fin.last 0) aux ha
  refine ⟨t, ht, out, ho, ?_⟩
  have eq : topPencil M = ((M.map C).charpolyRev.coeff r).coeff 0 :=
    SchurKey.compute_correct (M.map C) _ he r 0
  rw [eq]
  exact run

/-- Instantiating the two Schur calls, the concrete inverse and the final
multiplication gives the packed Cramer quotient with a common polynomial
space cap. The two ready auxiliary banks are returned separately. -/
theorem native_runs {K L : Type} [DecidableEq K] [DecidableEq L] (c : Vector q deg)
    (N D : Matrix (Fin r) (Fin r) (Scalar c)) (a : Engine.Actions K) (b : Engine.Actions L)
    {addr width budget auxBound descTime descSpace : ℕ} (hw : Word.workingWidth q ≤ width)
    {readyD : Stacks K → Prop} {readyN : Stacks L → Prop}
    {pendingD : SchurKey r r 0 → Stacks K → Prop} {pendingN : SchurKey r r 0 → Stacks L → Prop}
    (den : Engine.Contracts a (SchurKey.program (U := r) (Z := 0) (constantEntries D))
      addr width budget (SchurKey.arityBound r r 0) readyD pendingD descTime)
    (descD : Engine.DescribeBounded a (SchurKey.program (U := r) (Z := 0) (constantEntries D))
      addr width descTime descSpace (depth r) readyD)
    (num : Engine.Contracts b (SchurKey.program (U := r) (Z := 0) (constantEntries N))
      addr width budget (SchurKey.arityBound r r 0) readyN pendingN descTime)
    (descN : Engine.DescribeBounded b (SchurKey.program (U := r) (Z := 0) (constantEntries N))
      addr width descTime descSpace (depth r) readyN)
    (boundD : ∀ s, readyD s → ∀ k, (s k).length ≤ auxBound)
    (boundN : ∀ s, readyN s → ∀ k, (s k).length ≤ auxBound)
    (auxD : Stacks K) (hD : readyD auxD) (auxN : Stacks L) (hN : readyN auxN)
    (room : (deg+1)*(width+1) + divideClock deg width ≤ space r addr width deg budget auxBound descSpace) :
    ∃ t ≤ 2 * clock r addr width deg budget descTime + divideClock deg width,
      ∃ outD outN, readyD outD ∧ readyN outN ∧
        (query a b).BoundedRun (space r addr width deg budget auxBound descSpace) t
          (host (entryBank c r addr width auxD) (entryBank c r addr width auxN)
            (frame q deg width (digits width c) [] [] []))
          (host (resultBank c r addr width (topPencil D) outD) (resultBank c r addr width (topPencil N) outN)
            (frame q deg width (digits width c) [] [] (digits width (minorQuotient c N D)))) := by
  obtain ⟨d, hd, outD, hoD, first⟩ := topPencil_runs c D a den descD boundD auxD hD
  obtain ⟨n, hn, outN, hoN, second⟩ := topPencil_runs c N b num descN boundN auxN hN
  obtain ⟨t, ht, both⟩ := query_runs a b c hw N D first second rfl rfl room
  exact ⟨t, by omega, outD, outN, hoD, hoN, both⟩

end SchurPair
end Cramer
end RankQuery.Stack.Coordinate

end VPVNP
end Computability
end OAI
