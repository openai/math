import OAI.Computability.NearSquareRoot.FixedLayerSweep
import OAI.Computability.NearSquareRoot.SynchronizedChronologicalBox

/-! # Fixed-candidate transform program from physical opcode semantics

The physical branch at a ticket updates the array in packed address order.
The program translates the incoming and outgoing records through the fixed
directory equivalence. Its exact isometry at tick `t` is the matrix of ticket
`length - 1 - t` in the generated directed word.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code DigitPacking FixedPoint FixedCandidate Matrix WithLp
  SynchronizedLayers.ScheduleProgram ShortFourier ShortFourier.BatchWord ProductMatrixLayers
  SynchronizedPadding ResidueFourier ProductRecovery

noncomputable section

abbrev tickets (n : ℕ) (dir : Bool) := directedPlan (dir,tally (addressBits n))

private def ticketIndex {m : ℕ} (t : ℕ) (ht : t < m) : Fin m := ⟨m - 1 - t, by omega⟩

private theorem tick_map {X Y : Type} [Fintype Y] [DecidableEq Y] (f : X → Square Y)
    (l : List X) (t : ℕ) (ht : t < l.length) :
    atTick (l.map f) t = f l[l.length-1-t] := by
  have hmap : t < (l.map f).length := by simpa using ht
  have hi : l.length - 1 - t < l.length := by omega
  simp only [atTick, List.getElem?_reverse hmap, List.length_map, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

private theorem ticket_depth {k : ℕ} (hk : 1024 ≤ k) (dir : Bool) :
    (directedPlan (dir,tally k)).length ≤ 2^(10*k) := by
  have he := executionPlan_length dir k
  rw [executionPlan, List.length_reverse] at he
  rw [he]
  have hlog : Nat.clog 2 k ≤ k := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := k)).le
  calc
    936230400 * Nat.clog 2 k + 117074160 ≤ 2^31*k := by omega
    _ ≤ 2^(9*k)*2^k := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega))
      (Nat.lt_two_pow_self (n := k)).le
    _ = _ := by rw [←pow_add]; congr 1; omega

variable {n : ℕ} (h : Directory n) (hd : 4 ≤ (FixedCandidate.box n).length)

def ticketMatrix (r : Bool × Row SlotDescriptor) : Matrix (FixedCandidate.Axis n) (FixedCandidate.Axis n) ℂ :=
  letI := BoxFin.modulus_neZero h
  boxRow (physicalLayout h) hd r

private theorem unitaryTickets (dir : Bool) :
    letI := BoxFin.modulus_neZero h
    UnitaryFactors ((tickets n dir).map (ticketMatrix h hd)) := by
  let _ := BoxFin.modulus_neZero h
  intro M hM
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hM
  exact ((directedPlan_correct h hd (physicalLayout h) dir).2.1 r hr).unitary

private def recordStep (dir : Bool) (out : Fin (tickets n dir).length → Array n → Array n)
    (t : ℕ) (r : FixedCandidate.Axis n → Record (addressBits n)) : FixedCandidate.Axis n → Record (addressBits n) :=
  if ht : t < (tickets n dir).length then
    (out (ticketIndex t ht) (r ∘ (index h).symm)) ∘ index h else r

/-- The fixed-candidate plan uses the specified physical command on each chronological tick. -/
def programOfRows (dir : Bool) (out : Fin (tickets n dir).length → Array n → Array n) : Program h :=
  letI := BoxFin.modulus_neZero h
  Layers.fromMatrices _ (unitaryTickets h hd dir) (recordStep h dir out)

theorem programOfRows_steps (dir : Bool) (out : Fin (tickets n dir).length → Array n → Array n) :
    steps h (programOfRows h hd dir out) = (tickets n dir).length :=
  List.length_map (ticketMatrix h hd)

/-- Exact equality of physical records, throughout the whole tape domain. -/
theorem programOfRows_nextArray (dir : Bool) (out : Fin (tickets n dir).length → Array n → Array n)
    (t : ℕ) (ht : t < (tickets n dir).length) (x : Array n) :
    nextArray h (programOfRows h hd dir out) t x =
      out ⟨(tickets n dir).length - 1 - t, by omega⟩ x := by
  have hcomp : (x ∘ index h) ∘ (index h).symm = x := by funext j; simp
  change (recordStep h dir out t (x ∘ index h)) ∘ (index h).symm = _
  rw [recordStep, dite_eq_left ht, hcomp]
  funext j
  simp [ticketIndex]

/-- Required numerical guarantee from a physical branch. Both terms use
the padded residue grid on which the exact Fourier matrix acts. -/
def TicketError (dir : Bool) (out : Fin (tickets n dir).length → Array n → Array n) : Prop :=
  letI := BoxFin.modulus_neZero h
  ∀ (j : Fin (tickets n dir).length) (x : Array n), working h x →
    ‖recordArray (out j x ∘ index h) -
      toLp 2 (ticketMatrix h hd (tickets n dir)[j.val] *ᵥ (fun z => recordArray (x ∘ index h) z))‖ ≤
        1/(2:ℝ)^(50*addressBits n)

/-- Local guarantees in the working range give the forward or adjoint
accuracy certificate used by the fixed multiplication candidate. -/
theorem programOfRows_correct (hk : 1024 ≤ addressBits n) (dir : Bool)
    (out : Fin (tickets n dir).length → Array n → Array n) (err : TicketError h hd dir out) :
    if dir then InverseOK h (programOfRows h hd dir out) else ForwardOK h (programOfRows h hd dir out) := by
  let _ := BoxFin.modulus_neZero h
  let ms := (tickets n dir).map (ticketMatrix h hd)
  have hms : UnitaryFactors ms := unitaryTickets h hd dir
  have prod : ms.prod = if dir then (paddedFourier (FixedCandidate.box n))ᴴ else paddedFourier (FixedCandidate.box n) :=
    (directedPlan_correct h hd (physicalLayout h) dir).1
  let F := programOfRows h hd dir out
  let U := if dir then (FixedCandidate.ideal h).symm.toLinearIsometry else (FixedCandidate.ideal h).toLinearIsometry
  have approx : F.Approximates U := by
    refine ⟨?_, ?_, ?_⟩
    · change steps h (programOfRows h hd dir out) ≤ _
      rw [programOfRows_steps]
      exact ticket_depth hk dir
    · intro x
      change exactLayerPrefix (ProductMatrixLayers.ideal ms hms) x ms.length = U x
      rw [execute, prod]
      cases dir
      · rfl
      · exact (matrixIsometry_symm_apply _ (tensorMatrix_axisPadding_unitary
          (B := fun i => Fin (BoxFin.padding (FixedCandidate.box n) i))
          (fun i => axisMatrix (BoxFin.modulus (FixedCandidate.box n) i))
          (fun i => axisMatrix_unitary (BoxFin.modulus (FixedCandidate.box n) i))) (ofLp x)).symm
    · intro t ht r hr
      have ht' : t < (tickets n dir).length := by
        change t < ((tickets n dir).map (ticketMatrix h hd)).length at ht
        simpa using ht
      let j := ticketIndex t ht'
      let x := r ∘ (index h).symm
      have hx : x ∘ index h = r := by funext z; simp [x]
      have hw : working h x := by change ‖recordArray (x ∘ index h)‖ ≤ _; rw [hx]; exact hr
      have he := err j x hw
      rw [hx] at he
      change ‖recordArray (recordStep h dir out t r) -
        (matrixIsometry (atTick ms t) (unitary_atTick hms t)) (recordArray r)‖ ≤ _
      rw [recordStep, dite_eq_left ht']
      change ‖recordArray (out j x ∘ index h) - toLp 2 (atTick ms t *ᵥ (fun z => recordArray r z))‖ ≤ _
      rw [show atTick ms t = ticketMatrix h hd (tickets n dir)[j.val] from tick_map _ _ t ht']
      exact he
  cases dir <;> exact approx

end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
