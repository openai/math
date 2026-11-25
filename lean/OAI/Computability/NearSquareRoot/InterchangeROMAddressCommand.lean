import OAI.Computability.NearSquareRoot.InterchangeROMAddress
import OAI.Computability.NearSquareRoot.InterchangeBQuestResolve

/-! # A single pivot descriptor kernel and its recursive command

The literal carrying the radix and the cuts varies with the finite template.
The register cutoff, the descriptor kernel and the exponents in its clock
are common to all templates. Neither the descriptor kernel nor the call loop
duplicates the live payload.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims NearSquareRoot.InterchangeBatch Space
  CommonRegisters RegisterWitness InterchangeSpace
open Filter

/-- Install the template literal on the header side of the caller's packet. -/
def prepare (core : Cmd) (s : Spec) : Cmd :=
  splitRoot 0 (fun _ => .pass)
    (((Task.prepare 0 (send s)).join ((pack 0).join core)).join (pack 0))

/-- The enclosing recursive routine lies one binder outside the batch loop. -/
def command (core : Cmd) (s : Spec) : Cmd :=
  (prepare core s).join (batch (.again 1))

def headerTime (spec : Spec) (h : Header) (K d : ℕ) : ℕ :=
  5 * size spec + K * (size (spec,h) + 1)^d + 20

/-- The fixed kernel can be chosen once, independently of every parameter
of an interchange and of the number of pivots in its program. -/
theorem exists_core :
    ∃ (core : Cmd) (R K d : ℕ),
      (∀ spec : Spec, Within R (command core spec)) ∧
      ∀ spec h (stream : Tree) env deck,
        Fits env (prepare core spec) (pile 0 (.fork (send h) stream) deck)
          (pile 0 (.fork (send (plan (spec,h))) stream) deck) (headerTime spec h K d) := by
  obtain ⟨u,⟨d,C,hbound⟩,c,D,hc⟩ := plan_poly
  obtain ⟨R,hR,hcode,hbatch⟩ : ∃ R : ℕ, 0 < R ∧ Within R c ∧ Within R (batch (.again 1)) := by
    exact ((eventually_gt_atTop (0 : ℕ)).and ((RegisterSelect.within_eventually c).and
      (RegisterSelect.within_eventually (batch (.again 1))))).exists
  refine ⟨c,R,D*(C+1),d,?_,?_⟩
  · intro spec
    have pv := (prepare_within (R:=R) (i:=0) (send spec)).mpr hR
    exact ⟨(splitRoot_within.mpr ⟨hR,trivial,trivial,⟨⟨pv,⟨hR,hcode⟩⟩,hR⟩⟩),hbatch⟩
  · intro spec h stream env deck
    let saved := pile 0 stream deck
    have push := Task.fits_prepare 0 (send spec) env (pile 0 (send h) saved)
    have packed := fits_pack (send spec) (send h) saved 0 env
    have run := hc (spec,h) env saved
    have finish := fits_pack (send (plan (spec,h))) stream deck 0 env
    have pre := fits_pair (c:=fun _ => .pass) ((push.join (packed.join run)).join finish)
    refine pre.mono ?_
    have hh := hbound (spec,h)
    have pos : 1 ≤ (size (spec,h) + 1)^d := Nat.one_le_pow _ _ (by omega)
    have bound : D * (u (spec,h) + 1) ≤ D * (C+1) * (size (spec,h) + 1)^d := by
      rw [Nat.mul_assoc,Nat.add_mul,Nat.one_mul]
      exact Nat.mul_le_mul_left _ (by omega)
    unfold headerTime size at *
    omega

variable {X : Type*}

/-- Child time is charged once per element of the linked schedule. Header
construction contributes no term depending on the number of payload cells. -/
theorem run (core : Cmd) (K d : ℕ)
    (ok : ∀ spec h (stream : Tree) env deck,
      Fits env (prepare core spec) (pile 0 (.fork (send h) stream) deck)
        (pile 0 (.fork (send (plan (spec,h))) stream) deck) (headerTime spec h K d))
    (spec : Spec) (h : Header) (hdr payload reply : X → Tree)
    (time data depth : X → ℕ) (parent : Cmd) (env : Env) (V : ℕ)
    {x y : Tree} {qs : List X} (tags : send (plan (spec,h)) = headers hdr qs)
    (chain : Chain payload reply x qs y)
    (hx : ∀ q ∈ qs, (payload q).count ≤ V) (hy : y.count ≤ V)
    (child : ∀ q ∈ qs, ∀ deck base, DeckCap base deck →
      BoundedFits (parent :: env) parent (pile 0 (.fork (hdr q) (payload q)) deck)
        (pile 0 (reply q) deck) (time q) (base + data q) (depth q))
    (deck : Deck) (base : ℕ) (hc : DeckCap base deck) :
    let T := headerTime spec h K d
    let H := (headers hdr qs).count
    let input := Tree.fork (send h) x
    BoundedFits (parent :: env) (command core spec)
      (pile 0 input deck) (pile 0 y deck)
      (T + (((qs.map time).sum + qs.length) + 110 * (H + 1)) + 2)
      (base + max (input.count + T) (dataSpace V H (childPeak data qs)))
      (max (T+1) (returnSpace H (childPeak depth qs))) := by
  let T := headerTime spec h K d
  let H := (headers hdr qs).count
  let input := Tree.fork (send h) x
  let cap := max (input.count + T) (dataSpace V H (childPeak data qs))
  let ret := max (T+1) (returnSpace H (childPeak depth qs))
  have pre := ok spec h x (parent :: env) deck
  rw [tags] at pre
  have ready := BoundedFits.of_fits pre (cap:=base+cap) (depth:=T) (fun j => ?_) le_rfl
  · have calls := run_recursive_batch hdr payload reply time data depth parent env V
      (dataSpace V H (childPeak data qs)) (returnSpace H (childPeak depth qs))
      chain hx hy (le_max_left ..) (le_max_left ..)
      (fun q hq => (Nat.add_le_add_left (le_childPeak data hq) H).trans (le_max_right ..))
      (fun q hq => (Nat.succ_le_succ (le_childPeak depth hq)).trans (le_max_right ..))
      child deck base hc
    exact ready.join (calls.mono le_rfl (Nat.add_le_add_left (le_max_right ..) base)
      (le_max_right ..)) (le_max_left ..)
  · have sz := hc.pile 0 input j
    have lo : input.count + T ≤ cap := le_max_left ..
    change (letters (pile 0 input deck) j).length + T ≤ base + cap
    omega

end InterchangeROMAddress

end NearSquareRoot
end Computability
end OAI
