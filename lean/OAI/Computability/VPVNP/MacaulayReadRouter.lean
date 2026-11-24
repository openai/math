import OAI.Computability.VPVNP.MacaulayReadPorts
import OAI.Computability.VPVNP.RankQueryGramReadSpace
import OAI.Computability.VPVNP.RankQueryTagSpace
import OAI.Computability.VPVNP.RegisterTable

/-! # Calling the three physical Macaulay entry routines

The row descriptor selects an original coefficient, an affine pin coefficient,
or a powered-monomial equality test. The dispatch and selection code preserves
the caller's input addresses. Its running time is polynomial in the word
width. The long selected routine uses its own independent live-space bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead

open BurstRAM RAMTape MacaulayRowDispatch Engine

variable {K : Type} [DecidableEq K]

/-- Decode tag 0 as an original equation, tag 1 as an affine pin and any larger tag as a
powered monomial. -/
def ofTag (n : ℕ) : Kind := if n = 0 then .equation else if n = 1 then .affine else .power

private theorem ofTag_tag (k : Kind) : ofTag k.tag = k := by cases k <;> rfl

/-- One fixed instruction table, formed from the three coefficient routines. -/
def reader (arms : Kind → FiniteRoutine (Bus K)) : FiniteRoutine (Bus K) :=
  (MacaulayRowDispatch.machine.onPorts route).followedBy
    (TagRouter.select (route (.reg (outReg 0))) 2 (arms ∘ ofTag))

/-- Runtime size words occupy registers 2 through 7. Registers 0 and 1
refer to the caller's two address ports, and may change between reads. -/
def Params {w : ℕ} (equations pins multiples : ℕ) (rs : Reg → Word w) : Prop :=
  ∀ a : Fin 8, 2 ≤ a.val → (rs (inReg a)).val = inputs 0 0 equations pins multiples a

/-- The private workspace contains the advised row counts and a coefficient bank satisfying the
caller's readiness predicate. -/
def Ready (w equations pins multiples : ℕ) (leafReady : Stacks K → Prop) (aux : Stacks (Work K)) : Prop :=
  ∃ (rs : Reg → Word w) (leaf : Stacks K), Params equations pins multiples rs ∧ leafReady leaf ∧ aux = auxBank rs leaf

private theorem install_inputs {w equations pins multiples : ℕ} {rs : Reg → Word w}
    (hp : Params equations pins multiples rs) {i j : ℕ} (hi : i < 2^w) (hj : j < 2^w) :
    ∀ a, ((setAddresses rs i j) (inReg a)).val = inputs i j equations pins multiples a := by
  intro a
  fin_cases a
  · simp [setAddresses, inputs, inReg, Dispatch.Code.inReg, Nat.mod_eq_of_lt hi]
  · simp [setAddresses, inputs, inReg, Dispatch.Code.inReg, Nat.mod_eq_of_lt hj]
  · simpa (config := { decide := true }) [setAddresses, inReg, Dispatch.Code.inReg, inputs] using hp 2 (by decide)
  · simpa (config := { decide := true }) [setAddresses, inReg, Dispatch.Code.inReg, inputs] using hp 3 (by decide)
  · simpa (config := { decide := true }) [setAddresses, inReg, Dispatch.Code.inReg, inputs] using hp 4 (by decide)
  · simpa (config := { decide := true }) [setAddresses, inReg, Dispatch.Code.inReg, inputs] using hp 5 (by decide)
  · simpa (config := { decide := true }) [setAddresses, inReg, Dispatch.Code.inReg, inputs] using hp 6 (by decide)
  · simpa (config := { decide := true }) [setAddresses, inReg, Dispatch.Code.inReg, inputs] using hp 7 (by decide)

omit [DecidableEq K] in
private theorem frame_length {w A : ℕ} (rs : Reg → Word w) (leaf : Stacks K)
    (h : ∀ k, (leaf k).length ≤ A) (z : Bus K) : (frame rs [] leaf z).length ≤ max w A := by
  cases z with
  | row | col => simp [frame, bank, UniversalCountStack.length_digits]
  | result => simp [frame, bank]
  | aux x =>
    rcases x with q | k
    · change (auxBank rs leaf (.inl q)).length ≤ max w A
      have hl := RegisterTable.bank_length_le Fin.elim0 (0 : Word w) rs q
      cases q with
      | reg r => simp [auxBank]; split_ifs <;> simp
      | pub | work | persistent | logPort => exact hl.trans (le_max_left ..)
    · exact (h k).trans (le_max_right ..)

/-- A run of one coefficient routine from a populated row descriptor. The
three routines are called on disjoint classes of indices. Their bounds may
be exponential in time while keeping polynomial space. -/
def ArmCorrect {p e n m : ℕ} {c : SliceArithmetic.Vector p e}
    (M : Matrix (Fin n) (Fin m) (Scalar c)) (w v equations pins multiples B S : ℕ)
    (leafReady : Stacks K → Prop) (arms : Kind → FiniteRoutine (Bus K)) : Prop :=
  ∀ (i : Fin n) (j : Fin m) (rs : Reg → Word w) (leaf : Stacks K),
    (∀ a, (rs (inReg a)).val = inputs i j equations pins multiples a) →
    (∀ a, (rs (outReg a)).val = (address i j equations pins multiples).fields a) → leafReady leaf →
    ∃ t ≤ B, ∃ out, Ready w equations pins multiples leafReady out ∧
      (arms (address i j equations pins multiples).kind).BoundedRun S t (frame rs [] leaf)
        (bank w i j (scalar v (M i j)) out)

/-- The call interface consumed by the Gram and Schur engine, with all
routing and register framing accounted for. -/
theorem correctSpace_of_arms {p e n m : ℕ} {c : SliceArithmetic.Vector p e}
    (M : Matrix (Fin n) (Fin m) (Scalar c)) (w v equations pins multiples B S A b : ℕ)
    (leafReady : Stacks K → Prop) (arms : Kind → FiniteRoutine (Bus K))
    (bound : ∀ (i : Fin n) (j : Fin m) a, inputs i j equations pins multiples a < 2^b)
    (hw : requiredWidth b ≤ w) (hbw : b ≤ w) (ht : 2 ≤ w)
    (space : ∀ leaf, leafReady leaf → ∀ k, (leaf k).length ≤ A)
    (room : max w A + ticks w ≤ S) (arm : ArmCorrect M w v equations pins multiples B S leafReady arms) :
    CorrectSpace (reader arms) M w v (ticks w + (4+B)) S (Ready w equations pins multiples leafReady) := by
  rintro i j _ ⟨rs,leaf,pars,ok,rfl⟩
  have hi : i.val < 2^w := (bound i j 0).trans_le (Nat.pow_le_pow_right (by decide) hbw)
  have hj : j.val < 2^w := (bound i j 1).trans_le (Nat.pow_le_pow_right (by decide) hbw)
  let start := setAddresses rs i j
  have hin := install_inputs pars hi hj
  obtain ⟨td,hd,mid,disp,hkeep,hout⟩ := dispatch_runs _ _ _ _ _ b (bound i j) hw start hin [] leaf
  have midIn a : (mid (inReg a)).val = inputs i j equations pins multiples a := (congrArg Fin.val (hkeep a)).trans (hin a)
  obtain ⟨ta,ha,aux,hr,run⟩ := arm i j mid leaf midIn hout ok
  let addr := address i.val j.val equations pins multiples
  have hs : frame mid [] leaf (route (.reg (outReg 0))) = UniversalCountStack.digits w addr.kind.tag := by
    rw [frame_route]
    change wordBits (mid (outReg 0)) = wordBits (Fin.ofNat _ addr.kind.tag)
    apply congrArg wordBits
    apply Fin.ext
    have hh : (mid (outReg 0)).val = addr.kind.tag := hout 0
    exact hh.trans (Nat.mod_eq_of_lt (hh ▸ (mid (outReg 0)).isLt)).symm
  have htag : addr.kind.tag < 2^2 := by cases addr.kind <;> decide
  have sub : (arms ∘ ofTag) addr.kind.tag = arms addr.kind := congrArg arms (ofTag_tag _)
  have select := TagRouter.digits_bounded (route (.reg (outReg 0))) (arms ∘ ofTag) ht htag _ _ hs (sub.symm ▸ run)
  have dr : (MacaulayRowDispatch.machine.onPorts route).BoundedRun S td (frame start [] leaf) (frame mid [] leaf) :=
    UniversalCountStack.spaceRun_of_steps disp fun z => (Nat.add_le_add (frame_length start leaf (space leaf ok) z) hd).trans room
  refine ⟨td+(2*2+ta), by omega, aux, hr, ?_⟩
  rw [reframe]
  exact dr.followedBy select

end RankQuery.Stack.MacaulayRead

end VPVNP
end Computability
end OAI
