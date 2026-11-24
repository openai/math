import OAI.Computability.VPVNP.MacaulayPairPower

/-! # Physical Macaulay entry arms with restored scratch banks

Both arms preserve the two ordinal words, the degree and cardinality
parameters, and the unary label counter. The equation arm prepends the
ordered residual exponent words and a full-word divisibility flag. The
powered-monomial arm prepends one full-word equality flag. Temporary raw
keys are erased before returning to the matrix reader.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.PairCall

open RAMTape UniversalCountStack

/-- Perform the source ordinal lookup and then the column ordinal lookup, retaining both raw
keys. -/
def scans := (ordinal false).followedBy (ordinal true)

/-- Erase the two temporary raw-key stacks before returning to the caller. -/
def clearKeys : FiniteRoutine Port :=
  SliceArithmetic.CallClear.cleanup [.external (.raw false), .external (.raw true)]

/-- Return the packed column-minus-source exponents and a divisibility flag after looking up
both monomials and clearing their keys. -/
def equation := (scans.followedBy packRaw).followedBy clearKeys
/-- Return the equality flag comparing the column with the shifted and scaled source monomial,
then clear both temporary keys. -/
def powered := (scans.followedBy powerRaw).followedBy clearKeys

/-- A bounded-degree exponent vector on the input variables, with its degree bound taken from
the source or column side. -/
abbrev Monomial (d : Inputs) (c : Bool) := BoundedMonomial d.arity (d.degree c)
/-- Valid indices into the bounded-monomial enumerations for the source and column. -/
abbrev Ordinals (d : Inputs) := (c : Bool) → Fin (size d.arity (d.degree c))

/-- The bounded monomial at the selected ordinal on the indicated side of the entry query. -/
def monomial (d : Inputs) (k : Ordinals d) (c : Bool) : Monomial d c := enumeration d.arity (d.degree c) (k c)

/-- Combined tick allowance for the source and column ordinal searches at their respective
degree bounds. -/
def scanClock (w B : ℕ) (d : Inputs) :=
  ordinalClock w B d.arity (d.degree false) + ordinalClock w B d.arity (d.degree true)

theorem scans_runs {w B : ℕ} (d : Inputs) (k : Ordinals d) (hk : ∀ c, d.ordinal c = (k c).val)
    (fit : ∀ c, ISA.Fits (ISA.graded d.arity (d.degree c) (k c)) w) (packed flag : List Bool)
    (hw : w ≤ B) (ht : d.arity ≤ B) (hp : packed.length ≤ B) (hf : flag.length ≤ B) :
    let key := keys w (monomial d k false) (monomial d k true)
    ∃ n ≤ scanClock w B d, scans.BoundedRun (ordinalSpace w B) n
      (publicBank w d (fun _ => []) packed flag) (publicBank w d key packed flag) := by
  intro key
  let left : Bool → List Bool := fun c => if c then [] else digits w (rawCode (monomial d k false)).val
  obtain ⟨n₁,hn₁,hr₁⟩ := ordinal_runs d false (k false) (hk false) (fit false) (fun _ => []) packed flag
    (values_le d _ packed flag hw ht (fun _ => Nat.zero_le _) hp hf)
  have h₁ : Function.update (fun _ : Bool => ([] : List Bool)) false
      (digits w (rawCode (monomial d k false)).val ++ []) = left := by funext c; cases c <;> simp [left]
  change (ordinal false).BoundedRun _ _ _ (publicBank w d (Function.update _ false
    (digits w (rawCode (monomial d k false)).val ++ [])) packed flag) at hr₁
  rw [h₁] at hr₁
  have hlen (c : Bool) : (left c).length ≤ B := by cases c <;> simp [left,hw]
  obtain ⟨n₂,hn₂,hr₂⟩ := ordinal_runs d true (k true) (hk true) (fit true) left packed flag
    (values_le d _ packed flag hw ht hlen hp hf)
  have h₂ : Function.update left true (digits w (rawCode (monomial d k true)).val ++ left true) = key := by
    funext c; cases c <;> simp [left, key, keys]
  change (ordinal true).BoundedRun _ _ _ (publicBank w d (Function.update left true
    (digits w (rawCode (monomial d k true)).val ++ left true)) packed flag) at hr₂
  rw [h₂] at hr₂
  exact ⟨n₁+n₂, Nat.add_le_add hn₁ hn₂, hr₁.followedBy hr₂⟩

/-- Tick allowance to clear two raw-key stacks of at most w bits each and return. -/
def clearCost (w : ℕ) := 2*(w+1)+1

private theorem clearKeys_runs {w B : ℕ} (d : Inputs) (raw : Bool → List Bool) (packed flag : List Bool)
    (hr : ∀ c, (raw c).length ≤ w) (hB : ∀ i, (values w d raw packed flag i).length ≤ B) :
    ∃ n ≤ clearCost w, clearKeys.BoundedRun (B+clearCost w) n (publicBank w d raw packed flag)
      (publicBank w d (fun _ => []) packed flag) := by
  let ports : List Port := [.external (.raw false), .external (.raw true)]
  let s := publicBank w d raw packed flag
  have h (i : Port) (hi : i ∈ ports) : (s i).length ≤ w := by
    simp only [ports, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact hr _
  obtain ⟨n,hn,hclear⟩ := SliceArithmetic.CallClear.cleanup_runs ports s w h
  have he : SliceArithmetic.CallClear.erased ports s = publicBank w d (fun _ => []) packed flag := by
    funext i
    rcases i with i | i | _
    · cases i with
      | raw c => cases c <;> simp [SliceArithmetic.CallClear.erased, ports, publicBank, CallBank.clean, CallBank.frame, values]
      | _ => simp [SliceArithmetic.CallClear.erased, ports, s, publicBank, CallBank.clean, CallBank.frame, values]
    · simp [SliceArithmetic.CallClear.erased, ports, s, publicBank, CallBank.clean, CallBank.frame]
    · simp [SliceArithmetic.CallClear.erased, ports, s, publicBank, CallBank.clean, CallBank.frame]
  rw [he] at hclear
  refine ⟨n,hn, spaceRun_of_steps hclear fun i => Nat.add_le_add ?_ hn⟩
  rcases i with i | i | _ <;> first | exact hB _ | exact Nat.zero_le _

@[simp] theorem length_difference {w t L D : ℕ} (a : BoundedMonomial t L) (b : BoundedMonomial t D) :
    (difference w a b).length = t*w := by
  have h (xs : List ℕ) : (ExponentPack.packed w xs).length = xs.length*w := by
    induction xs with
    | nil => simp [ExponentPack.packed]
    | cons a xs ih =>
      change ((UniversalCountStack.digits w a) ++ ExponentPack.packed w xs).length = (xs.length+1)*w
      rw [List.length_append, length_digits, ih, Nat.add_one_mul, Nat.add_comm]
  simp [difference,h]

/-- Maximum stack allowance for ordinal lookup, residual packing and final cleanup in the
equation arm. -/
def equationSpace (w B : ℕ) (d : Inputs) :=
  max (max (ordinalSpace w B) (packSpace d.arity w B)) (B + d.arity*w + w + clearCost w)

/-- Maximum stack allowance for ordinal lookup, powered-exponent comparison and final cleanup
in the powered arm. -/
def poweredSpace (w B : ℕ) :=
  max (max (ordinalSpace w B) (powerSpace w B)) (B+w+clearCost w)

theorem equation_runs {w B : ℕ} (d : Inputs) (k : Ordinals d) (hk : ∀ c, d.ordinal c = (k c).val)
    (fit : ∀ c, ISA.Fits (ISA.graded d.arity (d.degree c) (k c)) w) (packed flag : List Bool)
    (hw : w ≤ B) (ht : d.arity ≤ B) (hp : packed.length ≤ B) (hf : flag.length ≤ B) :
    let a := monomial d k false
    let b := monomial d k true
    ∃ n ≤ scanClock w B d + packClock d.arity w B + clearCost w,
      equation.BoundedRun (equationSpace w B d) n (publicBank w d (fun _ => []) packed flag)
        (publicBank w d (fun _ => []) (difference w a b ++ packed) (digits w (decide (a.val ≤ b.val)).toNat ++ flag)) := by
  intro a b
  let key := keys w a b
  have hlen (c) : (key c).length = w := by cases c <;> simp [key,keys]
  obtain ⟨n₁,h₁,r₁⟩ := scans_runs d k hk fit packed flag hw ht hp hf
  have fs := fit false
  have fc := fit true
  rw [← hk] at fs fc
  obtain ⟨n₂,h₂,r₂⟩ := packRaw_runs d a b fs fc packed flag
    (values_le d key packed flag hw ht (fun c => (hlen c).trans_le hw) hp hf)
  let msg := difference w a b ++ packed
  let out := digits w (decide (a.val ≤ b.val)).toNat ++ flag
  let bound := B+d.arity*w+w
  have hmsg : msg.length ≤ bound := by simp [msg, bound]; omega
  have hout : out.length ≤ bound := by simp [out, bound]; omega
  obtain ⟨n₃,h₃,r₃⟩ := clearKeys_runs d key msg out (fun c => (hlen c).le)
    (values_le d key msg out (by dsimp [bound]; omega) (by dsimp [bound]; omega)
      (fun c => by rw [hlen]; dsimp [bound]; omega) hmsg hout)
  let cap := equationSpace w B d
  have t₁ : scans.BoundedRun cap n₁ _ _ := r₁.mono_cap ((le_max_left ..).trans (le_max_left ..))
  have t₂ : packRaw.BoundedRun cap n₂ _ _ := r₂.mono_cap ((le_max_right ..).trans (le_max_left ..))
  have t₃ : clearKeys.BoundedRun cap n₃ _ _ := r₃.mono_cap (le_max_right ..)
  exact ⟨_, Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃, (t₁.followedBy t₂).followedBy t₃⟩

theorem powered_runs {w B : ℕ} (d : Inputs) (k : Ordinals d) (hk : ∀ c, d.ordinal c = (k c).val)
    (fit : ∀ c, ISA.Fits (ISA.graded d.arity (d.degree c) (k c)) w) (hfit : ExponentISA.Fits (powerParams d) w)
    (packed flag : List Bool) (hw : w ≤ B) (ht : d.arity ≤ B) (hp : packed.length ≤ B) (hf : flag.length ≤ B) :
    let a := monomial d k false
    let b := monomial d k true
    ∃ n ≤ scanClock w B d + powerClock d.arity w B + clearCost w,
      powered.BoundedRun (poweredSpace w B) n (publicBank w d (fun _ => []) packed flag)
        (publicBank w d (fun _ => []) packed (digits w (powerMatch d a b).toNat ++ flag)) := by
  intro a b
  let key := keys w a b
  have hlen (c) : (key c).length = w := by cases c <;> simp [key,keys]
  obtain ⟨n₁,h₁,r₁⟩ := scans_runs d k hk fit packed flag hw ht hp hf
  obtain ⟨n₂,h₂,r₂⟩ := powerRaw_runs d a b hfit (fit false).arity_lt
    ((rawCode a).isLt.trans (fit false).limit_lt) ((rawCode b).isLt.trans (fit true).limit_lt) packed flag
    (values_le d key packed flag hw ht (fun c => (hlen c).trans_le hw) hp hf)
  let out := digits w (powerMatch d a b).toNat ++ flag
  have hout : out.length ≤ B+w := by simp [out]; omega
  obtain ⟨n₃,h₃,r₃⟩ := clearKeys_runs d key packed out (fun c => (hlen c).le)
    (values_le d key packed out (by omega) (by omega)
      (fun c => by rw [hlen]; omega) (by omega) hout)
  let cap := poweredSpace w B
  have t₁ : scans.BoundedRun cap n₁ _ _ := r₁.mono_cap ((le_max_left ..).trans (le_max_left ..))
  have t₂ : powerRaw.BoundedRun cap n₂ _ _ := r₂.mono_cap ((le_max_right ..).trans (le_max_left ..))
  have t₃ : clearKeys.BoundedRun cap n₃ _ _ := r₃.mono_cap (le_max_right ..)
  exact ⟨_, Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃, (t₁.followedBy t₂).followedBy t₃⟩

end RadicalCertificate.MonomialIndex.PairCall

end VPVNP
end Computability
end OAI
