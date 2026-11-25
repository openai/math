import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalBounded

/-! # Shared time and peak bounds of the physical ground repair -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip InterchangeROM

/-- The exact public domains of the nine leaves. -/
inductive Inputs {E W S : Type} (wide : W → List E) (short : S → List E) : Leaf → List E → Prop
  | duplicate x : Inputs wide short .duplicate (wide x)
  | stage x : Inputs wide short .stage (wide x)
  | extract x y : Inputs wide short .extract (wide x ++ wide y)
  | forward x y : Inputs wide short .forward (short x ++ short y)
  | correct x y : Inputs wide short .correct (short x ++ short y)
  | backward x y : Inputs wide short .backward (short x ++ short y)
  | restore x y z : Inputs wide short .restore (wide x ++ (short y ++ short z))
  | copyCube x y z : Inputs wide short .copyCube ((wide x ++ wide y) ++ wide z)
  | finish x y z w : Inputs wide short .finish (((wide x ++ wide y) ++ wide z) ++ wide w)

theorem inputs_domains {E W S : Type} (wide : W → List E) (short : S → List E) :
    LeafDomains (Inputs wide short) wide short :=
  ⟨.duplicate,.stage,.extract,.forward,.correct,.backward,.restore,.copyCube,.finish⟩

def small (r : ℕ) (xs : List Tree) : Prop := ∀ t ∈ xs, t.count ≤ r

private theorem small_append {r : ℕ} {xs ys : List Tree} :
    small r (xs++ys) ↔ small r xs ∧ small r ys := by
  simp only [small,List.mem_append]
  grind

private theorem volume {r : ℕ} (xs : List Tree) (h : small r xs) (z : Tree) :
    (packet z xs).count ≤ z.count + 2 + xs.length*(r+1) := by
  have forest (as : List Tree) (hr : small r as) :
      (Task.forest id as).count ≤ 1 + as.length*(r+1) := by
    induction as with
    | nil => simp [Tree.count]
    | cons a as ih =>
      have h₁ := hr a (by simp)
      have h₂ := ih (fun v hv => hr v (by simp [hv]))
      simp only [Task.forest_cons,id_eq,Tree.count,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  have := forest xs h
  simp only [packet,Tree.count]
  omega

variable {R V U L X : Type} [Field R] [Fintype V] [Fintype U] {m : ℕ}
    {leaf : Leaf → List Tree → List Tree} {t : Spec R V U m} {half : R}
    {tag : X → Fin m → Bool} {fw bw : (X → R) → X → R}
    {advance : Bank R L X V → Bank R L X V}
    {wide : Bank R L X V → List Tree} {short : Bank R L X U → List Tree}

private theorem leaf_bounds (h : LeafSemantics leaf t half tag fw bw advance wide short)
    {n q r : ℕ} (hw : ∀ x, (wide x).length = n) (hs : ∀ y, (short y).length = q)
    (bw : ∀ x, small r (wide x)) (bs : ∀ x, small r (short x))
    {a xs} (src : Inputs wide short a xs) :
    xs.length ≤ 4*n+2*q ∧ (leaf a xs).length ≤ 4*n+2*q ∧ small r (leaf a xs) := by
  cases src <;> simp only [h.duplicate,h.stage,h.extract,h.forward,h.correct,h.backward,h.restore,
    h.copyCube,h.finish,List.length_append,hw,hs,small_append,bw,bs,and_true] <;> omega

theorem steps_length (n d : ℕ) : (steps n d).length = 4*d+8 := by
  simp [steps]
  omega

theorem steps_park {n d : ℕ} {s : Step} (h : s ∈ steps n d) : s.1 ≤ 3*n := by
  obtain ⟨k,a⟩ := s
  simp [steps,List.mem_replicate,Prod.mk.injEq] at h
  dsimp; omega

/-- Middle banks and saved prefixes are included once in the stack bound.
Only the local time factor is multiplied by the number of parked rows. -/
theorem allowance_steps (h : LeafSemantics leaf t half tag fw bw advance wide short)
    (n q r : ℕ) (hw : ∀ x, (wide x).length = n) (hs : ∀ x, (short x).length = q)
    (bw : ∀ x, small r (wide x)) (bs : ∀ x, small r (short x))
    (header : Tree) (d stage child loc cap depth : ℕ) (charge : Leaf → List Tree → Allowance)
    (cost : ∀ a xs, Inputs wide short a xs →
      (charge a xs).time ≤ loc + price stage q m (0,a)*child ∧
      (charge a xs).cap ≤ cap ∧ (charge a xs).depth ≤ depth)
    (x : Bank R L X V) :
    let v := header.count + 2 + (7*n+2*q)*(r+1)
    let overhead := 256*(v+1)
    let actual := allowance leaf charge header (steps n d) (wide x)
    actual.time ≤ 1+(4*d+8)*(loc+3*n*overhead+2)+(4*d*stage+4*q*m)*child ∧
    actual.cap ≤ cap+overhead ∧ actual.depth ≤ depth+overhead+1 := by
  intro v ov
  let tick := loc+3*n*ov+2
  have go (ss : List Step) (xs : List Tree)
      (limit : xs.length ≤ 7*n+2*q) (bounds : small r xs)
      (live : Ready leaf (Inputs wide short) ss xs) (park : ∀ s ∈ ss, s.1 ≤ 3*n) :
      let a := allowance leaf charge header ss xs
      a.time ≤ 1+ss.length*tick + (ss.map (price stage q m)).sum*child ∧
      a.cap ≤ cap+ov ∧ a.depth ≤ depth+ov+1 := by
    have hdr : (packet header xs).count ≤ v :=
      (volume xs bounds header).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ limit) _)
    induction ss generalizing xs with
    | nil => simp [allowance]; dsimp [ov]; omega
    | cons s ss ih =>
      obtain ⟨hlen,src,live'⟩ := live
      obtain ⟨_,lout,sout⟩ := leaf_bounds h hw hs bw bs src
      have lp := park s (by simp)
      let next := applyStep leaf xs s
      have ln : next.length ≤ 7*n+2*q := by
        simp only [next,applyStep,List.length_append,List.length_take_of_le hlen]; omega
      have sn : small r next :=
        small_append.mpr ⟨fun a ha => bounds a (List.mem_of_mem_take ha),sout⟩
      have hd : (packet header next).count ≤ v :=
        (volume _ sn _).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ln) _)
      have ih' := ih next ln sn live' (fun a ha => park a (by simp [ha])) hd
      obtain ⟨ct,cc,cd⟩ := cost _ _ src
      have one : 256*(max (packet header xs).count (packet header next).count+1) ≤ ov :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right (max_le hdr hd) _)
      have step : (stageAllowance leaf charge header xs s).time + 2 ≤
          tick + price stage q m s*child := by
        have hp := Nat.mul_le_mul lp one
        dsimp only [stageAllowance]
        change _ + s.1*(256*(max (packet header xs).count (packet header next).count+1))+2 ≤ _
        change (charge s.2 (xs.drop s.1)).time ≤ loc + price stage q m s*child at ct
        dsimp only [tick]; omega
      have peak : (stageAllowance leaf charge header xs s).cap ≤ cap+ov :=
        Nat.add_le_add cc one
      have ret : (stageAllowance leaf charge header xs s).depth ≤ depth+ov :=
        Nat.add_le_add cd one
      rcases ih' with ⟨t',p',d'⟩
      change (stageAllowance ..).time + (allowance leaf charge header ss next).time + 2 ≤ _ ∧
        max (stageAllowance ..).cap (allowance leaf charge header ss next).cap ≤ _ ∧
        max ((stageAllowance ..).depth+1) (allowance leaf charge header ss next).depth ≤ _
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul,List.map_cons,List.sum_cons]
      exact ⟨by omega,max_le peak p',max_le (by omega) d'⟩
  have v' := go (steps n d) (wide x) (by rw [hw]; omega) (bw x)
    (ready_steps h (inputs_domains wide short) n hw d x) (fun _ hs' => steps_park hs')
  simpa only [steps_length,total_price,tick] using v'

end InterchangeROMRepair.Physical

end NearSquareRoot
end Computability
end OAI
