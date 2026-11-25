import OAI.Computability.VPVNP.RAMTapeISADispatch
import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Polynomial-time bounded execution of finite bit-stack tables

A unary clock lets the outer tape program call the existing RAM instruction
dispatcher. Halts are absorbing, so the caller may supply a uniform upper bound.
-/

namespace OAI.Computability.MultitapeWeakETH.StackInterpreter

open IntegerMultiplication.Code VPVNP.RAMTape
noncomputable section

@[ext] structure Label (Q : Type) where
  val : Q

variable {Q K X Y : Type}

private def ordinal (K : Type) [Fintype K] := Fintype.equivFin K

instance [Fintype Q] : Codec (Label Q) := ⟨fun q => send (tally ((ordinal Q q.val).val))⟩

instance [Fintype Q] : FiniteState (Label Q) where
  finite := Finite.of_injective Label.val (fun _ _ => Label.ext)
  identify := by
    intro a b h
    have e : size (tally (ordinal Q a.val).val) = size (tally (ordinal Q b.val).val) := congrArg Tree.count h
    simp [size_tally] at e
    exact Label.ext ((ordinal Q).injective (Fin.ext e))

theorem label_size [Fintype Q] (q : Q) : size (Label.mk q) ≤ 2*Fintype.card Q+1 := by
  change size (tally _) ≤ _
  rw [size_tally,tally_length]
  have := (ordinal Q q).isLt
  omega

/-- A finite family of polynomial programs selected by a decoded control label. -/
theorem select_poly [Fintype Q] [Codec X] [Codec Y] (tag : X → Label Q) (ht : Poly tag)
    (f : Q → X → Y) (each : ∀ q, Poly (f q)) (fallback : X → Y) (base : Poly fallback) :
    Poly (fun x => f (tag x).val x) := by
  classical
  have loop (labels : List Q) :
      Poly (fun x => if (tag x).val ∈ labels then f (tag x).val x else fallback x) := by
    induction labels with
    | nil => simpa using base
    | cons q qs ih =>
      let test (z : Label Q) := decide (z.val=q)
      have choose := Poly.choose (ht.compose (Easy.finite test).poly) (each q) ih
      convert choose using 1
      funext x
      by_cases e : (tag x).val=q <;> simp [test,e]
  simpa using loop Finset.univ.toList

abbrev Bank := List (List Bool)
abbrev Snapshot (Q : Type) := Label Q × Bank

/-- The port enumeration depends only on the fixed table. -/
def pack [Fintype K] (s : Stacks K) : Bank := List.ofFn (s ∘ (ordinal K).symm)

theorem size_pack [Fintype K] (s : Stacks K) (cap : ℕ) (h : ∀ i, (s i).length ≤ cap) :
    size (pack s) ≤ (2*cap+2)*Fintype.card K+1 := by
  have mass (bs : List Bool) : size bs = 2*bs.length+1 := by
    induction bs <;> simp_all
    omega
  have bound (bs : Bank) (ok : ∀ b ∈ bs, b.length ≤ cap) :
      size bs ≤ (2*cap+2)*bs.length+1 := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
      have x := ok b List.mem_cons_self
      have y := ih (fun v hv => ok v (List.mem_cons_of_mem _ hv))
      simp only [size_cons,mass,List.length_cons,Nat.mul_add,Nat.mul_one]; omega
  simpa [pack] using bound (pack s) (by simpa [pack] using fun i => h ((ordinal K).symm i))

theorem pack_poly [Fintype K] [Codec X] (f : K → X → List Bool) (hf : ∀ k, Poly (f k)) :
    Poly (fun x => pack (fun k => f k x)) := by
  have build (n : ℕ) (g : Fin n → X → List Bool) (hg : ∀ i, Poly (g i)) :
      Poly (fun x => List.ofFn (fun i => g i x)) := by
    induction n with
    | zero => simpa using (IntegerMultiplication.Code.Poly.const (X:=X) ([] : Bank))
    | succ n ih =>
      simp only [List.ofFn_succ]
      exact ((hg 0).pair (ih (fun i => g i.succ) (fun i => hg i.succ))).compose Easy.cons.poly
  exact build _ (fun i => f ((ordinal K).symm i)) (fun i => hf _)

def get [Fintype K] (k : K) (s : Bank) : List Bool := Iter.pick [] (s,tally (ordinal K k).val)

def modify [Fintype K] (k : K) (f : List Bool → List Bool) (s : Bank) := s.modify (ordinal K k).val f

theorem get_easy [Fintype K] (k : K) : Easy (get k) :=
  (Easy.identity.pair (Easy.const _)).compose (Iter.facile [])

theorem get_pack [Fintype K] (k : K) (s : Stacks K) : get k (pack s) = s k := by
  simpa only [get,pack,Function.comp_apply,Equiv.symm_apply_apply] using Iter.entry (s ∘ (ordinal K).symm) (ordinal K k) []

private theorem modifyAt_easy {A : Type} [Codec A] (f : A → A) (e : Easy f) (i : ℕ) :
    Easy (fun s : List A => s.modify i f) := by
  induction i with
  | zero =>
    convert Easy.listCase [] (((Easy.fst.compose e).pair Easy.snd).compose Easy.cons) using 1
    funext xs
    cases xs <;> rfl
  | succ i ih =>
    convert Easy.listCase [] ((Easy.fst.pair (Easy.snd.compose ih)).compose Easy.cons) using 1
    funext xs
    cases xs <;> rfl

theorem modify_easy [Fintype K] (k : K) (f : List Bool → List Bool) (e : Easy f) :
    Easy (modify k f) := modifyAt_easy f e _

theorem modify_pack [Fintype K] [DecidableEq K] (k : K) (f : List Bool → List Bool) (s : Stacks K) :
    modify k f (pack s) = pack (Function.update s k (f (s k))) := by
  apply List.ext_getElem
  · simp [modify,pack]
  · intro j hj hk
    have h : j < Fintype.card K := by simpa [pack] using hk
    let i : Fin (Fintype.card K) := ⟨j,h⟩
    by_cases eq : (ordinal K k).val=j
    · have same : (ordinal K).symm i = k := (ordinal K).symm_apply_eq.mpr (Fin.ext eq.symm)
      simp [modify,pack,eq,show (ordinal K).symm ⟨j,h⟩ = k from same]
    · have ne : (ordinal K).symm i ≠ k := fun he => eq (congrArg Fin.val ((ordinal K).symm_apply_eq.mp he)).symm
      simp [modify,pack,eq]
      exact (Function.update_of_ne ne _ _).symm

private def popBits (bits : List Bool) := bits.tail

private theorem pop_easy : Easy popBits := by
  convert Easy.listCase (X:=Bool) [] Easy.snd using 1
  funext xs
  cases xs <;> rfl

private theorem top_easy : Easy (List.head? (α:=Bool)) := by
  convert Easy.listCase none (Easy.fst.compose Easy.some) using 1
  funext xs
  cases xs <;> rfl

variable [Fintype Q] [Fintype K]

private def op (i : StackOp K Q) (p : Snapshot Q) : Snapshot Q :=
  match i with
  | .push k b q => (⟨q⟩,modify k (b :: ·) p.2)
  | .pop k f => (⟨f (get k p.2).head?⟩,modify k popBits p.2)
  | .goto q => (⟨q⟩,p.2)
  | .halt _ | .choose .. => p

private theorem op_poly (i : StackOp K Q) : Poly (op i) := by
  cases i with
  | push k b q => exact ((Easy.const (Label.mk q)).pair (Easy.snd.compose
      (modify_easy k _ (((Easy.const b).pair Easy.identity).compose Easy.cons)))).poly
  | pop k f => exact (((((Easy.snd.compose (get_easy k)).compose top_easy).compose
      (Easy.finite (fun z => Label.mk (f z)))).pair (Easy.snd.compose (modify_easy k _ pop_easy)))).poly
  | goto q => exact ((Easy.const (Label.mk q)).pair Easy.snd).poly
  | halt | choose => exact Poly.identity

def step (code : StackCode K Q) (p : Snapshot Q) := op (code p.1.val) p

private theorem step_poly (code : StackCode K Q) : Poly (step code) :=
  select_poly Prod.fst Easy.fst.poly (fun q => op (code q)) (fun q => op_poly (code q)) id Poly.identity

private theorem size_modify (f : List Bool → List Bool) (inc : ∀ x, size (f x) ≤ size x+2)
    (s : Bank) (i : ℕ) : size (s.modify i f) ≤ size s+2 := by
  induction s generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp only [List.modify_zero_cons,size_cons]; have := inc x; omega
    | succ i => simp only [List.modify_succ_cons,size_cons]; have := ih i; omega

private theorem step_size (code : StackCode K Q) (p : Snapshot Q) :
    size (step code p) ≤ size p + (2*Fintype.card Q+3) := by
  have tail (s : List Bool) : size (popBits s) ≤ size s+2 := by
    cases s <;> simp [popBits]
    omega
  unfold step
  cases code p.1.val with
  | push k b q =>
    have inc := size_modify (b::·) (by intro x; simp; omega) p.2 (ordinal K k).val
    simp only [op,size_prod,modify]; have := label_size q; omega
  | pop k f =>
    have inc := size_modify _ tail p.2 (ordinal K k).val
    simp only [op,size_prod,modify]; have := label_size (f (get k p.2).head?); omega
  | goto q => simp only [op,size_prod]; have := label_size q; omega
  | halt | choose => simp [op]

def run (code : StackCode K Q) := ride (step code)

theorem run_poly (code : StackCode K Q) : Poly (run code) :=
  Poly.rider _ (step_poly code) _ (step_size code)

omit [Fintype Q] in
private theorem step_eq [DecidableEq K] {code : StackCode K Q} {q t : Q} {s u : Stacks K}
    (hs : StackStep code q s t u) : step code (⟨q⟩,pack s) = (⟨t⟩,pack u) := by
  cases hs <;> simp_all [step,op,get_pack,modify_pack,popBits]

omit [Fintype Q] in
theorem run_at_halt [DecidableEq K] {code : StackCode K Q} {q t : Q} {s u : Stacks K} {a : Bool} {j : ℕ}
    (hs : StackRuns code j q s t u) (halt : code t = .halt a) (fuel : ℕ) (enough : j ≤ fuel) :
    run code (tally fuel,(⟨q⟩,pack s)) = (⟨t⟩,pack u) := by
  simp only [run,ride_t,tally_length]
  induction hs generalizing fuel with
  | nil q s =>
    apply Function.iterate_fixed
    simp [step,op,halt]
  | cons h _ ih =>
    cases fuel with
    | zero => omega
    | succ f => rw [Function.iterate_succ_apply,step_eq h]; exact ih halt _ (by omega)

end
end OAI.Computability.MultitapeWeakETH.StackInterpreter
