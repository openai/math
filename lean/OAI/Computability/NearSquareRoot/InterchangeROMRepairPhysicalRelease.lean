import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalRealize
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalBank

/-! # Bounded release of the selected repair program on a packed bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Physical

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip CommonRegisters Space InterchangeROM

variable {R V U L X : Type} [Field R] [Fintype V] [Fintype U] {m : ℕ}
    {t : Spec R V U m} {half : R} {tag : X → Fin m → Bool} {fw bw : (X → R) → X → R}
    {advance : Bank R L X V → Bank R L X V} {wide : Bank R L X V → List Tree}
    {short : Bank R L X U → List Tree}

/-- The compiled command's input, output, and resource bounds are independent
of any arbitrary model for malformed tape data. -/
theorem bounded_from_actual (n q r : ℕ) (hw : ∀ x, (wide x).length = n) (hs : ∀ x, (short x).length = q)
    (bwide : ∀ x, small r (wide x)) (bshort : ∀ y, small r (short y)) (s : ℕ)
    (c : Leaf → Cmd) (charge : Leaf → List Tree → Allowance) (header : Tree) (env : Env)
    (act : Actual (Transition t half tag fw bw advance wide short) c charge header env)
    (stage child loc cap depth : ℕ)
    (cost : ∀ a xs, Inputs wide short a xs →
      (charge a xs).time ≤ loc + price stage q m (0,a)*child ∧
      (charge a xs).cap ≤ cap ∧ (charge a xs).depth ≤ depth)
    (x : Bank R L X V) (deck : Deck) (base : ℕ) (bg : DeckCap base deck) :
    let v := header.count+2+(7*n+2*q)*(r+1)
    let ov := 256*(v+1)
    BoundedFits env (command c (steps n s)) (pile 0 (packet header (wide x)) deck)
      (pile 0 (packet header (wide (schedule t half tag fw bw (advance^[s]) x))) deck)
      (1+(4*s+8)*(loc+3*n*ov+2)+(4*s*stage+4*q*m)*child)
      (base+cap+ov) (depth+ov+1) := by
  obtain ⟨model,sem,hreal⟩ := model_of_actual act
  have e := command_bounded hreal _ _ (ready_steps sem (inputs_domains ..) n hw s x) deck base bg
  dsimp only at e
  rw [run_steps sem n hw s x] at e
  obtain ⟨ht,hc,hd⟩ := allowance_steps sem n q r hw hs bwide bshort header s stage child loc cap depth charge cost x
  exact e.mono ht (by omega) hd

open InterchangeROMRepair.Physical.LocalTable.Lift
open InterchangeROMTable

/-- The encoded length of each lane stays linear in the number of records
times the payload width, including the zero-width field case. -/
theorem bank_small {A X : Type} {P : A → Type} {p l n : ℕ} (rows : Series A)
    (pay : (a : A) → Series (P a)) (key : (a : A) → P a → X) (width : ℕ)
    (hw : ∀ a, (pay a).count ≤ width) (x : Bank (ZMod (p+1)) (Fin l) X (Fin n)) :
    small (1+rows.count*(2+width*(2*p+2))) (bank rows pay key x) := by
  have stripe_size {T : Type} (s : Series T) (data : T → Tree) (k : ℕ)
      (h : ∀ u, (data u).count ≤ k) : (stripe s data).count ≤ 1+s.count*(k+1) := by
    have aux (l : List T) : (Task.forest data l).count ≤ 1+l.length*(k+1) := by
      induction l with
      | nil => simp [Tree.count]
      | cons a l ih =>
        simp only [Task.forest_cons,Tree.count,List.length_cons,Nat.add_mul,Nat.one_mul]
        have := h a
        omega
    simpa only [stripe,Series.tab,Task.forest_map,id_eq,Series.count] using aux s.explore
  intro u hu
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
  have payload_size (a : A) :
      (stripe (pay a) fun j => numeral (coords key x a j i).val).count ≤ 1+width*(2*p+2) := by
    have digit (j : P a) : (numeral (coords key x a j i).val).count ≤ 2*p+1 := by
      change size (tally _) ≤ _
      rw [size_tally,tally,List.length_replicate]
      have h := ZMod.val_lt (coords key x a j i)
      omega
    have h := stripe_size (pay a) _ _ digit
    apply h.trans
    simpa only [Nat.add_assoc] using Nat.add_le_add_left (Nat.mul_le_mul_right (2*p+2) (hw a)) 1
  have h := stripe_size rows _ _ payload_size
  simpa only [show (1+width*(2*p+2))+1=2+width*(2*p+2) by omega] using h

end InterchangeROMRepair.Physical

end

end NearSquareRoot
end Computability
end OAI
