import OAI.Hierarchy.DescentExteriorShelfOperands
import OAI.Hierarchy.DescentExteriorFlight
import OAI.Hierarchy.DescentExteriorPublicPins

namespace OAI
/-! # The native output columns certify the unique two exterior planes -/
namespace Hierarchy.DescentExteriorFetch
open DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {w j r t e : ℕ}
local notation "R" => 2^(j+r)
local notation "n" => e*R
local notation "k" => j+(j+r)
local notation "I" => Fin n

structure Capacity (g : Banks) (w j r t e start : ℕ) : Prop where
  fits : ∀b∈g.all,b.Fits w start
  keys : e*2^(j+r)≤g.key.size
  starts : e*2^(j+r)≤g.slab.size
  offsets : 2^(keyBits j r)≤g.offsets.size
  source : 2^(keyBits j r)≤g.source.size
  data : e*2^(j+r)≤g.data.size
  table : 2^(keyBits j r)*2^(2^j*t)≤g.table.size

private theorem cast_inj {d w : ℕ} (fit : d≤w) (x y : Word d) :
    (x.val:Word w)=(y.val:Word w) ↔ x=y := by
  rw [Fin.ext_iff,Fin.val_cast_of_lt (x.isLt.trans_le (Nat.pow_le_pow_right (by decide) fit)),
    Fin.val_cast_of_lt (y.isLt.trans_le (Nat.pow_le_pow_right (by decide) fit)),Fin.ext_iff]

theorem compare_value (wordPos : 0<w) (wordRoom : 2^j*t≤w)
    (g : Banks) (guess : Bank) (s : Fin 2) (start : ℕ) (M : Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) (pm : Memory w)
    (capacity : Capacity g w j r t e start)
    (loaded : Inputs g s.castSucc M (passInputs x z s.castSucc) pm) (guessFit : guess.Fits w start)
    (guessRows : n≤guess.size) (copy : ∀i:I,pm (guess.base+i.val)=
      ((gathered z (phase s,false,slab i,dest i)).val:Word w)) (i : I) :
    (compare g guess).eval pm (i.val:Word w)=0 ↔
      gathered z (phase s,false,slab i,dest i)=result s.castSucc M (passInputs x z s.castSucc) i := by
  have trueWord:=read g capacity.fits capacity.keys capacity.starts capacity.offsets capacity.source
    capacity.data capacity.table s.castSucc M _ pm loaded i
  have incoming : guess.read pm (i.val:Word w)=pm (guess.base+i.val) := by
    have inside := i.isLt.trans_le guessRows
    simp only [Bank.read,Fin.val_cast_of_lt (inside.trans guessFit.2.1),Nat.mod_eq_of_lt inside]
  have one : (1:Word w)≠0 := by
    have lim : 1<2^w := Nat.one_lt_pow (by omega) (by decide)
    intro eqn
    have vals := congrArg Fin.val eqn
    simp [Nat.mod_eq_of_lt lim] at vals
  simp only [compare,Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,
    trueWord,incoming,copy]
  by_cases eqn : gathered z (phase s,false,slab i,dest i)=result s.castSucc M (passInputs x z s.castSucc) i
  · simp [eqn]
  · have bad : ((result s.castSucc M (passInputs x z s.castSucc) i).val:Word w)≠
        ((gathered z (phase s,false,slab i,dest i)).val:Word w) :=
      fun h=>eqn ((cast_inj wordRoom _ _).mp h).symm
    simp [bad,eqn,one]


theorem zero_columns (keyAt start : ℕ) (kb : KeyBanks) (g : Fin 3→Banks) (guess : Fin 2→Bank)
    (ready : ∀s,(columns g guess s).Fits w start) (M : Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) (m : Memory w)
    (cap : ∀s,Capacity (g s) w j r t e start)
    (input : ∀s,Inputs (g s) s M (passInputs x z s)
      (ProtocolRAM.image keyAt n (joinKey kb) m))
    (guessFit : ∀s,(guess s).Fits w start) (guessRows : ∀s,n≤(guess s).size)
    (copy : ∀(s : Fin 2) (i : I),ProtocolRAM.image keyAt n (joinKey kb) m ((guess s).base+i.val)=
      ((gathered z (phase s,false,slab i,dest i)).val:Word w)) (wordPos : 0<w) (wordRoom : 2^j*t≤w) :
    (∀s : Fin 2,∀i:I,finalMem keyAt start n kb g guess m (start+s.val*n+i.val)=0) ↔ z=canonical M x := by
  rw [←canonical_iff M x z,gathered_correct]
  have check (s : Fin 2) (i : I) :
      finalMem keyAt start n kb g guess m (start+s.val*n+i.val)=0 ↔
      gathered z (phase s,false,slab i,dest i)=result s.castSucc M (passInputs x z s.castSucc) i := by
    have columnAt := read_column keyAt start n kb g guess ready m s.castSucc i
    change finalMem keyAt start n kb g guess m (start+s.val*n+i.val)=_ at columnAt
    rw [columnAt]
    have col : columns g guess s.castSucc=compare (g s.castSucc) (guess s) := by fin_cases s <;>rfl
    rw [col]
    exact compare_value wordPos wordRoom _ _ s start M x z (ProtocolRAM.image keyAt n (joinKey kb) m) (cap _) (input _)
      (guessFit _) (guessRows _) (copy s) i
  simp_rw [check]
  let index (a : Fin e) (v : Rows j r) : I := finProdFinEquiv (a,rowOrd j r v)
  have orig (a : Fin e) (v : Rows j r) : slab (index a v)=a ∧ dest (index a v)=v := by
    simp [slab,dest,index]
  constructor
  · intro ok
    constructor
    · intro a v
      simpa [result,passInputs,DescentExterior.pass,phase,(orig a v).1,(orig a v).2] using ok 0 (index a v)
    · intro a v
      simpa [result,passInputs,DescentExterior.pass,phase,(orig a v).1,(orig a v).2] using ok 1 (index a v)
  · rintro ⟨a,b⟩ s i
    fin_cases s
    · exact a _ _
    · exact b _ _

theorem final_row (keyAt start : ℕ) (kb : KeyBanks) (g : Fin 3→Banks) (guess : Fin 2→Bank)
    (ready : ∀s,(columns g guess s).Fits w start) (M : Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) (m : Memory w)
    (cap : ∀s,Capacity (g s) w j r t e start)
    (input : ∀s,Inputs (g s) s M (passInputs x z s)
      (ProtocolRAM.image keyAt n (joinKey kb) m)) (i : I) :
    finalMem keyAt start n kb g guess m (start+2*n+i.val) = ((pack (fun l=>output (M (slab i)) (projected z true (slab i))
      (l,dest i))).val:Word w) := by
  have columnAt := read_column keyAt start n kb g guess ready m (2:Fin 3) i
  change finalMem keyAt start n kb g guess m (start+2*n+i.val)=_ at columnAt
  rw [columnAt]
  exact read _ (cap 2).fits (cap 2).keys (cap 2).starts (cap 2).offsets (cap 2).source
    (cap 2).data (cap 2).table 2 M _ (ProtocolRAM.image keyAt n (joinKey kb) m) (input 2) i

end
end Hierarchy.DescentExteriorFetch

end OAI
