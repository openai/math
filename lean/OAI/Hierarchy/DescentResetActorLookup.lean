import OAI.Hierarchy.DescentResetActorRaster

namespace OAI
/-! # One original base or terminal lookup for each relative reset actor address -/

namespace Hierarchy.DescentActorRaster
open DescentChosenRouter DescentColonies DescentContacts DescentCommonHost DescentRelativeContacts
open scoped Classical
noncomputable section
variable {V : Type} {n m : ℕ}

def complete (m : ℕ) (group : ℕ) (z : V×Endpoint (2^n)) : V×Endpoint (2^n) :=
  (z.1,((m+z.2.1.1,group*2^z.2.1.1+z.2.1.2),z.2.2))

theorem full_code (z : V×Endpoint (2^n)) (lower : m≤z.2.1.1) :
    complete m (coarseName m z) (shortName m z)=z := by
  rcases z with ⟨v,⟨⟨age,row⟩,tag⟩⟩
  change m ≤ age at lower
  simp only [complete,coarseName,shortName,Prod.mk.injEq,true_and,and_true]
  exact ⟨by omega,Nat.div_add_mod' row (2^(age-m))⟩

theorem code_match (z t : V×Endpoint (2^n)) (group : ℕ) (low : m≤t.2.1.1) :
    shortName m t=z ∧ coarseName m t=group ↔
      z.2.1.2<2^z.2.1.1 ∧ t=complete m group z := by
  constructor
  · rintro ⟨rfl,rfl⟩
    exact ⟨Nat.mod_lt _ (Nat.two_pow_pos _),(full_code t low).symm⟩
  · rintro ⟨small,rfl⟩
    rcases z with ⟨v,⟨⟨age,row⟩,tag⟩⟩
    change row < 2^age at small
    have quotient : (group*2^age+row)/2^age=group := by
      rw [Nat.mul_comm group (2^age),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt small,Nat.add_zero]
    simp [complete,shortName,coarseName,Nat.mod_eq_of_lt small,quotient]

variable [DecidableEq V] (b : V→ℕ) (low : ∀v,m≤b v)
def absoluteBase (u : V×ℕ) (x : Block m) (ok : u.2<2^(b u.1-m)) : BaseId b :=
  ⟨u.1,⟨x.val*2^(b u.1-m)+u.2,by
    have f : 2^(b u.1) = 2^m*2^(b u.1-m) := by rw [←pow_add,show m+(b u.1-m)=b u.1 by have:=low u.1;omega]
    rw [f]
    calc
      _ < x.val*2^(b u.1-m)+2^(b u.1-m) := Nat.add_lt_add_left ok _
      _ = (x.val+1)*2^(b u.1-m) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ x.isLt⟩⟩

omit [DecidableEq V] in
theorem absolute_read (u : V×ℕ) (x : Block m) (ok : u.2<2^(b u.1-m)) :
    DescentCanonicalPorts.short (m:=m) b (absoluteBase b low u x ok)=u ∧
      DescentCanonicalPorts.coarse (m:=m) b (absoluteBase b low u x ok)=x.val := by
  rcases u with ⟨v,t⟩
  change t < 2^(b v-m) at ok
  have quotient : (x.val*2^(b v-m)+t)/2^(b v-m)=x.val := by
    rw [Nat.mul_comm x.val (2^(b v-m)),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt ok,Nat.add_zero]
  simp [absoluteBase,DescentCanonicalPorts.short,DescentCanonicalPorts.coarse,
    DescentCanonicalPorts.relative,Nat.mod_eq_of_lt ok,quotient]

end
end Hierarchy.DescentActorRaster

namespace Hierarchy.DescentSixParty.ResetInput
open DescentChosenRouter DescentCommonHost DescentRelativeContacts DescentContacts DescentCanonicalPorts
open DescentColonies DescentActorRaster
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "R" => Z.placement
local notation "m" => T.commonDepth

/-- Read the configured tree height at a single observed original terminal.
A populated directory with height zero still returns a live root. -/
def terminalEntry (s : Bool) (z : Z.V×Endpoint (2^Z.n)) : Option ℕ :=
  if present : ∃t,T.code t=z then some (((R).fallbackBook s present.choose).height) else none

theorem terminal_read (s : Bool) (z : Z.V×Endpoint (2^Z.n)) (hgt : ℕ) :
    terminalEntry Z T s z=some hgt ↔ ∃t,T.code t=z ∧ ((R).fallbackBook s t).height=hgt := by
  by_cases existsT : ∃t,T.code t=z
  · simp only [terminalEntry,dite_eq_left existsT,Option.some.injEq]
    constructor
    · intro h
      exact ⟨existsT.choose,existsT.choose_spec,h⟩
    · rintro ⟨t,code,eqn⟩
      rw [T.code.injective (existsT.choose_spec.trans code.symm)]
      exact eqn
  · simp [terminalEntry,existsT,show ¬∃t,T.code t=z ∧ ((R).fallbackBook s t).height=hgt
      from fun ⟨t,yes,_⟩=>existsT ⟨t,yes⟩]

def activeBase (u : Z.V×ℕ) (x : DescentActorRaster.Block m) : Prop :=
  if ok : u.2<2^((R).b u.1-m) then
    absoluteBase (R).b T.commonLow u x ok∉validBases (R).b (R).keys ∧ ¬(R).hub u.1
  else False

theorem good_query (s : Bool) (u : Z.V×ℕ) (cell : (DescentCommonPalette.rotor Z.graph).Site)
    (x : DescentActorRaster.Block m) : emits Z T (.good s u cell) x ↔ activeBase Z T u x := by
  constructor
  · rintro ⟨g,hname,hgroup⟩
    have legal : u.2<2^((R).b u.1-m) := by
      rw [←hname]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [activeBase,dite_eq_left legal]
    have read:=absolute_read (R).b T.commonLow u x legal
    have eqn : absoluteBase (R).b T.commonLow u x legal=g.val :=
      DescentCanonicalPorts.recover (R).b (read.2.trans hgroup.symm) (read.1.trans hname.symm)
    rw [eqn]
    have host : g.val.1 = u.1 := congrArg Prod.fst hname
    exact ⟨g.property.1,host ▸ g.property.2⟩
  · intro yes
    unfold activeBase at yes
    split at yes
    next legal =>
      let base := absoluteBase (R).b T.commonLow u x legal
      have read:=absolute_read (R).b T.commonLow u x legal
      exact ⟨⟨base,yes⟩,read.1,read.2⟩
    next => contradiction

theorem fall_query (s : Bool) (z : Z.V×Endpoint (2^Z.n)) (ps : List Bool) (x : DescentActorRaster.Block m) :
    emits Z T (.fall s z ps) x ↔ z.2.1.2<2^z.2.1.1 ∧
      ∃hgt,terminalEntry Z T s (complete m x.val z)=some hgt ∧ ps.length≤hgt := by
  constructor
  · rintro ⟨t,name,group,depth⟩
    have pair := (code_match z (T.code t) x.val (T.codeLegal t).1).mp ⟨name,group⟩
    exact ⟨pair.1,_,(terminal_read Z T s _ _).mpr ⟨t,pair.2,rfl⟩,depth⟩
  · rintro ⟨legal,hgt,found,fits⟩
    obtain ⟨t,code,rfl⟩:=(terminal_read Z T s _ _).mp found
    have result := (code_match z (T.code t) x.val (T.codeLegal t).1).mpr ⟨legal,code⟩
    exact ⟨t,result.1,result.2,fits⟩

theorem trunk_query (s : Bool) (z : Z.V×Endpoint (2^Z.n)) (x : DescentActorRaster.Block m) :
    emits Z T (.trunk s z) x ↔ z.2.1.2<2^z.2.1.1 ∧
      (terminalEntry Z T s (complete m x.val z)).isSome=true := by
  constructor
  · rintro ⟨t,name,coord⟩
    have h:=(code_match z (T.code t) x.val (T.codeLegal t).1).mp ⟨name,coord⟩
    obtain ⟨g,found⟩ : ∃hgt,terminalEntry Z T s (complete m x.val z)=some hgt :=
      ⟨_,(terminal_read Z T s _ _).mpr ⟨t,h.2,rfl⟩⟩
    exact ⟨h.1,by simp [found]⟩
  · rintro ⟨legal,someEntry⟩
    cases hentry:terminalEntry Z T s (complete m x.val z) with
    | none=>simp [hentry] at someEntry
    | some hgt=>
      obtain ⟨t,name,_⟩:=(terminal_read Z T s _ _).mp hentry
      exact ⟨t,(code_match z (T.code t) x.val (T.codeLegal t).1).mpr ⟨legal,name⟩⟩

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
