import OAI.Computability.BorderVNP.DiagonalNativeRoute
import OAI.Computability.BorderVNP.DiagonalNativeExpansionValue

/-! # Native argument preparation after the true routing choices

A successful deterministic public geometry and directory prefix is shared by every
preparation path. Each admitted sender word then gives one route return. Its post-fold
memory and its bank are the input for the physical argument preparation, retaining
any further guesses made by that code.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM TeamContraction Transmission
open scoped BigOperators Classical

variable {w : ℕ}

/-- Public geometry, interval layout and group emission before the four native routing stages. -/
def beforeRoute (epochs groups : Code) : Code := .block [epochs,Packing.Directory.ISA.program,groups]

private theorem prepare_iff {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m es t mt}
    (epochs groups arguments : Code) :
    Runs pub mac (prepareExpansion epochs groups arguments) s m es t mt ↔
      Runs pub mac (.seq (beforeRoute epochs groups) (.seq route arguments)) s m es t mt :=
  Runs.block_append_iff (a := [epochs,Packing.Directory.ISA.program,groups]) (b := [route,arguments])
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

variable (epochs groups arguments : Code) {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es t mt} (pre : Runs pub mac (beforeRoute epochs groups) s m es t mt)
    (det : (beforeRoute epochs groups).deterministic = true)

include pre det in
/-- On rejected routed inputs, completing the entire argument preparation is impossible. -/
theorem prepare_empty_of_route (empty : IsEmpty (Returns route pub mac t mt)) :
    IsEmpty (Returns (prepareExpansion epochs groups arguments) pub mac s m) := by
  constructor
  rintro ⟨⟨fs,z,mz⟩,r⟩
  obtain ⟨_,_,_,_,_,start,next⟩ := Runs.seq_iff.mp ((prepare_iff epochs groups arguments).mp r)
  obtain ⟨_,rfl,rfl⟩ := pre.unique_of_deterministic det start
  obtain ⟨u,mu,hs,_,_,rt,_⟩ := Runs.seq_iff.mp next
  exact empty.false ⟨(hs,u,mu),rt⟩

/-- Appending each possible native argument construction to its particular routed
state identifies every complete preparation return, with exact multiplicities. -/
noncomputable def prepareRouteEquiv {B : Type*} (routePaths : B ≃ Returns route pub mac t mt) :
    (Σ b : B, Returns arguments pub mac (routePaths b).val.2.1 (routePaths b).val.2.2) ≃
      Returns (prepareExpansion epochs groups arguments) pub mac s m := by
  let go (a : Σ b : B, Returns arguments pub mac (routePaths b).val.2.1 (routePaths b).val.2.2) :
      Returns (prepareExpansion epochs groups arguments) pub mac s m :=
    ⟨(es ++ ((routePaths a.1).val.1 ++ a.2.val.1),a.2.val.2),
      (prepare_iff epochs groups arguments).mpr (pre.seq ((routePaths a.1).property.seq a.2.property))⟩
  refine Equiv.ofBijective go ⟨?_,?_⟩
  · rintro ⟨a,x⟩ ⟨b,y⟩ eq
    have he : (es++((routePaths a).val.1++x.val.1),x.val.2) =
      (es++((routePaths b).val.1++y.val.1),y.val.2) := congrArg Subtype.val eq
    obtain ⟨h,state⟩ := Prod.mk.inj he
    have same := List.append_cancel_left h
    obtain ⟨ev,reg,mem⟩ := (routePaths a).property.eq_of_shared_events (routePaths b).property same
    have ab : a = b := routePaths.injective (Subtype.ext (Prod.ext ev (Prod.ext reg mem)))
    subst b
    have xy : x = y := Subtype.ext (Prod.ext (List.append_cancel_left same) state)
    subst y
    rfl
  · rintro ⟨⟨fs,z,mz⟩,r⟩
    obtain ⟨_,_,_,_,rfl,start,next⟩ := Runs.seq_iff.mp ((prepare_iff epochs groups arguments).mp r)
    obtain ⟨rfl,rfl,rfl⟩ := pre.unique_of_deterministic det start
    obtain ⟨v,mv,rs,as,rfl,rt,ra⟩ := Runs.seq_iff.mp next
    obtain ⟨b,rb⟩ := routePaths.surjective ⟨(rs,v,mv),rt⟩
    have e := congrArg Subtype.val rb
    change (routePaths b).val = (rs,v,mv) at e
    have eqs : (routePaths b).val.2.1 = v := congrArg (fun x => x.2.1) e
    have eqm : (routePaths b).val.2.2 = mv := congrArg (fun x => x.2.2) e
    refine ⟨⟨b,⟨(as,z,mz),eqs ▸ eqm ▸ ra⟩⟩,?_⟩
    apply Subtype.ext
    change (es ++ ((routePaths b).val.1 ++ as),(z,mz)) = _
    rw [e]

/-- Exact chronological guess and post-state components, including all subsequent
argument-preparation choices after the public and physical routing history. -/
theorem prepareRouteEquiv_val {B : Type*} (routePaths : B ≃ Returns route pub mac t mt)
    (b : B) (x : Returns arguments pub mac (routePaths b).val.2.1 (routePaths b).val.2.2) :
    (prepareRouteEquiv epochs groups arguments pre det routePaths ⟨b,x⟩).val =
      (es ++ ((routePaths b).val.1 ++ x.val.1),x.val.2) := rfl

/-- In particular a fitted deterministic typed argument constructor gives a single
complete preparation for each admitted physical sender word. Its actual output bank
and memory are precisely the constructor's output. -/
noncomputable def deterministicPreparationEquiv {B : Type*} (routePaths : B ≃ Returns route pub mac t mt)
    (argDet : arguments.deterministic = true)
    (build : ∀ b : B, Returns arguments pub mac (routePaths b).val.2.1 (routePaths b).val.2.2) :
    B ≃ Returns (prepareExpansion epochs groups arguments) pub mac s m := by
  let choice : B ≃ (Σ b : B, Returns arguments pub mac (routePaths b).val.2.1 (routePaths b).val.2.2) :=
    { toFun b := ⟨b,build b⟩
      invFun p := p.1
      left_inv _ := rfl
      right_inv := fun ⟨b,x⟩ => by
        obtain ⟨he,hr,hm⟩ := (build b).property.unique_of_deterministic argDet x.property
        have eq : build b = x := Subtype.ext (Prod.ext he (Prod.ext hr hm))
        exact congrArg (Sigma.mk b) eq }
  exact choice.trans (prepareRouteEquiv epochs groups arguments pre det routePaths)

/-- The chronological value after deterministic argument initialization. -/
theorem deterministicPreparationEquiv_val {B : Type*} (routePaths : B ≃ Returns route pub mac t mt)
    (argDet : arguments.deterministic = true)
    (build : ∀ b : B, Returns arguments pub mac (routePaths b).val.2.1 (routePaths b).val.2.2) (b : B) :
    (deterministicPreparationEquiv epochs groups arguments pre det routePaths argDet build b).val =
      (es ++ ((routePaths b).val.1 ++ (build b).val.1),(build b).val.2) := rfl

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
