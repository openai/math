import OAI.Computability.NearSquareRoot.CRTControlledResidues
import OAI.Computability.NearSquareRoot.CRTPositionReadRows
import OAI.Computability.IntegerMultiplication.Staff.Nat

/-! # Serialized residue and singleton passes for a gathered XOR

The gathered source is the most significant native chunk and the destination is
the middle chunk. A packed pass contains its residue and one unary read per
destination position. A read equal to the chunk width disables that position.
The upper positions with insufficient guard space emit individual CNOTs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code

abbrev Op := (Fin 3 × Fin 3) ⊕ ((Tally × List Tally) ⊕ ((Tally × Tally) ⊕ (Tally × Tally)))
abbrev swapChunks (v : Fin 3 × Fin 3) : Op := .inl v
abbrev packed (v : Tally × List Tally) : Op := .inr (.inl v)
abbrev highCnot (v : Tally × Tally) : Op := .inr (.inr (.inl v))
abbrev tailSwap (v : Tally × Tally) : Op := .inr (.inr (.inr v))

@[fun_prop] theorem poly_left {A B : Type} [Codec A] [Codec B] : Code.Poly (@Sum.inl A B) :=
  (Easy.pair (Easy.const false) Easy.identity : Easy (fun a : A => (false,a))).poly

@[fun_prop] theorem poly_right {A B : Type} [Codec A] [Codec B] : Code.Poly (@Sum.inr A B) :=
  (Easy.pair (Easy.const true) Easy.identity : Easy (fun a : B => (true,a))).poly

private def optBits : Option Tally → List Bool
  | none => []
  | some v => true :: v.map (fun _ => false)

private theorem optBits_easy : Easy optBits := by
  have enc (t : Tally) : send (t.map (fun _ => false)) = send t := by
    induction t with
    | nil => rfl
    | cons u t ih => simp only [List.map_cons,send_cons,ih]; rfl
  have eq : (fun t : Option Tally => send (optBits t)) = send := by
    funext t
    cases t with
    | none => rfl
    | some v => simp only [optBits,send_cons,enc,send_some]; rfl
  change Task size send (fun t : Option Tally => send (optBits t))
  rw [eq]
  exact Task.self

private def normEntry (q : (Tally × List (Option Tally)) × Tally) : Tally :=
  let x := optBits (Iter.pick none (q.1.2,q.2))
  if x = [] ∨ q.1.1.length ≤ x.tail.length then q.1.1 else ruler x.tail

private theorem normEntry_poly : Code.Poly normEntry := by
  let get (q : (Tally × List (Option Tally)) × Tally) := optBits (Iter.pick none (q.1.2,q.2))
  have getEasy : Easy get := (show Easy (fun q : (Tally × List (Option Tally)) × Tally => (q.1.2,q.2)) by fun_prop).compose
    ((Iter.facile none).compose optBits_easy)
  have tailEasy : Easy (@List.tail Bool) := by
    convert (Easy.listCase ([] : List Bool) (Easy.snd (X := Bool) (Y := List Bool))) using 1
    funext t; cases t <;> rfl
  have tl : Easy (fun q => (get q).tail) := getEasy.compose tailEasy
  have nonempty : Easy (fun q => !(get q).isEmpty) := by
    have form : Easy (@List.isEmpty Bool) := by
      convert (Easy.listCase true (Easy.const (X := Bool × List Bool) false)) using 1
      funext t; cases t <;> rfl
    exact getEasy.compose (form.compose (Easy.finite (!·)))
  have valid := (tl.pair (show Easy (fun q : (Tally × List (Option Tally)) × Tally => q.1.1) by fun_prop)).compose Iter.small_easy
  have select := Code.Poly.choose nonempty.poly (Code.Poly.choose valid.poly tl.ruler.poly
    (show Easy (fun q : (Tally × List (Option Tally)) × Tally => q.1.1) by fun_prop).poly)
    (show Easy (fun q : (Tally × List (Option Tally)) × Tally => q.1.1) by fun_prop).poly
  convert select using 1
  funext q
  change (if get q = [] ∨ q.1.1.length ≤ (get q).tail.length then q.1.1 else ruler (get q).tail) =
    (bif !(get q).isEmpty then (bif Iter.small ((get q).tail,q.1.1) then ruler (get q).tail else q.1.1) else q.1.1)
  cases h : get q with
  | nil => simp
  | cons a t =>
    by_cases ht : t.length < q.1.1.length <;> simp [ht,Iter.small,Nat.not_le_of_lt,Nat.le_of_not_gt]

def normalize (q : Tally × List (Option Tally)) : List Tally :=
  polyPush normEntry (q,Iter.lineup q.1)

@[fun_prop] theorem normalize_poly : Code.Poly normalize :=
  (Code.Poly.identity.pair (Easy.fst.poly.compose Iter.poly_line)).compose
    (Code.Poly.push ([],[]) [] normEntry_poly)

theorem normalize_value {n : ℕ} (t : List (Option Tally)) :
    normalize (tally n,t) = List.ofFn fun j : Fin n =>
      tally (((decodePort t j).map Fin.val).getD n) := by
  simp only [normalize,polyPush,Iter.lined,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply,normEntry,decodePort,tally_length]
  cases eq : Iter.pick none (t,tally j.val) with
  | none => rfl
  | some b =>
    by_cases h : b.length < n
    · simp [optBits,h,Nat.not_le_of_lt h,ruler,tally,List.map_const']
    · simp [optBits,h,Nat.le_of_not_gt h]

abbrev PassData := Tally × Tally × List Tally
abbrev PassInput := PassData × Tally

def upperIndex (z : PassInput) : Tally :=
  ((cutLists (z.1.2.1,z.2)).2 ++ [()] |> fun u => (cutLists (u,z.1.1)).2)

private theorem upperIndex_easy : Easy upperIndex := by
  have h := (easy_cut (show Easy (fun z : PassInput => (z.1.2.1,z.2)) by fun_prop)).sndCompose
  exact (easy_cut ((((h.pair (Easy.const [()])).compose Easy.append).pair
    (show Easy (fun z : PassInput => z.1.1) by fun_prop)))).sndCompose

theorem upperIndex_length (z : PassInput) :
    (upperIndex z).length = z.1.1.length - ((z.2.length - z.1.2.1.length)+1) := by
  simp [upperIndex,cutLists]

def pass (z : PassInput) : List Op :=
  let n := z.1.1
  let g := z.1.2.1
  let p := z.2
  if p.length < g.length then [packed (p,z.1.2.2)]
  else
    let j := upperIndex z
    let b := Iter.pick n (z.1.2.2,j)
    if p.length-g.length < n.length ∧ n.length < j.length+2*g.length ∧ b.length<n.length then
      [highCnot (b,j)] else []

private theorem pickDefault_poly : Code.Poly (fun z : (List Tally × Tally) × Tally =>
    Iter.pick z.2 z.1) := by
  let dropped := fun z : (List Tally × Tally) × Tally => (cutLists (z.1.2,z.1.1)).2
  have dr : Easy dropped := (easy_cut (show Easy (fun z : (List Tally × Tally) × Tally => (z.1.2,z.1.1)) by fun_prop)).sndCompose
  have h := (dr.pair ((Easy.snd.pair (Easy.const [])).compose Easy.cons)).compose Easy.append
  convert (h.compose (Iter.leader ([] : Tally))).poly using 1
  funext z
  change (z.1.1.drop z.1.2.length).headD z.2 = (_ ++ [z.2]).headD []
  change _ = (z.1.1.drop z.1.2.length ++ [z.2]).headD []
  cases z.1.1.drop z.1.2.length <;> rfl

@[fun_prop] theorem pass_poly : Code.Poly pass := by
  let reg : Strip.Regime PassInput := ⟨size,send,Dom.base _⟩
  have num (f : PassInput → Tally) (h : Code.Poly f) : Staff.Realizes reg (fun z => (f z).length) := by
    change Code.Poly (fun z => tally (f z).length)
    simpa only [recover_tally] using h
  have n := num (fun z => z.1.1) (by fun_prop)
  have g := num (fun z => z.1.2.1) (by fun_prop)
  have p := num (fun z => z.2) (by fun_prop)
  have j := num upperIndex upperIndex_easy.poly
  let b := fun z : PassInput => Iter.pick z.1.1 (z.1.2.2,upperIndex z)
  have hb : Code.Poly b := (((show Code.Poly (fun z : PassInput => z.1.2.2) by fun_prop).pair upperIndex_easy.poly).pair
    (show Code.Poly (fun z : PassInput => z.1.1) by fun_prop)).compose pickDefault_poly
  have less (f h : PassInput → ℕ) (hf : Staff.Realizes reg f) (hh : Staff.Realizes reg h) :
      Code.Poly (fun z => decide (f z < h z)) := by
    change reg.Has (fun z => decide (f z < h z))
    simpa only [Iter.small,Function.comp_def,tally_length] using (Strip.Regime.Has.pair hf hh).ez Iter.small_easy
  have one {f : PassInput → Op} (h : Code.Poly f) : Code.Poly (fun z => [f z]) :=
    (h.pair (Code.Poly.const [])).compose Code.Poly.cons
  have yes : Code.Poly (fun z : PassInput => [packed (z.2,z.1.2.2)]) := one (by unfold packed; fun_prop)
  have high : Code.Poly (fun z : PassInput => [highCnot (b z,upperIndex z)]) :=
    one (((hb.pair upperIndex_easy.poly).compose poly_left).compose poly_right |>.compose poly_right)
  have a := less _ _ (p.minused g) n
  have c := less _ _ n (j.plus (g.plus g))
  have e := less _ _ (num b hb) n
  have answer := Code.Poly.choose (less _ _ p g) yes (Code.Poly.choose a
    (Code.Poly.choose c (Code.Poly.choose e high (Code.Poly.const [])) (Code.Poly.const [])) (Code.Poly.const []))
  convert answer using 1
  funext z
  change (if z.2.length < z.1.2.1.length then _ else
    if z.2.length-z.1.2.1.length < z.1.1.length ∧
      z.1.1.length < (upperIndex z).length+2*z.1.2.1.length ∧ (b z).length<z.1.1.length then _ else _) = _
  by_cases h₁ : z.2.length < z.1.2.1.length <;>
    by_cases h₂ : z.2.length-z.1.2.1.length < z.1.1.length <;>
    by_cases h₃ : z.1.1.length < (upperIndex z).length+(z.1.2.1.length+z.1.2.1.length) <;>
    by_cases h₄ : (b z).length < z.1.1.length <;> simp [h₁,h₂,h₃,h₄,two_mul]
  rfl

def passes (q : PassData) : List Op :=
  (polyPush pass (q,Iter.lineup (q.2.1 ++ q.2.1 ++ q.2.1))).flatten

@[fun_prop] theorem passes_poly : Code.Poly passes := by
  have t : Easy (fun q : PassData => q.2.1 ++ q.2.1 ++ q.2.1) := by fun_prop
  exact ((Code.Poly.identity.pair (t.poly.compose Iter.poly_line)).compose
    (Code.Poly.push ([],[],[]) [] pass_poly)).compose Easy.flatten.poly

theorem pass_value (n g r : ℕ) (t : List Tally) :
    pass ((tally n,tally g,t),tally r) =
      if r < g then [packed (tally r,t)] else
        let j := n-((r-g)+1)
        let b := Iter.pick (tally n) (t,tally j)
        if r-g<n ∧ n<j+2*g ∧ b.length<n then [highCnot (b,tally j)] else [] := by
  have h : upperIndex ((tally n,tally g,t),tally r) = tally (n-((r-g)+1)) := by
    rw [← recover_tally (upperIndex _),upperIndex_length]
    simp only [tally_length]
  simp only [pass,h,tally_length]

theorem passes_range (n g : ℕ) (t : List Tally) :
    passes (tally n,tally g,t) =
      (List.range (3*g)).flatMap (fun r => pass ((tally n,tally g,t),tally r)) := by
  have clock : tally g ++ tally g ++ tally g = tally (3*g) := by
    rw [← recover_tally (tally g ++ tally g ++ tally g)]
    apply congrArg tally
    simp only [List.length_append,tally_length]
    omega
  simp only [passes,polyPush,clock,Iter.lined,List.flatMap_def]
  apply congrArg List.flatten
  apply List.ext_getElem <;> simp

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
