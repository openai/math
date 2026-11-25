import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntax
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxAddress
import Batteries.Tactic.OpenPrivate

/-! # Numerical transitions of the structured-program compiler

A row stores the next site and at most one stack change. Stack zero carries
return addresses, and stack `i+1` is the source program's register `i`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Transition

open IntegerMultiplication

abbrev Symbol := ℕ ⊕ Site
abbrev Heads := List (Option Symbol)
abbrev Result := Option (Option Site × Option (ℕ × Option Symbol))
abbrev Row := Option (Option Site × Option (Option Symbol))

def rowAt (r : Result) (j : ℕ) : Row :=
  r.map fun (q, change) => (q, change.bind fun (i,a) => if i = j then some a else none)

def readHead (heads : Heads) (i : ℕ) : Option Symbol := heads.getD i none

def fields (n : ℕ) : List ℕ := (Encodable.decode (α := List ℕ) n).getD []

def resolve (sites : List Site) (s : Site) : Option Site :=
  if sites.idxOf s < sites.length then some s else none

def go (q : Option Site) : Result := some (q, none)

def act (i : ℕ) (a : Option Symbol) (q : Option Site) : Result := some (q, some (i,a))

def ret (heads : Heads) : Result :=
  ((readHead heads 0).bind Sum.getRight?).bind fun p => act 0 none (some p)

def look (options : List (Option ℕ)) (sites : List Site) (heads : Heads)
    (scope : List ℕ) (i : ℕ) (branches : List ℕ) : Result :=
  let select (v : Option ℕ) := go (resolve sites (scope, branches.getD (options.idxOf v) 0))
  (readHead heads (i+1)).elim (select none) fun s => (s.getLeft?).bind (fun v => select (some v))

def instruction (options : List (Option ℕ)) (sites : List Site) (heads : Heads)
    (scope : List ℕ) (args : List ℕ) : Result :=
  let op := args.getD 0 0
  let a := args.getD 1 0
  let b := args.getD 2 0
  if op = 0 then go none
  else if op = 1 then act (a+1) (some (.inl b)) none
  else if op = 2 then act (a+1) none none
  else if op = 3 then look options sites heads scope a (args.drop 2)
  else if op = 4 then (resolve sites (scope,b)).bind (fun p =>
    act 0 (some (.inr p)) (resolve sites (scope,a)))
  else if op = 5 then go (resolve sites (a :: scope,a))
  else if op = 6 then scope[a]?.bind (fun p => go (resolve sites (scope.drop a,p)))
  else none

def step (options : List (Option ℕ)) (sites : List Site) (heads : Heads)
    (q : Option Site) : Result :=
  q.elim (ret heads) fun s => instruction options sites heads s.1 (fields s.2)

variable {A : Type} [Fintype A] (letter : A ↪ ℕ) (U : List (Prog.Loc A))

/-- Codes of look symbols in exactly the order used in each source instruction. -/
noncomputable def options : List (Option ℕ) := Prog.options.map (Option.map letter)

noncomputable def pcKey (q : Prog.Pc U) : Option Site :=
  q.map (fun p => site letter p.val)

noncomputable def symbolKey (a : Prog.Sym U) : Symbol :=
  Sum.map letter (fun p => site letter p.val) a

def register (k : Prog.Ix U) : ℕ := k.elim 0 fun i => i.val + 1

omit [Fintype A] in
theorem register_injective : Function.Injective (register U) := by
  rintro (_ | ⟨a, ha⟩) (_ | ⟨b, hb⟩) h <;> simp_all [register]

noncomputable def actionKey (a : SM.Action (Prog.Sym U)) : Option (Option Symbol) :=
  match a with
  | .skip => none
  | .pop => some none
  | .push v => some (some (symbolKey letter U v))

noncomputable def nativeAt (r : Option (Prog.Pc U × (Prog.Ix U → SM.Action (Prog.Sym U))))
    (j : Prog.Ix U) : Row :=
  r.map (fun (q, ops) => (pcKey letter U q, actionKey letter U (ops j)))

private theorem row_go (q : Prog.Pc U) (j : Prog.Ix U) :
    rowAt (go (pcKey letter U q)) (register U j) =
      nativeAt letter U (some (q, fun _ => .skip)) j := rfl

private theorem row_act (q : Prog.Pc U) (i j : Prog.Ix U) (a : SM.Action (Prog.Sym U))
    (v : Option Symbol) (e : actionKey letter U a = some v) :
    rowAt (act (register U i) v (pcKey letter U q)) (register U j) =
      nativeAt letter U (some (q, Function.update (fun _ => .skip) i a)) j := by
  classical
  by_cases h : j = i
  · subst j
    simp [rowAt, act, nativeAt, e]
  · have ne := (register_injective U).ne (Ne.symm h)
    simp [rowAt, act, nativeAt, Function.update_of_ne h, ne, actionKey]

open private pc ix touched_mem from OAI.Computability.IntegerMultiplication.Prog.Compile

private theorem resolve_pc (Γ : Scope A) (c : Prog A) :
    resolve (U.map (site letter)) (Γ.map (key letter),key letter c) =
      pcKey letter U (pc U Γ c) := by
  classical
  change resolve _ (site letter (Γ,c)) = _
  have mem : site letter (Γ,c) ∈ U.map (site letter) ↔ (Γ,c) ∈ U := by
    simp [(site_injective letter).eq_iff]
  unfold resolve
  rw [if_congr (List.idxOf_lt_length_iff.trans mem) rfl rfl]
  by_cases h : (Γ,c) ∈ U <;> simp [pc, pcKey, h]

private theorem lookup_option (v : Option A) (f : Option A → Prog A) :
    (Prog.options.map (fun a => key letter (f a))).getD
      ((options letter).idxOf (v.map letter)) 0 = key letter (f v) := by
  classical
  have inj : Function.Injective (Option.map (⇑letter)) := Option.map_injective letter.injective
  have hm : v.map letter ∈ options letter := List.mem_map.mpr ⟨v,Prog.mem_options v,rfl⟩
  have lt := List.idxOf_lt_length_of_mem hm
  have hs : (options letter).length = (Prog.options (A := A)).length := by simp [options]
  have hj : (options letter).idxOf (v.map letter) < (Prog.options (A := A)).length := by omega
  have he := List.getElem_idxOf lt
  simp only [options, List.getElem_map] at he
  have hpoint := inj he
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa only [List.length_map] using hj)]
  simp only [Option.getD_some, List.getElem_map, options, hpoint]

/-- Expanding the numerical row at any physical stack gives exactly the
transition the P192 compiler specifies for that stack, for every read tuple. -/
theorem step_correct (q : Prog.Pc U) (stk : Prog.Ix U → Option (Prog.Sym U)) (heads : Heads)
    (reads : ∀ k, readHead heads (register U k) = (stk k).map (symbolKey letter U))
    (j : Prog.Ix U) :
    rowAt (step (options letter) (U.map (site letter)) heads (pcKey letter U q)) (register U j) =
      nativeAt letter U (Prog.compile U q stk) j := by
  classical
  cases q with
  | none =>
    change rowAt (ret heads) _ = _
    unfold ret
    rw [show readHead heads 0 = _ from reads none]
    cases h : stk none with
    | none => simp [Prog.compile, h, rowAt, nativeAt]
    | some a =>
      cases a with
      | inl v => simp [symbolKey, Prog.compile, h, rowAt, nativeAt]
      | inr p =>
        simpa only [symbolKey, Option.map_some, Sum.map_inr, Sum.getRight?_inr, Option.bind_some,
          Prog.compile, h, pcKey, register, Option.elim_none] using row_act letter U (some p) none j .pop none rfl
  | some p =>
    obtain ⟨⟨Γ,c⟩, mem⟩ := p
    change rowAt (instruction _ _ _ (Γ.map (key letter)) (fields (key letter c))) _ = _
    cases c with
    | pass =>
      simpa [key, fields, instruction, Prog.compile, pcKey] using row_go letter U none j
    | push i a =>
      have hi := Prog.ix_val U i (touched_mem U Γ (.push i a) mem)
      simpa [key, fields, instruction, Prog.compile, register, pcKey, hi] using
        row_act letter U none (some (ix U i)) j (.push (.inl a)) (some (.inl (letter a))) rfl
    | pop i =>
      have hi := Prog.ix_val U i (touched_mem U Γ (.pop i) mem)
      simpa [key, fields, instruction, Prog.compile, register, pcKey, hi] using
        row_act letter U none (some (ix U i)) j .pop none rfl
    | look i f =>
      have hi := Prog.ix_val U i (touched_mem U Γ (.look i f) mem)
      have hr := reads (some (ix U i))
      simp only [register, Option.elim_some, hi] at hr
      cases hv : stk (some (ix U i)) with
      | none =>
        have hb := lookup_option letter none f
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.map_none] at hb
        simpa [key, fields, instruction, look, Prog.compile, hr, hv, hb, resolve_pc] using
          row_go letter U (pc U Γ (f none)) j
      | some v =>
        cases v with
        | inl v =>
          have hb := lookup_option letter (some v) f
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.map_some] at hb
          simpa [key, fields, instruction, look, Prog.compile, hr, hv, symbolKey, hb, resolve_pc] using
            row_go letter U (pc U Γ (f (some v))) j
        | inr p =>
          simp [key, fields, instruction, look, Prog.compile, hr, hv, symbolKey, nativeAt, rowAt]
    | join a b =>
      cases hp : pc U Γ b with
      | none => simp [key, fields, instruction, Prog.compile, resolve_pc, hp, pcKey, nativeAt, rowAt]
      | some p =>
        simpa [key, fields, instruction, Prog.compile, resolve_pc, hp, pcKey, register] using
          row_act letter U (pc U Γ a) none j (.push (.inr p)) (some (.inr (site letter p.val))) rfl
    | tie a =>
      have dest := resolve_pc letter U (a::Γ) a
      rw [List.map_cons] at dest
      simpa [key, fields, instruction, Prog.compile, dest] using row_go letter U (pc U (a::Γ) a) j
    | again i =>
      cases hp : Γ[i]? with
      | none => simp [key, fields, instruction, Prog.compile, hp, nativeAt, rowAt]
      | some a =>
        have dest := resolve_pc letter U (Γ.drop i) a
        rw [List.map_drop] at dest
        simpa [key, fields, instruction, Prog.compile, hp, dest] using row_go letter U (pc U (Γ.drop i) a) j

end GeneratorSyntax.Transition

end NearSquareRoot
end Computability
end OAI
