import OAI.LinearAlgebra.SpectralBooks.SignedWitness

/-! # Canonical framed programs

A successful parse consumes exactly the canonical encoding of the program it
returns. The remaining input is unconstrained. Repeated rule keys and
incorrect work-tape arities cannot yield a partial or alternative parse.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace ProgramCode

open SignedMachine
open private Parser readNat natField readFields three symbol direction transition action rule table
  symbolBits directionBits outputBits moveBits transitionBits actionBits ruleBits bodyBits
  from OAI.LinearAlgebra.SpectralBooks.SignedWitness

private abbrev Parses {α : Type} (f : Parser α) (enc : α → List Bool) (good : α → Prop) :=
  ∀ {input x rest}, f.run input = some (x, rest) → input = enc x ++ rest ∧ good x

private theorem nat_parses : Parses natField unary (fun _ ↦ True) := by
  intro input k rest h
  change readNat input = some (k,rest) at h
  induction input generalizing k rest with
  | nil => simp [readNat] at h
  | cons b bs ih =>
    cases b with
    | false =>
      obtain ⟨rfl, rfl⟩ := (by simpa [readNat] using h : 0 = k ∧ bs = rest)
      exact ⟨rfl,trivial⟩
    | true =>
      cases he : readNat bs with
      | none => simp [readNat,he] at h
      | some p =>
        obtain ⟨l, tail⟩ := p
        simp [readNat,he] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨congrArg (List.cons true) (ih he).1, trivial⟩

local macro "parse_bind" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| simp only [StateT.run_bind, StateT.run_pure, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] $loc)

private theorem three_parses {α : Type} (a b c : α) (enc : α → List Bool)
    (ha : enc a = unary 0) (hb : enc b = unary 1) (hc : enc c = unary 2) :
    Parses (three a b c) enc (fun _ ↦ True) := by
  intro inp x rest h
  unfold three at h
  parse_bind at h
  obtain ⟨⟨l, tail⟩, hl, h⟩ := h
  have hpre := (nat_parses hl).1
  cases l with
  | zero =>
    change some (a, tail) = some (x,rest) at h
    cases h
    exact ⟨ha ▸ hpre,trivial⟩
  | succ l =>
    cases l with
    | zero =>
      change some (b, tail) = some (x,rest) at h
      cases h
      exact ⟨hb ▸ hpre,trivial⟩
    | succ l =>
      cases l with
      | zero =>
        change some (c, tail) = some (x,rest) at h
        cases h
        exact ⟨hc ▸ hpre,trivial⟩
      | succ => contradiction

private theorem symbol_parses : Parses symbol symbolBits (fun _ ↦ True) :=
  three_parses Symbol.blank Symbol.zero Symbol.one symbolBits rfl rfl rfl

private theorem direction_parses : Parses direction directionBits (fun _ ↦ True) :=
  three_parses Direction.left Direction.stay Direction.right directionBits rfl rfl rfl

private theorem output_parses : Parses (three .zero .pos .neg) outputBits (fun _ ↦ True) :=
  three_parses .zero .pos .neg outputBits rfl rfl rfl

private theorem fields_parses {α : Type} {f : Parser α} {enc : α → List Bool} {good : α → Prop}
    (hf : Parses f enc good) (n : ℕ) : Parses (readFields f n) (List.flatMap enc)
      (fun xs ↦ xs.length = n ∧ ∀ x ∈ xs, good x) := by
  induction n with
  | zero =>
    intro inp xs rest h
    change some ([],inp) = some (xs, rest) at h
    cases h
    simp
  | succ n ih =>
    intro inp xs rest h
    rw [readFields] at h
    parse_bind at h
    obtain ⟨⟨x, mid⟩, hx, ⟨ys, tail⟩, hy, rfl, rfl⟩ := h
    obtain ⟨rfl, hg⟩ := hf hx
    obtain ⟨rfl, hl, hgs⟩ := ih hy
    simpa [hl, hg, List.append_assoc] using hgs

private theorem move_parses : Parses (Prod.mk <$> symbol <*> direction) moveBits (fun _ ↦ True) := by
  intro inp x rest h
  simp only [StateT.run_seq, StateT.run_map, Option.bind_eq_bind, Option.map_eq_map,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨_,_⟩, ⟨⟨s,mid⟩, hs, rfl,rfl⟩, ⟨d, tail⟩, hd, rfl,rfl⟩ := h
  obtain ⟨rfl, _⟩ := symbol_parses hs
  obtain ⟨rfl, _⟩ := direction_parses hd
  simp [moveBits, List.append_assoc]

private theorem transition_parses (k : ℕ) :
    Parses (transition k) transitionBits (fun t ↦ t.workMoves.length = k) := by
  intro inp t rest h
  unfold transition at h
  parse_bind at h
  obtain ⟨⟨st, _⟩, hs, ⟨d, _⟩, hd, ⟨ms, _⟩, hm, rfl, rfl⟩ := h
  obtain ⟨rfl, _⟩ := nat_parses hs
  obtain ⟨rfl, _⟩ := direction_parses hd
  obtain ⟨rfl, hl, _⟩ := fields_parses move_parses k hm
  exact ⟨by simp [transitionBits, List.append_assoc],hl⟩

private theorem action_parses (k : ℕ) : Parses (action k) actionBits (ActionArity k) := by
  intro inp a rest h
  unfold action at h
  parse_bind at h
  obtain ⟨⟨tag, mid⟩, hn, h⟩ := h
  obtain ⟨rfl, _⟩ := nat_parses hn
  cases tag with
  | zero =>
    dsimp only at h
    parse_bind at h
    obtain ⟨⟨o, _⟩, ho, rfl, rfl⟩ := h
    obtain ⟨rfl,_⟩ := output_parses ho
    exact ⟨by simp [actionBits, List.append_assoc],trivial⟩
  | succ tag =>
    cases tag with
    | zero =>
      dsimp only at h
      parse_bind at h
      obtain ⟨⟨t, _⟩, ht, rfl, rfl⟩ := h
      obtain ⟨rfl,hgt⟩ := transition_parses k ht
      exact ⟨by simp [actionBits, List.append_assoc],hgt⟩
    | succ tag =>
      cases tag with
      | zero =>
        dsimp only at h
        parse_bind at h
        obtain ⟨⟨s,_⟩, hs, ⟨t,_⟩, ht, rfl,rfl⟩ := h
        obtain ⟨rfl,hgs⟩ := transition_parses k hs
        obtain ⟨rfl,hgt⟩ := transition_parses k ht
        exact ⟨by simp [actionBits, List.append_assoc],hgs,hgt⟩
      | succ => contradiction

private theorem rule_parses (k : ℕ) : Parses (rule k) ruleBits
    (fun r ↦ r.workSymbols.length = k ∧ ActionArity k r.action) := by
  intro inp r rest h
  unfold rule at h
  parse_bind at h
  obtain ⟨⟨st,_⟩, hs, ⟨s,_⟩, hsy, ⟨ss,_⟩, hrs, ⟨a,_⟩, ha, rfl,rfl⟩ := h
  obtain ⟨rfl,_⟩ := nat_parses hs
  obtain ⟨rfl,_⟩ := symbol_parses hsy
  obtain ⟨rfl,hlen,_⟩ := fields_parses symbol_parses k hrs
  obtain ⟨rfl,hga⟩ := action_parses k ha
  exact ⟨by simp [ruleBits,List.append_assoc],hlen,hga⟩

private theorem table_parses (k : ℕ) : Parses (table k)
    (fun rs ↦ unary rs.length ++ rs.flatMap ruleBits) (fun rs ↦ WellFormed ⟨k,rs⟩) := by
  intro inp rs rest h
  unfold table at h
  parse_bind at h
  obtain ⟨⟨l,_⟩, hl, ⟨xs,tail⟩, hxs, ⟨u,s⟩, hu, rfl,rfl⟩ := h
  obtain ⟨rfl,_⟩ := nat_parses hl
  obtain ⟨rfl,hlen, hall⟩ := fields_parses (rule_parses k) l hxs
  by_cases hn : (xs.map (fun r ↦ (r.state,r.inputSymbol,r.workSymbols))).Nodup
  · simp [guard,hn] at hu
    obtain ⟨rfl, rfl⟩ := hu
    exact ⟨by simp [hlen,List.append_assoc],hn,hall⟩
  · simp [guard,hn] at hu

private theorem decodeBody_sound {b : List Bool} {p : Program} (h : decodeBody b = some p) :
    b = bodyBits p ∧ WellFormed p := by
  unfold decodeBody at h
  cases he : readNat b with
  | none => simp [he] at h
  | some pair =>
    obtain ⟨k,mid⟩ := pair
    cases hf : (table k).run mid with
    | none => simp [he,hf] at h
    | some pair =>
      obtain ⟨rs,rest⟩ := pair
      cases rest with
      | nil =>
        simp [he,hf] at h
        subst p
        obtain ⟨rfl, _⟩ := nat_parses (show natField.run b = _ from he)
        obtain ⟨h1,h2⟩ := table_parses k hf
        exact ⟨by simp [h1,bodyBits,List.append_assoc],h2⟩
      | cons => simp [he,hf] at h

/-- Exact inverse of the parser, including rejection of repeated keys. -/
theorem decode_eq_some_iff {bits : List Bool} {p : Program} :
    decode bits = some p ↔ WellFormed p ∧ ∃ data, bits = encode p ++ data := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases he : readNat bits with
    | none => simp [decode,he] at h
    | some pair =>
      obtain ⟨k,rest⟩ := pair
      by_cases hk : k ≤ rest.length
      · simp [decode,he,hk] at h
        obtain ⟨hb,hg⟩ := decodeBody_sound h
        obtain ⟨hp,_⟩ := nat_parses (show natField.run bits = _ from he)
        have hlen := congrArg List.length hb
        simp [Nat.min_eq_left hk] at hlen
        refine ⟨hg, rest.drop k, ?_⟩
        rw [hp, encode, ← hlen, ← hb, List.append_assoc, List.take_append_drop]
      · simp [decode,he,hk] at h
  · rintro ⟨hg, data,rfl⟩
    exact decode_encode_append _ hg _

end ProgramCode

end SpectralBooks
end LinearAlgebra
end OAI
