import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalTables
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalScript

/-! # Numeric source matrices for the five ordinary repair leaves

One label bank has `n = labels * w` wide lanes and `c = labels * s` check
lanes. The block boundaries below match the parent script's saved banks. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.LocalTable

open Raw Matrix

inductive Kind
  | duplicate | extract | restore | copyCube | finish
  deriving DecidableEq, Repr

def Kind.leaf : Kind → Leaf
  | .duplicate => .duplicate
  | .extract => .extract
  | .restore => .restore
  | .copyCube => .copyCube
  | .finish => .finish

def input (k : Kind) (n c : ℕ) : ℕ :=
  match k with
  | .duplicate => n
  | .extract => n+n
  | .restore => n+(c+c)
  | .copyCube => (n+n)+n
  | .finish => ((n+n)+n)+n

def output (k : Kind) (n c : ℕ) : ℕ :=
  match k with
  | .duplicate => n+n
  | .extract => n+(c+c)
  | .restore => (n+n)+n
  | .copyCube => ((n+n)+n)+n
  | .finish => n

def matrix (k : Kind) (p labels w s m half : ℕ) (t : Tape) : Mat :=
  let n := labels*w
  let c := labels*s
  match k with
  | .duplicate => vcat n ident ident
  | .extract =>
    let H := perLabel s w (atSlot t (1+m) w)
    vcat n (hcat n zeros ident) (vcat c (hcat n zeros H) (hcat n H zeros))
  | .restore =>
    let G := perLabel w s (atSlot t (2+m) s)
    vcat (n+n) (vcat n (hcat n ident zeros) (hcat n zeros (hcat c zeros G)))
      (hcat n zeros (hcat c G zeros))
  | .copyCube => vcat ((n+n)+n) ident (hcat (n+n) (hcat n ident zeros) zeros)
  | .finish =>
    hcat ((n+n)+n) (hcat (n+n) (hcat n (add ident (scale half ident)) ident) (neg p ident))
      (neg p (scale half ident))

variable {P : Type*} [Primcodable P]

theorem pr_input (k : Kind) {n c : P → ℕ} (hn : Primrec n) (hc : Primrec c) :
    Primrec fun x => input k (n x) (c x) := by
  cases k <;> first
    | exact hn
    | exact Primrec.nat_add.comp hn hn
    | exact Primrec.nat_add.comp hn (Primrec.nat_add.comp hc hc)
    | exact Primrec.nat_add.comp (Primrec.nat_add.comp hn hn) hn
    | exact Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp hn hn) hn) hn

theorem pr_output (k : Kind) {n c : P → ℕ} (hn : Primrec n) (hc : Primrec c) :
    Primrec fun x => output k (n x) (c x) := by
  cases k <;> first
    | exact hn
    | exact Primrec.nat_add.comp hn hn
    | exact Primrec.nat_add.comp hn (Primrec.nat_add.comp hc hc)
    | exact Primrec.nat_add.comp (Primrec.nat_add.comp hn hn) hn
    | exact Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp hn hn) hn) hn

theorem pr_matrix (k : Kind) {p l w s m half : P → ℕ} {t : P → Tape}
    (hp : Primrec p) (hl : Primrec l) (hw : Primrec w) (hs : Primrec s) (hm : Primrec m)
    (hh : Primrec half) (ht : Primrec t) : EntryPR fun x =>
      matrix k (p x) (l x) (w x) (s x) (m x) (half x) (t x) := by
  have hn := Primrec.nat_mul.comp hl hw
  have hc := Primrec.nat_mul.comp hl hs
  have h2 := Primrec.nat_add.comp hn hn
  have h3 := Primrec.nat_add.comp h2 hn
  have z : EntryPR (fun _ : P => zeros) := .const 0
  have e := primrec_ident (X := P)
  cases k with
  | duplicate => exact pr_vcat hn e e
  | extract =>
    have H := pr_perLabel hs hw (primrec_atSlot ht (Primrec.nat_add.comp (.const 1) hm) hw)
    exact pr_vcat hn (pr_hcat hn z e) (pr_vcat hc (pr_hcat hn z H) (pr_hcat hn H z))
  | restore =>
    have G := pr_perLabel hw hs (primrec_atSlot ht (Primrec.nat_add.comp (.const 2) hm) hs)
    exact pr_vcat h2 (pr_vcat hn (pr_hcat hn e z) (pr_hcat hn z (pr_hcat hc z G)))
      (pr_hcat hn z (pr_hcat hc G z))
  | copyCube => exact pr_vcat h3 e (pr_hcat h2 (pr_hcat hn e z) z)
  | finish => exact pr_hcat h3 (pr_hcat h2 (pr_hcat hn (e.add (e.scale hh)) e) (e.neg hp)) ((e.scale hh).neg hp)

variable {p l w s m half : ℕ} (t : Tape)

theorem act_duplicate (x : Fin (l*w) → ZMod (p+1)) :
    act ((l*w)+(l*w)) (l*w) (matrix .duplicate p l w s m half t) x = cat x x := by
  simp [matrix,act_vcat]

theorem act_extract (x y : Fin l → Fin w → ZMod (p+1)) :
    act ((l*w)+((l*s)+(l*s))) ((l*w)+(l*w)) (matrix .extract p l w s m half t)
      (cat (flat x) (flat y)) =
    cat (flat y) (cat (flat fun a => (decode p w s m t).extract *ᵥ y a)
      (flat fun a => (decode p w s m t).extract *ᵥ x a)) := by
  simp only [matrix,act_vcat,act_hcat,act_zero,act_ident,zero_add,add_zero,act_perLabel]
  rfl

theorem act_restore (u : Fin l → Fin w → ZMod (p+1)) (v z : Fin l → Fin s → ZMod (p+1)) :
    act (((l*w)+(l*w))+(l*w)) ((l*w)+((l*s)+(l*s))) (matrix .restore p l w s m half t)
      (cat (flat u) (cat (flat v) (flat z))) =
    cat (cat (flat u) (flat fun a => (decode p w s m t).restore *ᵥ z a))
      (flat fun a => (decode p w s m t).restore *ᵥ v a) := by
  simp only [matrix,act_vcat,act_hcat,act_zero,act_ident,zero_add,add_zero,act_perLabel]
  rfl

theorem act_copyCube (u v z : Fin (l*w) → ZMod (p+1)) :
    act ((((l*w)+(l*w))+(l*w))+(l*w)) (((l*w)+(l*w))+(l*w)) (matrix .copyCube p l w s m half t)
      (cat (cat u v) z) = cat (cat (cat u v) z) u := by
  simp [matrix,act_vcat,act_hcat]

theorem act_finish (u v z c : Fin (l*w) → ZMod (p+1)) :
    act (l*w) ((((l*w)+(l*w))+(l*w))+(l*w)) (matrix .finish p l w s m half t)
      (cat (cat (cat u v) z) c) = u - (half : ZMod (p+1)) • (c-u) - z + v := by
  simp only [matrix,act_hcat,act_add,act_scale,act_ident,act_neg]
  ext i
  simp only [Pi.add_apply,Pi.smul_apply,Pi.neg_apply,Pi.sub_apply,smul_eq_mul]
  ring

end InterchangeROMRepair.Physical.LocalTable

end NearSquareRoot
end Computability
end OAI
