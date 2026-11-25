import OAI.ThreeFlat.RAM.TraceBucketCapacity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI
/-! # The native leaf image uses one site count times a local polynomial -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Diagonal.TraceSourceOwner

/-- Base addresses can occupy high scratch. The size of source and address operands
computed before adding those bases is linear in the number of physical trace sites. -/
theorem footprint_le (s : Layout) {n : ℕ} (hn : 1≤n) (hrows : 0<s.shape.rows)
    (lanes : s.lowRows≤ s.shape.rows) (depth : s.depth≤n) (low : s.low≤n)
    (header : s.shape.header+s.shape.ticks≤2*s.shape.rows) (slots : s.slots≤n) (arcs : s.arcs≤n)
    (stride : s.shape.stride≤n) (lib : s.equalId+s.zeroId+s.unitId≤n) :
    s.footprint≤200*s.shape.rows*(n+1)^3 := by
  let R := s.shape.rows
  have hR : 1≤R := hrows
  have hc : s.shape.cpu≤n := by unfold Shape.stride at stride; omega
  have he : s.shape.edge≤n := by unfold Shape.stride at stride; omega
  have xg : s.shape.gates≤n := by unfold Shape.stride at stride; omega
  have xc : s.shape.copy≤n := by unfold Shape.stride at stride; omega
  have ht : s.shape.layers*s.shape.track≤n := by unfold Shape.stride at stride; omega
  have tr : s.shape.track≤2*n := Nat.mul_le_mul_left _ he
  have tick : s.shape.ticks≤2*R := by dsimp [R]; omega
  have cl : s.shape.count≤6*R*n := by
    unfold Shape.count
    rw [show s.shape.layers*(s.shape.rows*s.shape.track)=R*(s.shape.layers*s.shape.track) by dsimp [R]; ring]
    have t := Nat.mul_le_mul tick hc
    have l := Nat.mul_le_mul_left R ht
    have e := Nat.mul_le_mul (Nat.sub_le R 1) he
    have h := Nat.mul_le_mul_left R xc
    have g := Nat.mul_le_mul_left R xg
    change _≤6*R*n
    change _≤(2*R)*n at t
    dsimp [R] at e h g l t ⊢
    nlinarith only [e,h,g,l,t]
  have k1 : s.gates≤R*n := Nat.mul_le_mul lanes slots
  have k2 : s.per≤3*R*n := by
    calc
      _ ≤ R*(n*3) := Nat.mul_le_mul lanes (Nat.mul_le_mul_right _ slots)
      _ = _ := by ring
  have k3 : s.tags≤(1+2*n)*(3*R*n) := Nat.mul_le_mul (by omega) k2
  have k4 := Nat.mul_le_mul arcs k3
  have qr := Nat.mul_le_mul lanes stride
  have rs := Nat.mul_le_mul_left R stride
  have rr := Nat.mul_le_mul_left R slots
  have rt := Nat.mul_le_mul_left R tr
  have pr : n≤R*n := Nat.le_mul_of_pos_left n hrows
  have rx : R≤R*n := Nat.le_mul_of_pos_right R hn
  have hdr : s.shape.header≤2*R := by dsimp [R]; omega
  unfold Layout.footprint
  change s.arcs*s.tags≤n*((1+2*n)*(3*R*n)) at k4
  dsimp only [Layout.relays,Layout.bank] at *
  nlinarith only [cl,k1,k2,k3,k4,qr,rs,rr,rt,pr,rx,hdr,lanes,depth,low,hn,hR,slots,stride,lib,
    Nat.zero_le (R*n*n),Nat.zero_le (R*n*n*n)]

end ThreeFlat.RAM.TraceBucketAtom

end OAI
