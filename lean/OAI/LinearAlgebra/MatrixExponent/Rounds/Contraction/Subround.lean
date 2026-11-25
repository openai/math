import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat.Select
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat.Fanout
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Carry

/-! # Local controller widths with the full border retained -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Assembly History Packing Case Coloring Window
variable {κ : Type} [Field κ] (Q : Gadget κ) (Δ C d B : ℕ)
local notation "I" => Case κ Q.b d B
local notation "E" => e Δ B

theorem seat_factor : Short (fun i : I => 2 ^ (i.n + i.T.scheme.e)) :=
  tiles.short.exp_add spans.short

theorem radius_factor : Short (fun i : I => 2 ^ (Tile.radius i.T.scheme.d)) :=
  (short_const (2 ^ (Tile.radius d))).mono fun i =>
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.add_le_add_right i.h.degree 1))

theorem mask_factor : Short (fun i : I => 2 ^ (Tile.radius i.T.scheme.d + (i.n + 1))) :=
  (radius_factor Q d B).exp_add (child_factor Q d B).short

theorem outgoing : Short (fun i : I => (Window.Outgoing i.T.scheme).width) :=
  Width.vec spans.short (Width.pair Width.bit
    (Width.pair (Width.addr Case.slots.short.of_exp) (Width.addr spans.short.of_exp)))

theorem source_bound : Short (fun i : I => (i.T.Source i.a (b Q)).width) := by
  have hn : Short (fun i : I => 2 ^ i.n) := tiles.short
  have hw := Width.addr (child_factor Q d B).short.of_exp
  have occ := Width.pair hw (outgoing Q d B)
  have mat := Width.pair (Width.vec hn Width.bit)
    (Width.pair (Width.vec hn occ) (Width.vec hn (Width.vec Case.slots.short hw)))
  exact Width.pair (Width.vec hn (Width.addr Case.bits))
    (Width.pair (Width.vec (seat_factor Q d B) (Width.addr (short_const (b Q)))) mat)

theorem count_bound : Short (fun i : I => (i.T.WithCount i.a (b Q)).width) :=
  Width.pair (source_bound Q d B) (Width.vec tiles.short (Width.addr counters))

theorem pollRow_bound : Short (fun i : I => (i.T.PollRow i.a (b Q)).width) :=
  Width.pair Width.bit (source_bound Q d B)

theorem side_bound : Short (fun i : I => (Side.Input (i.n + i.T.scheme.e) (b Q)).width) :=
  Width.vec (seat_factor Q d B) (short_const (Side.Entry (b Q)).width)

theorem supplement_bound : Short (fun i : I => (i.A.Supplement i.a E).width) := by
  have a : Short (fun i : I => i.T.scheme.k) := (short_const 0).mono fun i => (i.h.single).le
  have p := Width.pair Width.bit (Width.pair (Width.addr (hop_factor Q d B).short.of_exp)
    (Width.pair (Width.addr levels.short) (Width.pair (Width.addr a) (Width.addr spans.short.of_exp))))
  have f : Short (fun i : I => i.A.pointer.width) :=
    Width.pair Width.bit (Width.pair (Width.addr levels.short) (Width.addr stations.short.of_exp))
  exact Width.pair (Width.vec (short_const (2 ^ 0)) (Width.vec (short_const (2 ^ E)) p))
    (Width.vec (place_factor Q d B).short f)

abbrev label (i : I) := i.T.Label i.a Δ C (menu Q d B i) E
  (cap (Q.extend i.F) i.A i.v i.positive i.z Δ B) (meter i.L i.z Δ B) (i.A.Supplement i.a E)

theorem label_bound : Short (fun i : I => (label Q Δ C d B i).width) :=
  Width.pair (Width.addr (child_bound Q Δ C d B).bits)
    (Width.pair (Width.addr (meter_bound Q Δ d B).short) (supplement_bound Q Δ d B))

theorem mask_bound : Short (fun i : I => (Tile.mask i.T.scheme.d i.n (i.T.degree i.a Δ C)).width) :=
  Width.vec (mask_factor Q d B) (Width.vec (child_slots Q Δ C d B).short (Width.vec (mask_factor Q d B) Width.bit))

theorem walk_bound : Short (fun i : I => (Walks 8 i.T.scheme.d (i.T.WithCount i.a (b Q))).width) :=
  Width.vec (radius_factor Q d B) (count_bound Q d B)

theorem word_bound : Short (fun i : I => (Tile.word i.T.scheme.d i.a i.n
    (i.T.degree i.a Δ C) (i.T.WithCount i.a (b Q))).width) :=
  Width.pair Width.bit (Width.pair Width.bit (Width.pair (Width.addr groups.short)
    (Width.pair (Width.addr (child_factor Q d B).short.of_exp)
      (Width.pair (mask_bound Q Δ C d B) (walk_bound Q d B)))))

theorem path_factor : Short (fun i : I => 2 ^ ((i.T.scheme.d + 1) * i.n)) := by
  refine (tiles.short.pow (d + 1)).mono fun i => ?_
  rw [← pow_mul, mul_comm i.n]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.succ_le_succ i.h.degree))

theorem tableWidth_bound : Short (fun i : I => i.T.tableWidth) := Case.bits.add (outgoing Q d B)

theorem patch_bound : Short (fun i : I => (Group.Patch ((i.T.scheme.d + 1) * i.n) i.n i.T.count).width) := by
  have hp := path_factor Q d B
  refine ((short_const 1).add (hp.mul ((hp.mul (short_const 2)).add (tiles.short.mul counters)))).mono fun i => ?_
  rw [Group.width_patch]

theorem groupLabels_bound : Short (fun i : I => (Group.Labels i.n).width) :=
  Width.vec tiles.short (Width.addr (child_factor Q d B).short.of_exp)

theorem groupArity_bound : Short (fun i : I => Group.arity ((i.T.scheme.d + 1) * i.n) i.n i.T.count) := by
  have hn : Short (fun i : I => 2 ^ i.n) := tiles.short
  have hs : Short (fun i : I => (Group.Summary i.n).width) :=
    (hn.mul (hn.of_exp.add (hn.mul (child_factor Q d B).short.of_exp))).mono fun i => by rw [Group.width_summary]
  exact (((patch_bound Q d B).add hs).add hn.of_exp).add (groupLabels_bound Q d B)

theorem colors_bound : Short (fun i : I => (i.T.Colors i.a).width) := Width.vec tiles.short Width.bit

theorem vote_bound : Short (fun i : I => (i.T.Vote i.a).width) :=
  Width.vec (child_factor Q d B).short (Width.addr ((seat_factor Q d B).of_exp.add (short_const 1)))

theorem arity_bound : Short (fun i : I => arity (Q.extend i.F) i.A i.L i.v i.positive i.z Δ C B i.r) := by
  have h := child_bound Q Δ C d B
  have g := (((tableWidth_bound Q d B).add (groupArity_bound Q d B)).add
    ((child_factor Q d B).short.of_exp.add (colors_bound Q d B))).add ((pollRow_bound Q d B).add (vote_bound Q d B))
  have mark := (pollRow_bound Q d B).add (side_bound Q d B)
  have issue := (word_bound Q Δ C d B).add (label_bound Q Δ C d B)
  have back := (fresh_bound Q Δ C d B).rebuildWidth (place_factor Q d B).short (hop_factor Q d B).short
  exact ((((g.add mark).add issue).add ((short_const 2).mul h.bits)).add back)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Controller arrays indexed by parent groups and expanded hosts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Assembly Packing Case Coloring Window
variable {κ : Type} [Field κ] (Q : Gadget κ) (Δ C d B : ℕ)
local notation "I" => Case κ Q.b d B

theorem original : Cost (fun i : I => i.T.format.width) := Case.Child.parent.format
theorem attached : Cost (fun i : I => i.A.format.width) := Case.Child.parent.attached Case.labels

theorem expanded {f : I → ℕ} (h : Row f) : Cost (fun i : I => 2 ^ (i.T.size i.a) * f i) :=
  h.expand (child_factor Q d B).short.block

theorem grouped {A : I → Format} (h : Short (fun i => (A i).width)) :
    Cost (fun i : I => (Fmt.groups i.m i.T.scheme.d i.a (A i)).width) :=
  Case.Child.parent.bank (h.block.groups.mono (fun _ => (Format.width_vec ..).le))

theorem counted_bound : Cost (fun i : I => (i.T.Counted i.a (b Q)).width) := grouped Q d B (count_bound Q d B)

theorem poll_bound : Cost (fun i : I => (i.T.Poll i.a (b Q)).width) :=
  Width.pack (original Q d B) (grouped Q d B (source_bound Q d B))

theorem seats_bound : Cost (fun i : I => Fintype.card (i.T.Slots i.a)) := by
  refine (seat_factor Q d B).block.groups.hosts.mono fun i => ?_
  rw [Fintype.card_congr (i.T.seatIndex i.a).symm, Fintype.card_fin, pow_add, pow_add, mul_assoc]

theorem seats_width (Z : Format) :
    Cost (fun i : I => (Fmt.pi (fun _ : i.T.Slots i.a => Z)).width) := by
  refine ((seats_bound Q d B).mul (block_const Z.width)).mono fun i => ?_
  simp only [Fmt.width_pi, Finset.sum_const, Finset.card_univ, smul_eq_mul, le_refl]

theorem candidate_bound : Cost (fun i : I => (i.T.Candidate i.a (b Q)).width) :=
  seats_width Q d B (.addr (b Q))

theorem groups_cost {f : I → ℕ} (hf : Short f) : Cost (fun i : I => 2 ^ (i.m + i.a) * f i) := by
  simpa only [pow_add, mul_assoc] using hf.block.groups.hosts

theorem groups_width {A : I → Format} (h : Short (fun i => (A i).width)) :
    Cost (fun i : I => (Format.vec (i.m + i.a) (A i)).width) :=
  (groups_cost Q d B h).mono fun _ => (Format.width_vec ..).le

theorem status_bound : Cost (fun i : I => (i.T.Status i.a).width) :=
  (expanded Q d B (long_const Format.bit.width).row).mono fun _ => (Format.width_vec ..).le

theorem graph_bound : Cost (fun i : I => (i.T.Graph i.a Δ C).width) := by
  have h := child_bound Q Δ C d B
  exact h.vector (Width.many h.neighbors (Long.row (Width.addr h.address)))

theorem header_bound : Cost (fun i : I => (i.T.ChildHeader i.a Δ C).width) := by
  have h := child_bound Q Δ C d B
  have s : Short (fun _ : I => (Format.bit.pair .bit).width) := short_const _
  exact h.vector (Short.long (Width.pair s (Width.vec h.neighbors s))).row

theorem raw_bound : Cost (fun i : I => (i.T.Raw i.a (b Q) Δ C).width) :=
  Width.pack (status_bound Q d B) (Width.pack (long_const Format.bit.width).row.cost
    (Width.pack (graph_bound Q Δ C d B) (counted_bound Q d B)))

theorem headed_bound : Cost (fun i : I => (i.T.Headed i.a (b Q) Δ C).width) :=
  Width.pack (raw_bound Q Δ C d B) (header_bound Q Δ C d B)

theorem parcel_bound : Row (fun i : I => BatchDescent.Beat.parcel i.T i.r) := by
  have flags : Short (fun i : I => (Group.Flags i.T.scheme.d).width) :=
    Width.vec Case.slots.short (Width.pair Width.bit Width.bit)
  have count : Short (fun i : I => (Format.vec i.n (.addr i.T.count)).width) :=
    Width.vec tiles.short (Width.addr counters)
  exact Width.pack Width.bit.long.row (Width.pack flags.long.row
    (count.block.groups.mono (fun _ => (Format.width_vec ..).le)))

theorem groupInput_bound : Cost (fun i : I => (i.T.groupInput i.a).width) :=
  Case.Child.parent.bank (parcel_bound Q d B)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Layout and header construction with both core and full graph masks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Assembly Packing Case Coloring

variable {κ : Type} [Field κ] (P : Gadget κ) (Δ C d B : ℕ)
local notation "I" => Case κ P.b d B

private theorem childInput_bound : Cost (fun i : I => (Child.Input i.m i.T.scheme.d).width) := by
  have hd : Long (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.short.long
  refine (Mixed.long Case.m (hd.mul ((long_const 1).add hosts))).mono fun i => ?_
  simp only [Child.Input, Format.width_vec, Format.width_pair, Format.width_addr]
  rw [Format.width_bit]

private theorem nav_bound {q : I → ℕ} (h : Short (fun i => 2 ^ (q i))) :
    Cost (fun i : I => i.T.navCost i.a (q i)) := by
  have bits := ((long_const 100).add ((hosts.add (child_factor P d B).short.long.of_exp).add h.long)).pow 201
  exact (((original P d B).add ((groupInput_bound P d B).scale 3)).add
    ((childInput_bound P d B).scale 68)).add (expanded P d B (Long.row bits))

private theorem childCost_bound : Cost (fun i : I => i.T.childCost i.a Δ C) := by
  have h := original P d B
  have s := h.add ((status_bound P d B).scale 34)
  exact (((h.scale 5).add s).add (nav_bound P d B (child_slots P Δ C d B).short)).scale 4

private theorem headerCost_bound : Cost (fun i : I => i.T.headerCost i.a Δ C) := by
  have h := original P d B
  have s := status_bound P d B
  have p := (child_slots P Δ C d B).short
  have q : Short (fun i : I => 2 ^ (Child.nextWidth i.n Δ i.T.scheme.d)) := by
    refine (short_const (2 ^ maxDegree Δ d)).mono fun i => ?_
    refine Nat.pow_le_pow_right (by decide) ?_
    exact Nat.mul_le_mul_right 3 (Nat.add_le_add_right (Nat.add_le_add i.h.degree (min_le_right ..)) 1)
  have bits := ((long_const 100).add (((hosts.add (child_factor P d B).short.long.of_exp).add p.long).add q.long)).pow 16
  have flags : Cost (fun i : I => (Format.vec (i.T.size i.a)
      (.vec (i.T.degree i.a Δ C) .bit)).width) := by
    refine (expanded P d B p.long.row).mono fun i => ?_
    rw [Format.width_vec, Format.width_vec, Format.width_bit, mul_one]
  have h₁ := ((h.scale 5).add (h.add (s.scale 34))).add (h.add (s.scale 2))
  have h₂ := (((h.scale 5).add (nav_bound P d B p)).add (nav_bound P d B q)).add (expanded P d B (Long.row bits))
  have h₃ := (Width.pack (Width.pack s s) flags).add ((header_bound P Δ C d B).scale 34)
  exact (((h.scale 5).add h₁).add h₂).add h₃

private theorem entries_bound : Cost (fun i : I => (i.T.Entries i.a (b P)).width) :=
  seats_width P d B (Side.Entry (b P))

private theorem markCost_bound : Cost (fun i : I => i.T.markCost i.a (b P)) := by
  have p := pollRow_bound P d B
  have s := side_bound P d B
  have x := ((poll_bound P d B).add ((groups_width P d B p).scale 2)).scale 4
  have y := groups_cost P d B (((short_const 1).add p).add s)
  have z := ((groups_width P d B s).add ((entries_bound P d B).scale 2)).scale 4
  exact (x.add y).add z

private theorem layoutCost_bound : Cost (fun i : I => i.T.layoutCost i.a (b P) (BatchDescent.Beat.profile P)) := by
  have hc := seats_bound P d B
  have h : Cost (fun i : I => 2 ^ (i.m + i.a + (i.n + i.T.scheme.e))) := by
    refine hc.mono fun i => ?_
    rw [Fintype.card_congr (i.T.seatIndex i.a).symm, Fintype.card_fin]
  have g : Cost (fun i : I => (Side.Input (i.m + i.a + (i.n + i.T.scheme.e)) (b P)).width) :=
    (h.mul (block_const (Side.Entry (b P)).width)).mono fun _ => (Format.width_vec ..).le
  have mark := (markCost_bound P d B).add (hc.mul (block_const (Branches.charge (b P))))
  exact (mark.add (((entries_bound P d B).add (g.scale 2)).scale 4)).add
    ((h.mul (block_const ((100 + BatchDescent.Beat.profile P) ^ 8))).scale 4)

private theorem rawCost_bound : Cost (fun i : I =>
    i.T.rawCost i.a (b P) Δ C (BatchDescent.Beat.profile P)) := by
  have p := poll_bound P d B
  have c := counted_bound P d B
  have hb : Cost (fun _ : I => Format.bit.width) := (long_const _).row.cost
  have copies := Width.pack (original P d B) (Width.pack p p)
  have fields := Width.pack (Width.pack (status_bound P d B) (graph_bound P Δ C d B)) (Width.pack hb c)
  have x := (p.add (copies.scale 2)).scale 4
  have y := (childCost_bound P Δ C d B).add ((layoutCost_bound P d B).add ((p.add (c.scale 2)).scale 4))
  exact (x.add y).add ((fields.add ((raw_bound P Δ C d B).scale 2)).scale 4)

theorem headedCost_bound : Cost (fun i : I => i.T.headedCost i.a (b P) Δ C (BatchDescent.Beat.profile P)) := by
  have p := poll_bound P d B
  have x := (p.add ((Width.pack p (original P d B)).scale 2)).scale 4
  exact x.add ((rawCost_bound P Δ C d B).add ((headerCost_bound P Δ C d B).scale 4))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Cost of the common grouping and voting circuits over an extension field -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Assembly Packing Case Coloring

variable {κ : Type} [Field κ] (Q : Gadget κ) (Δ C d B : ℕ)
local notation "I" => Case κ Q.b d B

private theorem labels_bound_row : Row (fun i : I => BatchDescent.Beat.labels i.T i.r) :=
  (groupLabels_bound Q d B).block.groups.mono fun _ => (Format.width_vec ..).le

private theorem fields_bound : Cost (fun i : I => (Window.Fields i.T.scheme i.a i.n (b Q)).width) :=
  Width.pack Child.parent.scheme (Width.pack (Child.parent.vector (labels_bound_row Q d B))
    (Width.pack (colors_bound Q d B).long.row.cost (candidate_bound Q d B)))

private theorem patchCost_bound : Cost (fun i : I =>
    let v := BatchDescent.Beat.parcel i.T i.r
    Group.patchCost i.m i.T.scheme.d i.a i.n i.T.count v (i.p.fee (i.m + (i.T.scheme.d + 1) * i.n) v)) := by
  have hp := path_factor Q d B
  have v := parcel_bound Q d B
  have patches := groups_width Q d B (patch_bound Q d B)
  have loads := Child.parent.vector (Width.many hp v)
  have cost := Mixed.long Case.m (((long_const 100).add (hosts.add hp.long)).pow 220)
  exact (((((groupInput_bound Q d B).add patches).add loads).add cost).scale 1000).add (Child.parent.gather hp v)

private theorem election_bound {c w : I → ℕ} (hc : Short (fun i => 2 ^ c i)) (hw : Short w) :
    Cost (fun i : I => 2 ^ c i * (2 ^ (i.m + i.a) * (100 + w i) ^ 5 + (100 + (c i + (w i + (i.m + i.a)))) ^ 42)) := by
  have a := groups_cost Q d B (((short_const 100).add hw).pow 5)
  have j : Long (fun i : I => i.m + i.a) := hosts.add Case.groups.short.long
  have g := ((long_const 100).add (hc.long.of_exp.add (hw.long.add j))).pow 42
  exact (a.add (Long.row g).cost).left hc.block

private theorem groupCost_bound :
    Cost (fun i : I => Group.cost (i.m + i.a) ((i.T.scheme.d + 1) * i.n) i.n i.T.count) := by
  have hn : Short (fun i : I => 2 ^ i.n) := tiles.short
  exact ((groups_cost Q d B ((short_const 1).add (groupArity_bound Q d B))).scale 100).add
    ((election_bound Q d B hn hn.of_exp).scale 4)

private theorem light_bound : Cost (fun i : I => i.T.lightCost i.a (b Q)) := by
  have hc := (colors_bound Q d B).long.row.cost
  have hv := vote_bound Q d B
  have hr := pollRow_bound Q d B
  have hp := poll_bound Q d B
  have polls := groups_width Q d B hr
  have votes := groups_width Q d B hv
  have ht := groups_cost Q d B (((short_const 1).add hr).add hv)
  have field := (child_factor Q d B).short
  have he := election_bound Q d B field ((seat_factor Q d B).of_exp.add (short_const 1))
  have cost := (((hp.add (polls.scale 2)).scale 4).add ht).add (((votes.scale 3).add he).scale 4)
  have hdr := (cost.add (long_const 1).row.cost).add (Long.row field.long.of_exp).cost
  exact (hdr.add hc).add ((Width.pack hp hc).scale 40)

private theorem prepareCost_bound : Cost (fun i : I => prepareCost (Q.extend i.F) i.T i.r i.p) := by
  have hr := Width.pack (original Q d B) (candidate_bound Q d B)
  have hf := fields_bound Q d B
  have elected := groups_width Q d B (groupLabels_bound Q d B)
  have hv := Child.parent.gather Case.slots.short (labels_bound_row Q d B)
  have records := (hf.add (grouped Q d B (source_bound Q d B))).scale 100
  have install : Cost (fun i : I => 2 ^ i.m * 2 ^ i.a * 2 ^ i.n * (1 + i.T.tableWidth)) := by
    refine (groups_cost Q d B (tiles.short.mul ((short_const 1).add (tableWidth_bound Q d B)))).mono fun i => ?_
    rw [pow_add, mul_assoc]
  have gather := (hv.add records).add install
  have setup := (((hr.add (groupInput_bound Q d B)).add elected).add hf).scale 200
  have collect := ((setup.add (patchCost_bound Q d B)).add (groupCost_bound Q d B)).add gather
  exact ((hr.scale 40).add collect).add (light_bound Q d B)

theorem firstCost_bound : Cost (fun i : I => firstCost (Q.extend i.F) i.A Δ C i.r i.p) := by
  have input := Width.pack (attached Q d B) (candidate_bound Q d B)
  have head := Width.pack (attached Q d B) (headed_bound Q Δ C d B)
  exact (((input.add head).scale 1000).add (prepareCost_bound Q d B)).add (headedCost_bound Q Δ C d B)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Cost of transporting and compressing all child labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Assembly Packing Case Coloring Window
variable {κ : Type} [Field κ] (Q : Gadget κ) (Δ C d B : ℕ)
local notation "I" => Case κ Q.b d B
local notation "Y" => fresh Q Δ C d B

private theorem tile_bound : Cost (fun i : I => Tile.cost i.m i.T.scheme.d i.a i.n (i.T.degree i.a Δ C)
    (i.T.WithCount i.a (b Q)) (label Q Δ C d B i)) := by
  have masks := Case.Child.parent.vector (mask_bound Q Δ C d B).long.row
  have body := Width.pack masks (grouped Q d B (walk_bound Q d B))
  have pre := Width.pack (status_bound Q d B) (Width.pack Width.bit.long.row.cost body)
  have work := ((block_const 1).add ((block_const 137).mul (word_bound Q Δ C d B).block)).add
    (label_bound Q Δ C d B).block
  refine ((pre.scale 4).add (expanded Q d B (Block.groups work))).mono fun i => ?_
  rw [Tile.cost, mul_assoc]

private theorem bank_bound : Cost (fun i : I => Tile.bankCost i.m i.T.scheme.d i.a i.n (i.T.degree i.a Δ C)
    (i.T.WithCount i.a (b Q)) (BatchDescent.Beat.walk (Q.extend i.F) i.T i.r)
    (i.p.fee (i.m + i.T.scheme.d) (BatchDescent.Beat.walk (Q.extend i.F) i.T i.r)) (precision i.T Δ C i.r)) := by
  have h := child_bound Q Δ C d B
  have hp : Long (fun i : I => precision i.T Δ C i.r) :=
    (h.address.add (mask_factor Q d B).long).add h.neighbors.long
  have in₁ := Mixed.long Case.m (((long_const 100).add (hosts.add (radius_factor Q d B).long)).pow 20)
  have in₂ := h.cost (Long.row (((long_const 100).add hp).pow 40))
  have read := Case.Child.parent.read Case.slots.short (walk_bound Q d B).block.groups
  exact (((raw_bound Q Δ C d B).scale 24).add ((in₁.add in₂).scale 4)).add (read.scale 9)

private theorem issue_bound : Cost (fun i : I =>
    let t := BatchDescent.Beat.walk (Q.extend i.F) i.T i.r
    i.T.issueCost i.a (b Q) Δ C (menu Q d B i) (e Δ B)
      (cap (Q.extend i.F) i.A i.v i.positive i.z Δ B) (meter i.L i.z Δ B) (i.A.Supplement i.a (e Δ B))
      t (i.p.fee (i.m + i.T.scheme.d) t) (precision i.T Δ C i.r)) := by
  have h := child_bound Q Δ C d B
  have h₀ := headed_bound Q Δ C d B
  have h₁ := Width.pack (graph_bound Q Δ C d B) (header_bound Q Δ C d B)
  have h₂ := raw_bound Q Δ C d B
  have h₃ := h.vector (h.stack (label_bound Q Δ C d B))
  have h₄ := Width.pack h.format (h.vector (h.stack (supplement_bound Q Δ d B)))
  have N := (bank_bound Q Δ C d B).add (tile_bound Q Δ C d B)
  have keep := (h₀.add (h₁.scale 2)).scale 4
  have run := ((h₀.add (h₂.scale 2)).scale 4).add N
  exact ((h₀.scale 20).add (keep.add run)).add (((Width.pack h₁ h₃).add (h₄.scale 2)).scale 4)

theorem secondCost_bound : Cost (fun i : I =>
    secondCost (Q.extend i.F) i.A i.L i.v i.positive i.z Δ C B i.r i.p) := by
  have h := child_bound Q Δ C d B
  have h₄ := Width.pack h.format (h.vector (h.stack (supplement_bound Q Δ d B)))
  have issue := issue_bound Q Δ C d B
  have a := attached Q d B
  have req := h.requests (place_factor Q d B).short (hop_factor Q d B).short
  exact ((a.scale 4).add issue).add (((Width.pack a h₄).add (req.scale 2)).scale 4)

theorem tailCost_bound : Case.Total (fun i : I =>
    i.A.shrinkCost (Y i) (slots i.A i.r) (copies Δ B) i.x i.y i.payload +
      208 * (Attachment.payload i.x i.y i.payload i.m).width + 4 * (i.T.Candidate i.a (b Q)).width) := by
  have h := (fresh_bound Q Δ C d B).shrinkCost (place_factor Q d B).short (copies Δ B)
  exact (h.add (Case.Child.parent.payload.scale 208)).add ((candidate_bound Q d B).total.scale 4)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Supplying both the border labels and the return pointers to the exterior transfer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)
  (s : ∀ q : (frame A L (Q.b * v) z payload Δ C P).state, Poll h q)
  (hd : 0 < Δ) (hc : Δ ≤ C) (hk : 2 ^ (k Δ) ≤ K) (hs : range (T := T) Δ C r ≤ T.scheme.m)

local notation "Y" => raw Q A L v (pos h) z Δ C B r
local notation "N" => next Q A L v (pos h) z Δ C B r
local notation "k'" => slots A r
local notation "p'" => (T.scheme.d + 1)
local notation "R" => requests Q A L v (pos h) z Δ C B r
local notation "U" => out Q A L v (pos h) z Δ C B r
local notation "self" => BatchDescent.Trail.hop T.scheme.d none

abbrev wiring (Δ C : ℕ) := (requests Q A L v (pos h) z Δ C B r).pair
  (out Q A L v (pos h) z Δ C B r).format

def pending (i : Path h s) : (wiring h Δ C).obj :=
  ((swept h s hd hc i).requests, (swept h s hd hc i).result)

def supplyCost (Δ C : ℕ) := secondCost Q A L v (pos h) z Δ C B r p +
  A.sweepCost (raw Q A L v (pos h) z Δ C B r) (slots A r) (T.scheme.d + 1) +
  24 * (requests Q A L v (pos h) z Δ C B r).width + rebuildCost Q A L v (pos h) z Δ C B r p

include hk hs in
theorem supply : ∃ gate : Table F, Processor.arity gate = issueWidth Q A L v (pos h) z Δ C B r ∧
    ∀ {u : ℕ} {W : Set (Table F)}, 3 ≤ u → arity Q A L v (pos h) z Δ C B r ≤ u →
    gate ∈ W → BatchDescent.Snapshot.sweepTable Y ∈ W → A.rebuildGate N k' p' self ∈ W →
    Computes F u W (headed Q A Δ C r) (wiring h Δ C)
      (mid h s) (pending h s hd hc) (fun i => (issued h s hd hc i).sweep_weight)
      (supplyCost h Δ C) := by
  obtain ⟨gate, hw, hn⟩ := second h s hd hc hk hs
  refine ⟨gate, hw, ?_⟩
  intro u W hu fit hg ha hrec
  have start := hn hu fit hg ha
  have decode := rebuild h s hd hc hk hs hu fit hrec
  have keep := Computes.of_map (L := W) (x := fun i => (swept h s hd hc i).requests)
    (Map.circuit hu (Circuit.id F R)) (fun _ => rfl)
  have run := start.comp (keep.pair hu decode)
  simp only [mul_one] at run
  refine run.mono ?_
  unfold supplyCost
  omega

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Composing the selector test, reattachment, bit transport and compaction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)

local notation "a" => (T.scheme.h - r)
local notation "Y" => raw Q A L v (pos h) z Δ C B r
local notation "N" => Template.sweep Y
local notation "U" => A.transport N (slots A r)
local notation "V" => A.shrink N (slots A r) (copies Δ B)
local notation "k'" => slots A r
local notation "p'" => (T.scheme.d + 1)
local notation "D" => Attachment.payload x y payload T.scheme.m
local notation "Z" => T.Candidate a (b Q)
local notation "self" => BatchDescent.Trail.hop T.scheme.d none

variable (Δ C)
def tables (gate : Table F) :=
  insert gate (insert (BatchDescent.Snapshot.sweepTable Y)
    (insert (A.rebuildGate N k' p' self) (insert (A.shrinkGate N k' (copies Δ B))
      (insert (T.markTable a (b Q)) (T.keys a (b Q) (k Δ) P.load Δ C)))))

theorem few (gate : Table F) : (tables Δ C h gate).card ≤ 10 := by
  unfold tables
  iterate 5
    apply (Finset.card_insert_le _ _).trans
    apply Nat.add_le_add_right
  exact T.card_keys ..

def runCost := firstCost Q A Δ C r p + supplyCost h Δ C +
  (A.shrinkCost N k' (copies Δ B) x y payload + 208 * (D).width + 4 * (Z).width)

variable {Δ C} (s : ∀ q : (frame A L (Q.b * v) z payload Δ C P).state, Poll h q)
  (hd : 0 < Δ) (hc : Δ ≤ C)

def Carries (u : ℕ) (W : Set (Table F)) (cost : ℕ) :=
  Computes F u W ((wiring h Δ C).pair D) ((U).port x y payload)
    (fun i : CaseBit h s => (pending h s hd hc i.1, oldBits h s i)) (output h s hd hc) (fun _ => 1) cost

set_option maxHeartbeats 350000 in
theorem controller (hΔ : 3 ≤ Δ) (hg : gain Δ ≤ K) (hk : 2 ^ (k Δ) ≤ K)
    (hs : range (T := T) Δ C r ≤ T.scheme.m) :
    ∃ gate : Table F, ∀ {u cost : ℕ} {W : Set (Table F)}, 3 ≤ u → arity Q A L v (pos h) z Δ C B r ≤ u →
      A.shrinkWidth N k' (copies Δ B) ≤ u → (tables Δ C h gate : Set _) ⊆ W →
      Carries h s hd hc u W cost →
      Transforms F u W (frame A L (Q.b * v) z payload Δ C P)
        (frame V L v z payload (Δ ^ degreePower) (C ^ degreePower) (after L P K Q.ratio 1 σ))
        (runCost Δ C h + cost) := by
  obtain ⟨gate, _, net⟩ := supply h s hd hc hk hs
  refine ⟨gate, ?_⟩
  intro u cost W hu hf hsh hw ship
  simp only [tables, Finset.coe_insert, Set.insert_subset_iff] at hw
  have init := first h hk hs s hu hf hw.2.2.2.2.2 hw.2.2.2.2.1
  have act := net hu hf hw.1 hw.2.1 hw.2.2.1
  have keep := Computes.of_map (L := W) (x := oldBits h s) (Map.circuit hu (Circuit.id F D))
    (fun _ => rfl)
  have run := ((act.restrict Prod.fst).par keep).comp ship
  simp only [mul_one, Function.comp_apply] at run
  have hi : (fun i : CaseBit h s => (mid h s i.1, oldBits h s i)) =
      fun i => start (Q := Q) (r := r) i.1.1 (((s i.1.1).selector (BatchDescent.Beat.choices Q)).write i.1.2)
        i.2.1 i.2.2 := funext fun i => (start_at h s i).symm
  rw [hi] at run
  let desc := selected h s hd hc hΔ hg
  have lift := Transforms.checked hu desc (start (Q := Q) (r := r)) init run
  have result := lift.comp (Contraction.shrink hu hsh hw.2.2.2.1)
  refine result.mono ?_
  unfold runCost
  omega

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Realizing the relocation of the exposed bits of a contracted network -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)
  (s : ∀ q : (frame A L (Q.b * v) z payload Δ C P).state, Poll h q)
  (hd : 0 < Δ) (hc : Δ ≤ C)

local notation "n" => (T.scheme.h - (T.scheme.h - r))
local notation "N" => Template.sweep (raw Q A L v (pos h) z Δ C B r)

theorem ship {W : Set (Table F)} {u : ℕ} (hu : 3 ≤ u) (hm : 1 ≤ T.scheme.m)
    (hw : A.carryWidth N (slots A r) (n + 1) payload ≤ u)
    (gate : A.carryGate N (slots A r) (n + 1) payload ∈ W) :
    Carries h s hd hc u W (A.carryCost N (slots A r) (T.scheme.d + 1) (n + 1) x y payload p) := by
  have hh : 2 ^ (n + 1) * ((payload + 1) * (2 ^ T.scheme.m + 2 ^ (T.scheme.m + (n + 1)))) < 2 ^ p.w := by
    rw [Nat.sub_sub_self h.group]
    exact fanout h
  have hm' : 1 ≤ T.scheme.m + (n + 1) := hm.trans (Nat.le_add_right ..)
  exact Attachment.carry (swept h s hd hc) (fun i => i.1.val) (moved h s hd hc)
    (fun i => i.1.property.2) (fun i => fits h i.1 (s i.1) i.2 hd hc)
    (Match.rowIndex T.scheme.m (n + 1)) (fun _ => rfl) (fun _ _ => rfl)
    (fun i => exterior h i.1 (s i.1) i.2 hd hc) hu hm hm' hh hw gate

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Realization with prescribed arity and cost budgets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)

local notation "n" => (T.scheme.h - (T.scheme.h - r))
local notation "N" => Template.sweep (raw Q A L v (pos h) z Δ C B r)
local notation "Y" => A.shrink N (slots A r) (copies Δ B)

theorem realize (hd : 3 ≤ Δ) (hc : Δ ≤ C) (hg : gain Δ ≤ K) (hk : 2 ^ (k Δ) ≤ K)
    (hs : range (T := T) Δ C r ≤ T.scheme.m) {u : ℕ} (hu : 3 ≤ u) (hm : 1 ≤ T.scheme.m)
    (hf : arity Q A L v (pos h) z Δ C B r ≤ u)
    (hsh : A.shrinkWidth N (slots A r) (copies Δ B) ≤ u)
    (hv : A.carryWidth N (slots A r) (n + 1) payload ≤ u) :
    ∃ W : Finset (Table F), W.card ≤ 11 ∧
      Transforms F u W (frame A L (Q.b * v) z payload Δ C P)
        (frame Y L v z payload (Δ ^ degreePower) (C ^ degreePower) (after L P K Q.ratio 1 σ))
        (runCost Δ C h + A.carryCost N (slots A r) (T.scheme.d + 1) (n + 1) x y payload p) := by
  have hp : 0 < Δ := by omega
  let s (q : (frame A L (Q.b * v) z payload Δ C P).state) := Classical.choice (elect h q hp hc hk)
  obtain ⟨gate, go⟩ := controller h s hp hc hd hg hk hs
  let keys := insert (A.carryGate N (slots A r) (n + 1) payload) (tables Δ C h gate)
  have move := ship h s hp hc (W := (keys : Set _)) hu hm hv (Finset.mem_insert_self ..)
  have run := go (W := (keys : Set _)) hu hf hsh (fun _ h => Finset.mem_insert_of_mem h) move
  exact ⟨keys, (Finset.card_insert_le ..).trans (Nat.add_le_add_right (few Δ C h gate) 1), run⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Cost prior to moving the outer payload -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Case
variable {κ : Type} [Field κ] (Q : Gadget κ) (Δ C d B : ℕ)

local notation "I" => Case κ Q.b d B
local notation "Y" => fresh Q Δ C d B
local notation "M" => plan Q Δ C d B

def subtotal (i : I) :=
  firstCost (Q.extend i.F) i.A Δ C i.r i.p +
  (secondCost (Q.extend i.F) i.A i.L i.v i.positive i.z Δ C B i.r i.p +
    i.A.sweepCost (M i) (slots i.A i.r) (i.T.scheme.d + 1) +
    24 * (i.A.Requests (Y i) (slots i.A i.r) (i.T.scheme.d + 1)).width +
    rebuildCost (Q.extend i.F) i.A i.L i.v i.positive i.z Δ C B i.r i.p) +
  (i.A.shrinkCost (Y i) (slots i.A i.r) (copies Δ B) i.x i.y i.payload +
    208 * (Attachment.payload i.x i.y i.payload i.m).width + 4 * (i.T.Candidate i.a (b Q)).width)

theorem subtotal_bound : Total (subtotal Q Δ C d B) := by
  have s := (fresh_bound Q Δ C d B).requests (place_factor Q d B).short (hop_factor Q d B).short
  have sub := (((secondCost_bound Q Δ C d B).add (sweepCost_bound Q Δ C d B)).add
      (s.scale 24)).add (rebuildCost_bound Q Δ C d B)
  exact (Cost.total ((firstCost_bound Q Δ C d B).add sub)).add (tailCost_bound Q Δ C d B)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Choosing one exponent for all controllers at fixed degrees -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Case

variable {κ : Type} [Field κ] (Q : Gadget κ) (Δ C d B : ℕ)
local notation "I" => Case κ Q.b d B
local notation "Y" => fresh Q Δ C d B

def shipment (i : I) :=
  i.A.carryCost (Y i) (slots i.A i.r) (i.T.scheme.d + 1) (i.n + 1) i.x i.y i.payload i.p

def shippingWidth (i : I) :=
  i.A.carryWidth (Y i) (slots i.A i.r) (i.n + 1) i.payload

structure Adequate (i : I) (H : ℕ) : Prop where
  few : 11 ≤ i.short ^ H
  degree : i.T.degree i.a Δ C ≤ H
  spans : 2 ^ e Δ B ≤ H
  counters : (meter i.L i.z Δ B).count ≤ i.base ^ H
  labels : (Y i).scheme.ℓ + (pack Q Δ C d B i).ℓ ≤ H * (i.T.scheme.ℓ + i.A.ℓ) + i.base ^ H
  arity : Beat.arity (Q.extend i.F) i.A i.L i.v i.positive i.z Δ C B i.r ≤ i.short ^ H
  shrink : i.A.shrinkWidth (Y i) (slots i.A i.r) (copies Δ B) ≤ i.short ^ H
  range : Beat.range (T := i.T) Δ C i.r ≤ i.short ^ H
  carry : shippingWidth Q Δ C d B i ≤ i.short ^ H
  size : subtotal Q Δ C d B i + shipment Q Δ C d B i ≤
    Contraction.size (x := i.x) (y := i.y) i.A i.p i.r i.z i.payload H

theorem sufficient (ha : Short (shippingWidth Q Δ C d B)) (hc : Total (shipment Q Δ C d B)) :
    ∃ H, 0 < H ∧ ∀ i : I, Adequate Q Δ C d B i H := by
  obtain ⟨j₁, h₁⟩ := (meter_bound Q Δ d B).bound
  obtain ⟨j₂, h₂⟩ := labels_bound Q Δ C d B
  obtain ⟨j₃, h₃⟩ := (arity_bound Q Δ C d B).bound
  obtain ⟨j₄, h₄⟩ := (shrinkWidth_bound Q Δ C d B).bound
  obtain ⟨j₅, h₅⟩ := (range_bound Q Δ C d B).bound
  obtain ⟨j₆, h₆⟩ := ha.bound
  obtain ⟨j₇, h₇⟩ := (subtotal_bound Q Δ C d B).add hc
  let H := 11 + maxDegree C d + 2 ^ e Δ B + j₁ + j₂ + j₃ + j₄ + j₅ + j₆ + j₇
  have hp : 0 < 2 ^ e Δ B := by positivity
  have hl : 11 ≤ H := by unfold H; omega
  refine ⟨H, by omega, fun i => ?_⟩
  have raised {n l : ℕ} (hn : 2 ≤ n) (hl : l ≤ H) : n ^ l ≤ n ^ H :=
    Nat.pow_le_pow_right (by omega) hl
  refine ⟨hl.trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left i.short_two H)),
    (child_degree Q Δ C d B i).trans (by unfold H; omega), by unfold H; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (h₁ i).trans (raised i.base_two (by unfold H; omega))
  · have ht : j₂ ≤ H := by unfold H; omega
    exact (h₂ i).trans (Nat.add_le_add (Nat.mul_le_mul_right _ ht) (raised i.base_two ht))
  · exact (h₃ i).trans (raised i.short_two (by unfold H; omega))
  · exact (h₄ i).trans (raised i.short_two (by unfold H; omega))
  · exact (h₅ i).trans (raised i.short_two (by unfold H; omega))
  · exact (h₆ i).trans (raised i.short_two (by unfold H; omega))
  · have ht : j₇ ≤ H := by unfold H; omega
    exact (h₇ i).trans (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left _ (raised i.long_two ht)) (Nat.mul_le_mul_left _ (raised i.block_two ht)))
      (Nat.mul_le_mul_left _ (raised i.outer_two ht)))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Realizing a wire-saving phase with its frozen border -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Assembly Packing
open scoped Classical

variable {κ : Type} [Field κ] (Q : Gadget κ) (Δ C d B : ℕ)

def fixed := 1 + 2 ^ (k Δ) + gain Δ

theorem fixed_pos : 0 < fixed Δ := by unfold fixed; positivity

variable {d B} (u : Case κ Q.b d B)
local notation "G" => Q.extend u.F

private theorem normalized : Input u.A u.L u.P u.p u.r Q.b (Q.b * u.v) u.v u.z u.payload d B u.K u.H u.σ := by
  rw [← u.h.units]
  exact u.h

local notation "N" => Template.sweep (raw G u.A u.L u.v (pos (Q := G) (normalized Q u)) u.z Δ C B u.r)
local notation "Y" => Attachment.shrink u.A N (slots u.A u.r) (copies Δ B)

local notation "n" => (u.T.scheme.h - (u.T.scheme.h - u.r))

-- Explicit equalities keep comparisons of widths from unfolding the
-- station tables in the template over the extension field.
private theorem plan_def : plan Q Δ C d B u = raw G u.A u.L u.v (pos (Q := G) (normalized Q u)) u.z Δ C B u.r :=
  rfl

private theorem fresh_def : fresh Q Δ C d B u = N := congrArg Template.sweep (plan_def Q Δ C u)

private theorem short_width (ha : Adequate Q Δ C d B u u.H) :
    u.A.shrinkWidth N (slots u.A u.r) (copies Δ B) ≤ (short u.A u.r u.z u.payload) ^ u.H :=
  (congrArg (fun J => u.A.shrinkWidth J (slots u.A u.r) (copies Δ B)) (fresh_def Q Δ C u)).symm.trans_le ha.shrink

private theorem combined_width (ha : Adequate Q Δ C d B u u.H) :
    (N).scheme.ℓ + (Y).ℓ ≤ u.H * (u.T.scheme.ℓ + u.A.ℓ) + u.base ^ u.H :=
  (congrArg (fun J => J.scheme.ℓ + (u.A.shrink J (slots u.A u.r) (copies Δ B)).ℓ)
    (fresh_def Q Δ C u)).symm.trans_le ha.labels

private theorem deliver_width (ha : Adequate Q Δ C d B u u.H) :
    u.A.carryWidth N (slots u.A u.r) (n + 1) u.payload ≤ (short u.A u.r u.z u.payload) ^ u.H :=
  (congrArg (fun J => u.A.carryWidth J (slots u.A u.r) (n + 1) u.payload)
    (fresh_def Q Δ C u)).symm.trans_le ha.carry

private theorem expense (ha : Adequate Q Δ C d B u u.H) :
    runCost (Q := G) Δ C (normalized Q u) + u.A.carryCost N (slots u.A u.r) (u.T.scheme.d + 1) (n + 1) u.x u.y u.payload u.p ≤
      size (x := u.x) (y := u.y) u.A u.p u.r u.z u.payload u.H := by
  let bill (J V : Template u.F) :=
    firstCost G u.A Δ C u.r u.p +
      (secondCost G u.A u.L u.v (pos (Q := G) (normalized Q u)) u.z Δ C B u.r u.p +
        u.A.sweepCost J (slots u.A u.r) (u.T.scheme.d + 1) +
        24 * (u.A.Requests V (slots u.A u.r) (u.T.scheme.d + 1)).width +
        rebuildCost G u.A u.L u.v (pos (Q := G) (normalized Q u)) u.z Δ C B u.r u.p) +
      (u.A.shrinkCost V (slots u.A u.r) (copies Δ B) u.x u.y u.payload +
        208 * (Attachment.payload u.x u.y u.payload u.m).width + 4 * (u.T.Candidate u.a (b Q)).width) +
      u.A.carryCost V (slots u.A u.r) (u.T.scheme.d + 1) (n + 1) u.x u.y u.payload u.p
  exact (congrArg₂ bill (plan_def Q Δ C u) (fresh_def Q Δ C u)).symm.trans_le ha.size

private theorem hardware (hd : 3 ≤ Δ) (hc : Δ ≤ C) (hk : fixed Δ ≤ u.K)
    (ha : Adequate Q Δ C d B u u.H) :
    ∃ W : Finset (Table u.F), W.card ≤ (short u.A u.r u.z u.payload) ^ u.H ∧
      Transforms u.F ((short u.A u.r u.z u.payload) ^ u.H) W (frame u.A u.L (Q.b * u.v) u.z u.payload Δ C u.P)
        (frame Y u.L u.v u.z u.payload (Δ ^ degreePower) (C ^ degreePower) (after u.L u.P u.K Q.ratio 1 u.σ))
        (size (x := u.x) (y := u.y) u.A u.p u.r u.z u.payload u.H) := by
  have h := normalized Q u
  have h₁ : 2 ^ (k Δ) ≤ u.K := ((Nat.le_add_left ..).trans (Nat.le_add_right ..)).trans hk
  have h₂ : gain Δ ≤ u.K := (Nat.le_add_left ..).trans hk
  have wid : range (T := u.T) Δ C u.r ≤ u.T.scheme.m := ha.range.trans h.small
  have low : 3 ≤ (short u.A u.r u.z u.payload) ^ u.H := (by decide : 3 ≤ 11).trans ha.few
  have hm : 1 ≤ u.T.scheme.m := ((by decide : 1 ≤ 11).trans ha.few).trans h.small
  obtain ⟨keys, hkeys, run⟩ := realize (Q := G) (normalized Q u) hd hc h₂ h₁ wid low hm ha.arity
    (short_width Q Δ C u ha) (deliver_width Q Δ C u ha)
  have last := run.mono (expense Q Δ C u ha)
  have hr : (G).ratio = Q.ratio := rfl
  rw [hr] at last
  exact ⟨keys, hkeys.trans ha.few, last⟩

theorem build (hd : 3 ≤ Δ) (hc : Δ ≤ C) (hk : fixed Δ ≤ u.K)
    (ha : Adequate Q Δ C d B u u.H) :
    Nonempty (Output u.A u.L u.P u.p u.r (Q.b * u.v) u.v u.z u.payload Δ (Δ ^ degreePower)
      C (C ^ degreePower) u.K u.H Q.ratio 1 u.σ) := by
  have h := normalized Q u
  have hp : 0 < u.K := (fixed_pos Δ).trans_le hk
  obtain ⟨keys, hkeys, run⟩ := hardware Q Δ C u hd hc hk ha
  refine ⟨⟨N, Y, Nat.sub_add_cancel h.group, Nat.le_add_right .., ?_, ha.degree, h.full, rfl,
    ha.spans, ?_, ?_, ha.counters, combined_width Q Δ C u ha, keys, hkeys, run⟩⟩
  · change u.T.scheme.m + (n + 1) ≤ _
    rw [Nat.sub_sub_self h.group]; omega
  · change n + u.A.k ≤ _
    rw [Nat.sub_sub_self h.group]; omega
  · change 2 ^ max u.A.e (e Δ B) ≤ 2 ^ u.A.e + u.H
    rcases le_total u.A.e (e Δ B) with hl|hl
    · rw [max_eq_right hl]
      exact ha.spans.trans (Nat.le_add_left ..)
    · rw [max_eq_left hl]
      exact Nat.le_add_right ..

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Uniform realization of a contraction step over all finite extensions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Beat

theorem subroundRule (κ : Type) [Field κ] : SubroundRule κ := by
  intro Q Δ hd
  refine ⟨fixed Δ, fixed_pos Δ, fun C d B hc => ?_⟩
  obtain ⟨H, hH, fit⟩ := sufficient Q Δ C d B (carryWidth_bound Q Δ C d B) (carrySize_bound Q Δ C d B)
  refine ⟨H, hH, ?_⟩
  intro F _ _ _ x y T A L P p r u v z payload σ h
  have eq := h.units
  subst u
  let i : Case κ Q.b d B := ⟨F, x, y, T, A, L, P, p, r, Q.b * v, v, z, payload, fixed Δ, H, σ, h⟩
  exact build Q Δ C i hd hc le_rfl (fit i)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end
