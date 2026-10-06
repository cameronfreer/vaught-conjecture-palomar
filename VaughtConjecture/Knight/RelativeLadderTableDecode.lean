/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLadderRankRendering
public import VaughtConjecture.Knight.RungTableRendering

/-! # Exact decoding of every retained padded coordinate

The same installed birth anchor is used before and after decoding. A finite
round trip recovers the entire numerical level table, not just its occupied
field ranks. Thus unused rungs, spare tips and zero shadows are included.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RelativeLadderLayer
open Transform Value ExtOrd
noncomputable section
variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
  (D : CellScheme A) (hA : 0 < A.card) (field : Cell D → X) (fields : Q → X → ExtOrd)

theorem renderWith_decode_normalized (j : ℕ) (a : Q) (p : X → ExtOrd)
    (hp : ∀ x, p x ≠ ⊤) {G : Finset ExtOrd} {H T : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hH : SelfVis j H)
    (hT : PairedSlotDecoder.decode j (PairedSlotEncoding.values p) G H T = H)
    (d : Cell (carrier D hA (X := X) (Q := Q))) :
    PairedSlotDecoder.decode j (PairedSlotEncoding.values p) G H
      (renderWith D hA field fields a (PairedSlotEncoding.normalize j p) T d) =
        renderWith D hA field fields a p H d := by
  let f := PairedSlotIncoming.encoder j (PairedSlotEncoding.values p)
  let g := PairedSlotDecoder.decode j (PairedSlotEncoding.values p) G H
  have hf := PairedSlotIncoming.encoder_bounded j (PairedSlotEncoding.values p)
  have hg : Witness (gTop j) g := PairedSlotDecoder.decode_witness hG hH
  have hinv (x : X) : g (f (p x)) = p x := by
    dsimp only [f, g]
    rw [PairedSlotIncoming.encoder_profile]
    exact PairedSlotDecoder.decode_normalize hG hH hp x
  have he := RungTableRendering.level_decode p hf.mono hg.mono hf.bot hg.bot hinv T
    (rankIndex D hA field fields a d)
  simpa only [renderWith, image, f, g, PairedSlotIncoming.encoder_profile, hT] using he

end
end VaughtConjecture.Knight.RelativeLadderLayer
