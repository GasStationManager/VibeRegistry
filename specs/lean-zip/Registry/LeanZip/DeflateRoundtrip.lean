/-
  # Spec for Unified DEFLATE Roundtrip (kim-em/lean-zip)

  Source: https://github.com/kim-em/lean-zip
  Module: Zip.Spec.DeflateRoundtrip

  Top-level DEFLATE roundtrip theorem: `inflate (deflateRaw data level) = .ok data`,
  plus two structural lemmas about the encoder's output that downstream
  framing proofs (Zlib, Gzip) depend on.

  Unlike VibeRegistry's math-library entries, this spec references impl-defined
  types (ByteArray, deflateRaw, inflate, bytesToBits, decode.goR) directly.
  The VibeRegistry pipeline overlays this Registry tree into the impl's Lake
  project via build_copy.sh, so these imports resolve to the impl's modules
  at the pinned commit.
-/

import Zip.Native.DeflateDynamic
import Zip.Native.Inflate
import Zip.Spec.Deflate

namespace Zip.Native.Deflate

/-- Unified DEFLATE roundtrip: inflate ∘ deflateRaw = identity.
    Generalized to any `maxOutputSize` large enough to hold the input. -/
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size < maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data := by
  sorry

/-- The output of `deflateRaw` decomposes into content bits plus short padding.
    Needed by `inflateRaw_endPos_ge` to establish that the native decoder
    consumes all of the deflated byte array. -/
theorem deflateRaw_pad (data : ByteArray) (level : UInt8) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRaw data level) = contentBits ++ padding ∧
      padding.length < 8 := by
  sorry

/-- For the encoder's output, `decode.goR` returns a short remaining (< 8 bits).
    Connects encoder structure to decoder bit consumption. -/
theorem deflateRaw_goR_pad (data : ByteArray) (level : UInt8) :
    ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (deflateRaw data level)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  sorry

end Zip.Native.Deflate
