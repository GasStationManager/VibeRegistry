# Sign-off packet — lean-zip

*Generated 2026-08-25 02:55 UTC by `scripts/generate_signoff_packet.py`. Do not edit by hand.*

- **Entry**: `lean-zip`
- **Upstream**: https://github.com/kim-em/lean-zip @ `e76f0813faa2`
- **Lean**: leanprover/lean4:v4.29.1
- **Machine checks**: comparator, nanoda — overall **fail** at 2026-08-25T02:28:25Z
- **Informal statements**: none adopted yet — run `python3 scripts/fetch_blueprint_statements.py entries/lean-zip.toml`

## What you are attesting

The machine checks below establish that the *implementation proves the spec*. They say nothing about whether the spec is the right statement. That is what your sign-off adds, and it is the only part no tool here can do for you.

Sign-off is optional: an entry whose comparator check passes stands on its own as a verified Lean statement. A sign-off says a human read the statement and vouches for it meaning what it claims.

### Checklist

- [ ] The Lean statement says what the informal statement says — same hypotheses,
      same conclusion, same quantifier order.
- [ ] No hypothesis is stronger than it looks (watch for `Nonempty`, finiteness,
      measurability, and typeclass assumptions that quietly rule out the hard case).
- [ ] No conclusion is weaker than it looks (existentials that are trivially
      satisfiable, bounds that hold vacuously).
- [ ] Definitions replicated from the impl mean what their names claim, and do not
      shadow a Mathlib definition of the same name with different content
      (`scripts/check_mathlib_conflicts.py` reports suspected collisions).
- [ ] Universe variables and implicit binders match the impl.
- [ ] The statement is `sorry`-ed: the spec asserts, it does not prove.


---

## `Registry.LeanZip.DeflateRoundtrip`

- Spec file: [`specs/lean-zip/Registry/LeanZip/DeflateRoundtrip.lean`](../specs/lean-zip/Registry/LeanZip/DeflateRoundtrip.lean)
- Implementation module: `Zip.Spec.DeflateRoundtrip`
- Spec file sha256: `173d1974f48940d6…`
- Existing sign-off: **none**

### `Zip.Native.Deflate.inflate_deflateRaw`

*Machine checks: comparator: fail, nanoda: not-reached*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> Unified DEFLATE roundtrip: inflate ∘ deflateRaw = identity.
>     Generalized to any `maxOutputSize` large enough to hold the input.

**Lean statement** (`Registry/LeanZip/DeflateRoundtrip.lean` lines 26–29):

```lean
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size < maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data := by
  sorry
```

### `Zip.Native.Deflate.deflateRaw_pad`

*Machine checks: comparator: fail, nanoda: not-reached*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> The output of `deflateRaw` decomposes into content bits plus short padding.
>     Needed by `inflateRaw_endPos_ge` to establish that the native decoder
>     consumes all of the deflated byte array.

**Lean statement** (`Registry/LeanZip/DeflateRoundtrip.lean` lines 34–38):

```lean
theorem deflateRaw_pad (data : ByteArray) (level : UInt8) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRaw data level) = contentBits ++ padding ∧
      padding.length < 8 := by
  sorry
```

### `Zip.Native.Deflate.deflateRaw_goR_pad`

*Machine checks: comparator: fail, nanoda: not-reached*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> For the encoder's output, `decode.goR` returns a short remaining (< 8 bits).
>     Connects encoder structure to decoder bit consumption.

**Lean statement** (`Registry/LeanZip/DeflateRoundtrip.lean` lines 42–46):

```lean
theorem deflateRaw_goR_pad (data : ByteArray) (level : UInt8) :
    ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (deflateRaw data level)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  sorry
```

---

## Submitting

Open a [sign-off issue](https://github.com/GasStationManager/VibeRegistry/issues/new?template=spec-signoff.yml) for `lean-zip`, listing the spec files you reviewed. A GitHub Action records the sign-off in the entry TOML and marks it stale automatically if the spec files change afterwards.

> 3 declaration(s) have no informal statement adopted: `Zip.Native.Deflate.inflate_deflateRaw`, `Zip.Native.Deflate.deflateRaw_pad`, `Zip.Native.Deflate.deflateRaw_goR_pad`.
