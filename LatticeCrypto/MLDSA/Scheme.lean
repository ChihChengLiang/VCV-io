/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Primitives
import VCVio.CryptoFoundations.IdenSchemeWithAbort
import VCVio.OracleComp.Constructions.SampleableType

/-!
# ML-DSA Identification Scheme Core

This file defines the core ML-DSA identification scheme with aborts, following the
proof-level abstraction used in the EasyCrypt formalization (formosa-crypto/dilithium).
The concrete FIPS 204 signing algorithm (with message-dependent hashing and retry counters)
is built on top of this in `LatticeCrypto.MLDSA.Signature`.

## Architecture

The `IdenSchemeWithAbort` type parameters instantiate as follows for ML-DSA:

| IdenSchemeWithAbort | ML-DSA meaning |
|---|---|
| `Stmt` (statement) | `PublicKey` — `(ρ, t₁)` |
| `Wit` (witness) | `SecretKey` — `(ρ, K, tr, s₁, s₂, t₀)` |
| `Commit` (commitment) | `Vector prims.High p.k` — `w₁ = HighBits(Ay)` |
| `PrvState` (state) | `SigningState` — `(y, w)` retained for the respond phase |
| `Chal` (challenge) | `CommitHashBytes p` — the `λ/4`-byte hash `c̃` |
| `Resp` (response) | `RqVec p.l × Vector prims.Hint p.k` — `(z, h)` |

## Separation from FIPS 204

This file models the **proof-level IDS** used in the Fiat-Shamir-with-aborts security argument:

- **Commit** samples `y` uniformly at random, rather than deriving it from message-dependent
  seeds via `ExpandMask(ρ'', κ)`.
- **No message hashing**: the IDS operates without messages; the message enters only through
  the Fiat-Shamir transform.
- **No retry counter**: the IDS commit is a single probabilistic step; retry logic with
  incrementing `κ` is handled by the signing layer.

## References

- EasyCrypt `IDSabort.ec`, `SimplifiedScheme.ec` (formosa-crypto/dilithium)
- NIST FIPS 204, Algorithms 7 and 8 (for the underlying arithmetic)
-/


open OracleComp OracleSpec
open LatticeCrypto TransformOps

namespace MLDSA

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]

/-- The semantic public key: the public seed `ρ` and the power-2 rounded key vector `t₁`. -/
structure PublicKey where
  rho : Bytes 32
  t1 : Vector prims.Power2High p.k

/-- The semantic secret key: includes the expanded public key material for efficient signing. -/
structure SecretKey where
  rho : Bytes 32
  key : Bytes 32
  tr : Bytes 64
  s1 : RqVec p.l
  s2 : RqVec p.k
  t0 : RqVec p.k

/-- The signing state: commitment data retained between commit and respond phases. -/
structure SigningState where
  y : RqVec p.l
  w : RqVec p.k

/-- The public commitment: `w₁ = HighBits(w)`. -/
abbrev Commitment := Vector prims.High p.k

/-- The signature response: the short vector `z` paired with the hint `h`. -/
abbrev Response := RqVec p.l × Vector prims.Hint p.k

/-- Compute `w'_Approx = NTT⁻¹(Â · NTT(z) - NTT(c) · NTT(t₁ · 2^d))` (Algorithm 8, line 9). -/
def computeWApprox (aHat : TqMatrix p.k p.l) (c : ChallengePoly) (z : RqVec p.l)
    (t1 : Vector prims.Power2High p.k) : RqVec p.k :=
  let cHat := nttOps.toHat c
  let zHat := nttOps.hatVec z
  let t1Shifted := prims.power2RoundShiftVec t1
  let t1ShiftedHat := nttOps.hatVec t1Shifted
  let azHat := nttOps.matVecMul aHat zHat
  let ct1Hat := nttOps.scalarVecMul cHat t1ShiftedHat
  nttOps.unhatVec (Vector.zipWith (· - ·) azHat ct1Hat)

/-! ### Key Generation -/

/-- ML-DSA key generation (Algorithm 6), modeled as a deterministic function from seed.

Given a 32-byte seed `ξ`:
1. Expand to `(ρ, ρ', K)` via `H(ξ ‖ k ‖ l, 128)`
2. Generate matrix `Â = ExpandA(ρ)`
3. Generate secret vectors `(s₁, s₂) = ExpandS(ρ')`
4. Compute `t = A·s₁ + s₂`
5. Split `t` into `(t₁, t₀)` via `Power2Round`
6. Compute `tr = H(pkEncode(ρ, t₁), 64)` -/
def keyGenFromSeed (seed : Bytes 32) : PublicKey p prims × SecretKey p :=
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let aHat := prims.expandA rho
  let (s1, s2) := prims.expandS rhoPrime
  let t := aHat * s1 + s2
  let (t1, t0) := prims.power2RoundVec t
  let pk : PublicKey p prims := ⟨rho, t1⟩
  let tr := prims.hashPublicKey rho t1
  let sk : SecretKey p := ⟨rho, key, tr, s1, s2, t0⟩
  (pk, sk)

/-- A key pair is valid when the public and secret keys are consistently derived:
the public seed matches, and `tr` is the hash of the encoded public key. -/
def validKeyPair (pk : PublicKey p prims) (sk : SecretKey p) : Bool :=
  decide (pk.rho = sk.rho ∧ sk.tr = prims.hashPublicKey pk.rho pk.t1)

omit nttOps in
@[simp] theorem validKeyPair_eq_true_iff (pk : PublicKey p prims) (sk : SecretKey p) :
    validKeyPair p prims pk sk = true ↔
      pk.rho = sk.rho ∧ sk.tr = prims.hashPublicKey pk.rho pk.t1 := by
  simp [validKeyPair]

/-! ### Identification Scheme -/

/-- The core identification scheme with aborts for ML-DSA.

- **Commit**: sample `y` uniformly, compute `w = NTT⁻¹(Â · NTT(y))`,
  return `(w₁ = HighBits(w), state = (y, w))`.
- **Respond** (Alg 7, lines 16–30): derive `c = SampleInBall(c̃)`, compute
  `z = y + c·s₁`, check `‖z‖∞ < γ₁ - β` and `‖LowBits(w - c·s₂)‖∞ < γ₂ - β`,
  compute hint `h = MakeHint(-c·t₀, w - c·s₂ + c·t₀)`, check `‖c·t₀‖∞ < γ₂`
  and hint weight `≤ ω`. Return `some (z, h)` on success, `none` on abort.
- **Verify** (Alg 8, lines 8–13): check `‖z‖∞ < γ₁ - β`, reconstruct
  `w'_Approx = Az - c·(t₁·2^d)`, verify `UseHint(h, w'_Approx) = w₁` and
  hint weight `≤ ω`. -/
def identificationScheme
    [DecidableEq prims.High] [SampleableType (RqVec p.l)] :
    IdenSchemeWithAbort
      (PublicKey p prims) (SecretKey p)
      (Commitment p prims) (SigningState p)
      (CommitHashBytes p) (Response p prims)
      (validKeyPair p prims) where
  commit := fun pk _sk => do
    let aHat := prims.expandA pk.rho
    let y ← $ᵗ (RqVec p.l)
    let w := aHat * y
    let w1 := prims.highBitsVec w
    return (w1, ⟨y, w⟩)
  respond := fun _pk sk st cTilde => do
    let c := prims.sampleInBall cTilde
    let cs1 := c • sk.s1
    let cs2 := c • sk.s2
    let z := st.y + cs1
    let r0 := prims.lowBitsVec (st.w - cs2)
    if polyVecNorm z < p.gamma1 - p.beta ∧ polyVecNorm r0 < p.gamma2 - p.beta then do
      let ct0 := c • sk.t0
      let h := prims.makeHintVec (-ct0) (st.w - cs2 + ct0)
      if polyVecNorm ct0 < p.gamma2 ∧ prims.hintWeight h ≤ p.omega then
        return some (z, h)
      else
        return none
    else
      return none
  verify := fun pk w1 cTilde (z, h) =>
    let c := prims.sampleInBall cTilde
    let aHat := prims.expandA pk.rho
    let wApprox := computeWApprox p prims aHat c z pk.t1
    let w1' := prims.useHintVec h wApprox
    decide (polyVecNorm z < p.gamma1 - p.beta) &&
    decide (w1' = w1) &&
    decide (prims.hintWeight h ≤ p.omega)

/-! ### Key Generation Algebraic Properties -/

/-- Keys generated by `keyGenFromSeed` satisfy `validKeyPair`. -/
theorem keyGenFromSeed_validKeyPair (seed : Bytes 32) :
    let (pk, sk) := keyGenFromSeed p prims seed
    validKeyPair p prims pk sk = true := by
  simp [keyGenFromSeed, validKeyPair]

/-- The key generation algebraic identity: `A·z - c·(t₁·2^d) = A·y - c·s₂ + c·t₀`
when `z = y + c·s₁` and the key pair comes from `keyGenFromSeed`.

This is the core identity underlying both signing correctness and the security proof.
It follows from `t = A·s₁ + s₂` (key generation), `t₁·2^d + t₀ = t` (Power2Round),
and NTT linearity. -/
theorem keyGenFromSeed_wApprox_eq {pk : PublicKey p prims} {sk : SecretKey p}
    (h_laws : Primitives.Laws prims nttOps)
    (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) :
    ∀ (c : Rq) (y : RqVec p.l),
      computeWApprox p prims (prims.expandA pk.rho) c (y + c • sk.s1) pk.t1 =
      (prims.expandA pk.rho) * y - c • sk.s2 + c • sk.t0 := by
  intro c y
  set aHat := prims.expandA pk.rho
  simp only [computeWApprox]
  have h_kg : aHat * sk.s1 + sk.s2 = prims.power2RoundShiftVec pk.t1 + sk.t0 := by
    have := hkeygen
    simp [keyGenFromSeed] at this
    obtain ⟨hpk, hsk⟩ := this
    have hrho : pk.rho = (prims.expandSeed seed).1 :=
      congr_arg PublicKey.rho hpk.symm
    have hs1 : sk.s1 = (prims.expandS (prims.expandSeed seed).2.1).1 :=
      congr_arg SecretKey.s1 hsk.symm
    have hs2 : sk.s2 = (prims.expandS (prims.expandSeed seed).2.1).2 :=
      congr_arg SecretKey.s2 hsk.symm
    have ht0 : sk.t0 = (prims.power2RoundVec (aHat * sk.s1 + sk.s2)).2 := by
      rw [hs1, hs2, show aHat = prims.expandA (prims.expandSeed seed).1 from by
        simp [aHat, hrho]]
      exact congr_arg SecretKey.t0 hsk.symm
    have ht1 : pk.t1 = (prims.power2RoundVec (aHat * sk.s1 + sk.s2)).1 := by
      rw [hs1, hs2, show aHat = prims.expandA (prims.expandSeed seed).1 from by
        simp [aHat, hrho]]
      exact congr_arg PublicKey.t1 hpk.symm
    -- now use the vector power2Round roundtrip
    rw [ht1, ht0]
    apply Vector.ext; intro i hi
    simp only [Primitives.power2RoundShiftVec, Primitives.power2RoundVec, Vector.map_map]
    change (aHat * sk.s1 + sk.s2)[i] =
      (Vector.map (prims.power2RoundShift ∘ Prod.fst ∘ prims.power2Round) (aHat * sk.s1 + sk.s2) +
      Vector.map (Prod.snd ∘ prims.power2Round) (aHat * sk.s1 + sk.s2)).get ⟨i, hi⟩
    set A := Vector.map (prims.power2RoundShift ∘ Prod.fst ∘ prims.power2Round) (aHat * sk.s1 + sk.s2)
    set B := Vector.map (Prod.snd ∘ prims.power2Round) (aHat * sk.s1 + sk.s2)
    have h_split : (A + B).get ⟨i, hi⟩ = A.get ⟨i, hi⟩ + B.get ⟨i, hi⟩ := by
      have : (Vector.ofFn (A.get + B.get)).get ⟨i, hi⟩ = A.get ⟨i, hi⟩ + B.get ⟨i, hi⟩ :=
        by simp [Vector.get_ofFn, Pi.add_apply]
      exact this
    rw[h_split]
    unfold A B
    simp only [Vector.get_map, Function.comp]
    exact (h_laws.power2Round_decomp _).symm
  have hatVec_add : ∀ {k} (u v : RqVec k),
    nttOps.hatVec (u + v) = Vector.zipWith nttOps.addHat (nttOps.hatVec u) (nttOps.hatVec v) := by
    intro k u v
    apply Vector.ext; intro i hi
    simp only [LatticeCrypto.TransformOps.hatVec, Vector.getElem_map, Vector.getElem_zipWith]
    -- (u + v)[i] = u[i] + v[i], bridging instAdd_toMathlib
    have h : (u + v)[i]'hi = u[i]'hi + v[i]'hi := by
      have : (Vector.ofFn (u.get + v.get)).get ⟨i, hi⟩ = u.get ⟨i, hi⟩ + v.get ⟨i, hi⟩ :=
        by simp [Vector.get_ofFn, Pi.add_apply]
      exact this
    rw [h]
    exact h_laws.transform.toHat_add u[i] v[i]
  have h1 : matVecMul nttOps aHat (hatVec nttOps sk.s1) =
    hatVec nttOps (prims.power2RoundShiftVec pk.t1 + sk.t0 - sk.s2) := by
    rw[← h_kg]
    change matVecMul nttOps aHat (hatVec nttOps sk.s1) = hatVec nttOps (aHat * sk.s1 + sk.s2 - sk.s2)
    have : aHat * sk.s1 + sk.s2 - sk.s2 = aHat * sk.s1 := by
      apply Vector.ext; intro i hi
      set_option maxRecDepth 1000 in
      have h_cancel : ((aHat * sk.s1 : RqVec p.k) + sk.s2 - sk.s2)[i]'hi =
          (aHat * sk.s1)[i]'hi := by
        rw [Vector.getElem_sub]
        -- (A + B)[i] - B[i] = A[i]
        have h_add : ((aHat * sk.s1 : RqVec p.k) + sk.s2)[i]'hi =
            (aHat * sk.s1)[i]'hi + sk.s2[i]'hi := by
          have : (Vector.ofFn ((aHat * sk.s1 : RqVec p.k).get + sk.s2.get)).get ⟨i, hi⟩ =
              (aHat * sk.s1).get ⟨i, hi⟩ + sk.s2.get ⟨i, hi⟩ :=
            by simp [Vector.get_ofFn, Pi.add_apply]
          exact this   -- bridges instAdd_toMathlib
        rw [h_add, add_sub_cancel_right]
      rw[h_cancel]
    rw[this]
    have hdef : aHat * sk.s1 =
    nttOps.unhatVec (nttOps.matVecMul aHat (nttOps.hatVec sk.s1)) := rfl
    rw[hdef]
    apply Vector.ext; intro i hi
    simp only [LatticeCrypto.TransformOps.hatVec, LatticeCrypto.TransformOps.unhatVec,
           Vector.getElem_map, h_laws.transform.toHat_fromHat _]

  -- NTT⁻¹( Â·NTT(y + c·s₁) − NTT(c)·NTT(t₁·2^d) )
  calc
    unhatVec nttOps (Vector.zipWith (· - ·)
      (matVecMul nttOps aHat (hatVec nttOps (y + c • sk.s1)))
      (scalarVecMul nttOps (toHat c) (hatVec nttOps (prims.power2RoundShiftVec pk.t1))))
  -- = NTT⁻¹( Â·(NTT(y) + NTT(c)·NTT(s₁)) − NTT(c)·NTT(t₁·2^d) )
  _ = unhatVec nttOps (Vector.zipWith (· - ·)
      (Vector.zipWith (addHat coeffRing) (matVecMul nttOps aHat (hatVec nttOps y))
        (matVecMul nttOps aHat (hatVec nttOps (c • sk.s1))))
      (scalarVecMul nttOps (toHat c) (hatVec nttOps (prims.power2RoundShiftVec pk.t1)))) := by
        rw[hatVec_add, matVecMul_add nttOps h_laws.transform]
  -- = NTT⁻¹( Â·NTT(y) + NTT(c)·Â·NTT(s₁) − NTT(c)·NTT(t₁·2^d) )
  _ = unhatVec nttOps (Vector.zipWith (· - ·)
        (Vector.zipWith (addHat coeffRing) (matVecMul nttOps aHat (hatVec nttOps y))
          (scalarVecMul nttOps (toHat c) (matVecMul nttOps aHat (hatVec nttOps sk.s1))))
        (scalarVecMul nttOps (toHat c) (hatVec nttOps (prims.power2RoundShiftVec pk.t1)))) := by
        congr 3
        apply Vector.ext; intro i hi
        have hdef : c • sk.s1 =
          nttOps.unhatVec (nttOps.scalarVecMul (toHat c) (nttOps.hatVec sk.s1)) := rfl
        simp [hdef, matVecMul, scalarVecMul]
        simp only [hatVec, unhatVec, mulHat_comm nttOps h_laws.transform,
           Vector.getElem_map, h_laws.transform.toHat_fromHat]

        sorry

  --   [h_kg: Â·NTT(s₁) = NTT(t₁·2^d + t₀ - s₂)]
  --   [NTT(c)·NTT(t₁·2^d) cancels]

  -- = NTT⁻¹( Â·NTT(y) + NTT(c)·NTT(t₀ - s₂) )
  --   [unhatVec linearity]
  _ = unhatVec nttOps (
         (matVecMul nttOps aHat (hatVec nttOps y)) +
        (scalarVecMul nttOps (toHat c) (hatVec nttOps (sk.t0 - sk.s2)))) := by
        sorry

  -- = NTT⁻¹(Â·NTT(y)) + c·(t₀ - s₂)
  _ = unhatVec nttOps ((matVecMul nttOps aHat (hatVec nttOps y))) + c• (sk.t0 - sk.s2) := by
        sorry
  -- = Â·y + c·t₀ - c·s₂
  _ = aHat * y + c • sk.t0 - c • sk.s2 := by
    simp only [unhatVec, hatVec]
    rw[smul_sub c sk.t0 sk.s2]
    sorry
  -- = aHat * y - c•s2 + c•t0   ✓
  _ = aHat * y - c • sk.s2 + c • sk.t0 := by
    sorry

end MLDSA
