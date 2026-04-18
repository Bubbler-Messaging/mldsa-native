//! Rust wrapper around mldsa-native (ML-DSA-87, FIPS 204).
//!
//! Only the derandomized `*_internal` API variants are exposed — callers
//! must supply their own keypair seed and signing randomness. This keeps
//! randomness sourcing in one place (the Bubbler crypto provider) and
//! avoids linking an external `randombytes` symbol into the C build.
//!
//! Signatures produced here are bit-for-bit compatible with the standard
//! `crypto_sign_signature` API invoked with an empty context string,
//! because we supply the same `pre = [0x00, 0x00]` domain-separation
//! prefix that FIPS 204 §5.2 prescribes for pure ML-DSA with empty
//! context.

#![no_std]

/// ML-DSA-87 public key size in bytes (FIPS 204, §5.1).
pub const PUBLIC_KEY_BYTES: usize = 2592;
/// ML-DSA-87 secret key size in bytes.
pub const SECRET_KEY_BYTES: usize = 4896;
/// ML-DSA-87 signature size in bytes.
pub const SIGNATURE_BYTES: usize = 4627;
/// Keygen seed size (level-independent).
pub const SEED_BYTES: usize = 32;
/// Signing randomness size (level-independent).
pub const RND_BYTES: usize = 32;

/// FIPS 204 §5.2 pure-ML-DSA domain-separation prefix for empty context:
/// `[0x00 (pure), 0x00 (ctxlen)]`.
const PURE_EMPTY_CTX_PREFIX: [u8; 2] = [0x00, 0x00];

unsafe extern "C" {
    fn bubbler_mldsa87_keypair_internal(
        pk: *mut u8,
        sk: *mut u8,
        seed: *const u8,
    ) -> core::ffi::c_int;

    fn bubbler_mldsa87_signature_internal(
        sig: *mut u8,
        siglen: *mut usize,
        m: *const u8,
        mlen: usize,
        pre: *const u8,
        prelen: usize,
        rnd: *const u8,
        sk: *const u8,
        externalmu: core::ffi::c_int,
    ) -> core::ffi::c_int;

    fn bubbler_mldsa87_verify_internal(
        sig: *const u8,
        siglen: usize,
        m: *const u8,
        mlen: usize,
        pre: *const u8,
        prelen: usize,
        pk: *const u8,
        externalmu: core::ffi::c_int,
    ) -> core::ffi::c_int;
}

/// Error returned by any mldsa-native API call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MlDsaError(pub i32);

/// Generate an ML-DSA-87 keypair from a caller-supplied 32-byte seed.
///
/// # Errors
///
/// Returns [`MlDsaError`] if the underlying C implementation reports a
/// failure (e.g. a built-in pairwise-consistency test rejected the key).
pub fn keypair_from_seed(
    seed: &[u8; SEED_BYTES],
) -> Result<([u8; PUBLIC_KEY_BYTES], [u8; SECRET_KEY_BYTES]), MlDsaError> {
    let mut pk = [0u8; PUBLIC_KEY_BYTES];
    let mut sk = [0u8; SECRET_KEY_BYTES];
    let rc = unsafe {
        bubbler_mldsa87_keypair_internal(pk.as_mut_ptr(), sk.as_mut_ptr(), seed.as_ptr())
    };
    if rc == 0 {
        Ok((pk, sk))
    } else {
        Err(MlDsaError(rc))
    }
}

/// Sign `message` with hedged randomness `rnd`, producing a FIPS 204
/// pure-ML-DSA signature with empty context.
///
/// When `rnd` is all zero, the signature is deterministic (still
/// standards-compliant). Feeding fresh randomness every call gives the
/// "hedged" variant with better side-channel resilience.
///
/// # Errors
///
/// Returns [`MlDsaError`] on signing failure (e.g. nonce exhaustion —
/// vanishingly rare but flagged by the underlying library).
pub fn sign(
    message: &[u8],
    rnd: &[u8; RND_BYTES],
    sk: &[u8; SECRET_KEY_BYTES],
) -> Result<[u8; SIGNATURE_BYTES], MlDsaError> {
    let mut sig = [0u8; SIGNATURE_BYTES];
    let mut siglen: usize = 0;
    let rc = unsafe {
        bubbler_mldsa87_signature_internal(
            sig.as_mut_ptr(),
            &mut siglen,
            message.as_ptr(),
            message.len(),
            PURE_EMPTY_CTX_PREFIX.as_ptr(),
            PURE_EMPTY_CTX_PREFIX.len(),
            rnd.as_ptr(),
            sk.as_ptr(),
            0,
        )
    };
    if rc != 0 {
        return Err(MlDsaError(rc));
    }
    // ML-DSA-87 signatures are fixed-size (FIPS 204); if the library
    // reports anything else, surface it as a failure rather than silently
    // truncating.
    if siglen != SIGNATURE_BYTES {
        return Err(MlDsaError(-99));
    }
    Ok(sig)
}

/// Verify a FIPS 204 pure-ML-DSA signature over `message` with empty context.
///
/// Returns `true` iff the signature verifies. Any underlying error is
/// treated as a verification failure — signature verification is public,
/// so there is no information-leak concern in collapsing error variants.
#[must_use]
pub fn verify(
    signature: &[u8],
    message: &[u8],
    pk: &[u8; PUBLIC_KEY_BYTES],
) -> bool {
    let rc = unsafe {
        bubbler_mldsa87_verify_internal(
            signature.as_ptr(),
            signature.len(),
            message.as_ptr(),
            message.len(),
            PURE_EMPTY_CTX_PREFIX.as_ptr(),
            PURE_EMPTY_CTX_PREFIX.len(),
            pk.as_ptr(),
            0,
        )
    };
    rc == 0
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;

    #[test]
    fn sign_verify_roundtrip() {
        let seed = [0x11u8; SEED_BYTES];
        let (pk, sk) = keypair_from_seed(&seed).expect("keypair");
        let msg = b"hello, post-quantum world";
        let rnd = [0x22u8; RND_BYTES];
        let sig = sign(msg, &rnd, &sk).expect("sign");
        assert!(verify(&sig, msg, &pk));
    }

    #[test]
    fn verify_rejects_tampered_message() {
        let seed = [0x33u8; SEED_BYTES];
        let (pk, sk) = keypair_from_seed(&seed).expect("keypair");
        let msg = b"original message";
        let rnd = [0x44u8; RND_BYTES];
        let sig = sign(msg, &rnd, &sk).expect("sign");
        assert!(!verify(&sig, b"tampered message", &pk));
    }

    #[test]
    fn deterministic_signing_with_zero_rnd() {
        let seed = [0x55u8; SEED_BYTES];
        let (_pk, sk) = keypair_from_seed(&seed).expect("keypair");
        let msg = b"determinism check";
        let zero_rnd = [0u8; RND_BYTES];
        let sig1 = sign(msg, &zero_rnd, &sk).expect("sign1");
        let sig2 = sign(msg, &zero_rnd, &sk).expect("sign2");
        assert_eq!(sig1, sig2);
    }
}
