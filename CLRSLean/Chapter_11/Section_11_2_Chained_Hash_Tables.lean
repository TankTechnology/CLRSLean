import Mathlib

/-!
# CLRS Section 11.2 - Chained hash tables

This section gives a deterministic correctness layer for chained hash tables.
The table is a function from bucket indices to lists of keys.  The hash function
decides the bucket, and insertion conses the key onto that bucket.

Main results:

- Theorem {lit}`bucket_hashInsert_same`: the inserted key appears in its hash
  bucket.
- Theorem {lit}`bucket_hashInsert_other`: buckets with a different index are
  unchanged.
- Theorem {lit}`hashSearch_hashInsert_self`: after insertion, searching for the
  inserted key succeeds.
- Theorem {lit}`hashSearch_hashInsert_iff`: after insertion, searching for any
  query succeeds exactly when it is the inserted key or was already present.

Current gaps:

- This file does not prove expected search time under simple uniform hashing.
  That theorem needs a probability-space model for random keys or hash
  functions.
-/

namespace CLRS
namespace Chapter11

/-! ## Chained table model -/

/-- A chained hash table maps bucket indices to lists of stored keys. -/
abbrev ChainedHashTable (K : Type u) := Nat → List K

/-- Insert a key into the bucket selected by the hash function. -/
def hashInsert (h : K → Nat) (x : K)
    (T : ChainedHashTable K) : ChainedHashTable K :=
  fun i => if i = h x then x :: T i else T i

/-- Search for a key in the bucket selected by its hash value. -/
def hashSearch (h : K → Nat) (T : ChainedHashTable K) (x : K) : Prop :=
  x ∈ T (h x)

/-! ## Deterministic correctness -/

/-- The inserted key appears in its own hash bucket. -/
theorem bucket_hashInsert_same (h : K → Nat) (T : ChainedHashTable K) (x : K) :
    x ∈ hashInsert h x T (h x) := by
  simp [hashInsert]

/-- A bucket with a different index is unchanged by insertion. -/
theorem bucket_hashInsert_other {h : K → Nat} {T : ChainedHashTable K}
    {x : K} {i : Nat} (hi : i ≠ h x) :
    hashInsert h x T i = T i := by
  simp [hashInsert, hi]

/-- After inserting a key, searching for that key succeeds. -/
theorem hashSearch_hashInsert_self (h : K → Nat)
    (T : ChainedHashTable K) (x : K) :
    hashSearch h (hashInsert h x T) x := by
  exact bucket_hashInsert_same h T x

/--
Searching after insertion succeeds exactly when the query is the inserted key or
the query already appeared in its own hash bucket.
-/
theorem hashSearch_hashInsert_iff (h : K → Nat)
    (T : ChainedHashTable K) (x y : K) :
    hashSearch h (hashInsert h y T) x ↔ x = y ∨ hashSearch h T x := by
  by_cases hxy : h x = h y
  · simp [hashSearch, hashInsert, hxy]
  · have hxne : x ≠ y := by
      intro hkey
      exact hxy (by rw [hkey])
    simp [hashSearch, hashInsert, hxy, hxne]

end Chapter11
end CLRS
