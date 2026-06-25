import CLRSLean.Chapter_08.Section_08_3_Radix_Sort

/-!
# CLRS Section 8.4 - Bucket sort

This file adds a deterministic correctness layer for bucket sort.

The probabilistic expected-time analysis in CLRS depends on a distributional
assumption about the input.  Here we isolate the pure correctness spine:

* distribute values into buckets by a bucket-index function;
* sort each bucket by the final key;
* concatenate buckets in increasing bucket-index order;
* prove the result is ordered and is a permutation of the input.

The theorem is intentionally parametric in the bucket-index function.  A
separate cross-bucket assumption states that every value in an earlier bucket is
at most every value in a later bucket according to the final sort key.
-/

namespace CLRS
namespace Chapter08

universe u v
variable {α : Type u}

/-! ## Bucket-sort model -/

/-- Every element in a list has bucket index strictly below {lit}`upper`. -/
def AllKeysLt (key : α → Nat) (xs : List α) (upper : Nat) : Prop :=
  ∀ x ∈ xs, key x < upper

/--
Bucket sort with an abstract per-bucket sorter.

The buckets are scanned in increasing order `0, 1, ..., bucketCount - 1`.
-/
def bucketSortBy (bucketCount : Nat) (bucketOf : α → Nat)
    (sortBucket : List α → List α) (xs : List α) : List α :=
  (List.range bucketCount).flatMap fun k => sortBucket (bucket bucketOf xs k)

theorem bucketSortBy_succ (bucketCount : Nat) (bucketOf : α → Nat)
    (sortBucket : List α → List α) (xs : List α) :
    bucketSortBy (bucketCount + 1) bucketOf sortBucket xs =
      bucketSortBy bucketCount bucketOf sortBucket xs ++
        sortBucket (bucket bucketOf xs bucketCount) := by
  simp [bucketSortBy, List.range_succ, List.flatMap_append]

theorem orderedBy_of_pairwise {key : α → Nat} :
    ∀ {xs : List α}, xs.Pairwise (fun x y => key x ≤ key y) →
      OrderedBy key xs
  | [], _ => by
      trivial
  | [_], _ => by
      trivial
  | x :: y :: ys, h => by
      cases h with
      | cons hhead htail =>
          exact ⟨hhead y (by simp), orderedBy_of_pairwise htail⟩

theorem flatMap_perm_of_forall {β : Type v} (ks : List β)
    (f g : β → List α)
    (h : ∀ k ∈ ks, (f k).Perm (g k)) :
    (ks.flatMap f).Perm (ks.flatMap g) := by
  induction ks with
  | nil =>
      simp
  | cons k ks ih =>
      simp at h ⊢
      exact List.Perm.append h.1 (ih h.2)

theorem bucketSortBy_perm_bucket_scan (bucketCount : Nat)
    (bucketOf : α → Nat) (sortBucket : List α → List α) (xs : List α)
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys) :
    (bucketSortBy bucketCount bucketOf sortBucket xs).Perm
      ((List.range bucketCount).flatMap fun k => bucket bucketOf xs k) := by
  unfold bucketSortBy
  apply flatMap_perm_of_forall
  intro k _hk
  exact hsort_perm _

theorem bucketSortBy_allKeysLt (bucketCount : Nat) (bucketOf : α → Nat)
    (sortBucket : List α → List α) (xs : List α)
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys) :
    AllKeysLt bucketOf (bucketSortBy bucketCount bucketOf sortBucket xs)
      bucketCount := by
  intro x hx
  rw [bucketSortBy, List.mem_flatMap] at hx
  rcases hx with ⟨k, hk_range, hx_sort⟩
  have hx_bucket : x ∈ bucket bucketOf xs k :=
    (hsort_perm (bucket bucketOf xs k)).mem_iff.mp hx_sort
  have hxkey : bucketOf x = k := (mem_bucket_iff.mp hx_bucket).2
  exact hxkey ▸ List.mem_range.mp hk_range

theorem bucketSortBy_ordered (bucketCount : Nat)
    (bucketOf rank : α → Nat) (sortBucket : List α → List α) (xs : List α)
    (hsort_ordered :
      ∀ k, OrderedBy rank (sortBucket (bucket bucketOf xs k)))
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys)
    (hcross : ∀ {x y : α}, bucketOf x < bucketOf y → rank x ≤ rank y) :
    OrderedBy rank (bucketSortBy bucketCount bucketOf sortBucket xs) := by
  induction bucketCount with
  | zero =>
      simp [bucketSortBy, OrderedBy]
  | succ bucketCount ih =>
      rw [bucketSortBy_succ]
      refine orderedBy_append_of_rel ih (hsort_ordered bucketCount) ?_
      intro x hx y hy
      have hxlt :
          bucketOf x < bucketCount :=
        bucketSortBy_allKeysLt bucketCount bucketOf sortBucket xs hsort_perm x hx
      have hy_bucket : y ∈ bucket bucketOf xs bucketCount :=
        (hsort_perm (bucket bucketOf xs bucketCount)).mem_iff.mp hy
      have hykey : bucketOf y = bucketCount :=
        (mem_bucket_iff.mp hy_bucket).2
      exact hcross (by simpa [hykey] using hxlt)

theorem bucketSortBy_perm [DecidableEq α] (bucketCount : Nat)
    (bucketOf : α → Nat) (sortBucket : List α → List α) (xs : List α)
    (hxs : AllKeysLt bucketOf xs bucketCount)
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys) :
    (bucketSortBy bucketCount bucketOf sortBucket xs).Perm xs := by
  cases bucketCount with
  | zero =>
      have hnil : xs = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        exact Nat.not_lt_zero _ (hxs x hx)
      simp [bucketSortBy, hnil]
  | succ maxKey =>
      have hscan :
          (bucketSortBy (maxKey + 1) bucketOf sortBucket xs).Perm
            (countingSortBy maxKey bucketOf xs) := by
        have hperm_scan :=
          bucketSortBy_perm_bucket_scan (maxKey + 1) bucketOf sortBucket xs
            hsort_perm
        simpa [countingSortBy, bucketSortBy] using hperm_scan
      have hle : AllKeysLe bucketOf xs maxKey := by
        intro x hx
        exact Nat.le_of_lt_succ (hxs x hx)
      exact hscan.trans (countingSortBy_perm maxKey bucketOf xs hle)

theorem bucketSortBy_mem_iff [DecidableEq α] (bucketCount : Nat)
    (bucketOf : α → Nat) (sortBucket : List α → List α) (xs : List α)
    (hxs : AllKeysLt bucketOf xs bucketCount)
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys) (x : α) :
    x ∈ bucketSortBy bucketCount bucketOf sortBucket xs ↔ x ∈ xs :=
  (bucketSortBy_perm bucketCount bucketOf sortBucket xs hxs hsort_perm).mem_iff

/-- Reader-facing correctness theorem for abstract deterministic bucket sort. -/
theorem bucketSortBy_correct [DecidableEq α] (bucketCount : Nat)
    (bucketOf rank : α → Nat) (sortBucket : List α → List α) (xs : List α)
    (hxs : AllKeysLt bucketOf xs bucketCount)
    (hsort_ordered :
      ∀ k, OrderedBy rank (sortBucket (bucket bucketOf xs k)))
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys)
    (hcross : ∀ {x y : α}, bucketOf x < bucketOf y → rank x ≤ rank y) :
    OrderedBy rank (bucketSortBy bucketCount bucketOf sortBucket xs) ∧
      (∀ x, x ∈ bucketSortBy bucketCount bucketOf sortBucket xs ↔ x ∈ xs) ∧
      (bucketSortBy bucketCount bucketOf sortBucket xs).Perm xs :=
  ⟨bucketSortBy_ordered bucketCount bucketOf rank sortBucket xs
      hsort_ordered hsort_perm hcross,
    bucketSortBy_mem_iff bucketCount bucketOf sortBucket xs hxs hsort_perm,
    bucketSortBy_perm bucketCount bucketOf sortBucket xs hxs hsort_perm⟩

/-! ## Executable bucket sorter using merge sort inside each bucket -/

/-- Sort one bucket by the final natural-number rank. -/
def sortBucketByRank (rank : α → Nat) (xs : List α) : List α :=
  xs.mergeSort (fun x y => decide (rank x ≤ rank y))

theorem sortBucketByRank_perm (rank : α → Nat) (xs : List α) :
    (sortBucketByRank rank xs).Perm xs := by
  simpa [sortBucketByRank] using
    List.mergeSort_perm xs (fun x y => decide (rank x ≤ rank y))

theorem sortBucketByRank_ordered (rank : α → Nat) (xs : List α) :
    OrderedBy rank (sortBucketByRank rank xs) := by
  apply orderedBy_of_pairwise
  simpa [sortBucketByRank] using
    List.pairwise_mergeSort' (r := fun x y : α => rank x ≤ rank y) xs

/-- Bucket sort whose per-bucket sorter is Lean's verified merge sort. -/
def bucketSortByRank (bucketCount : Nat) (bucketOf rank : α → Nat)
    (xs : List α) : List α :=
  bucketSortBy bucketCount bucketOf (sortBucketByRank rank) xs

/--
Reader-facing correctness theorem for the executable bucket-sort model.

The cross-bucket hypothesis is the deterministic analogue of the CLRS bucket
interval fact: every item in an earlier bucket is no larger than every item in
a later bucket.
-/
theorem bucketSortByRank_correct [DecidableEq α] (bucketCount : Nat)
    (bucketOf rank : α → Nat) (xs : List α)
    (hxs : AllKeysLt bucketOf xs bucketCount)
    (hcross : ∀ {x y : α}, bucketOf x < bucketOf y → rank x ≤ rank y) :
    OrderedBy rank (bucketSortByRank bucketCount bucketOf rank xs) ∧
      (∀ x, x ∈ bucketSortByRank bucketCount bucketOf rank xs ↔ x ∈ xs) ∧
      (bucketSortByRank bucketCount bucketOf rank xs).Perm xs := by
  unfold bucketSortByRank
  exact bucketSortBy_correct bucketCount bucketOf rank (sortBucketByRank rank)
    xs hxs
    (fun k => sortBucketByRank_ordered rank (bucket bucketOf xs k))
    (sortBucketByRank_perm rank)
    hcross

end Chapter08
end CLRS
