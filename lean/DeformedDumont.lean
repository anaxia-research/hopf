/-
  Finite certificates for "Deformed Dumont Permutations, First Letters and Graphical Shi Regions".
  Lean 4 core, no Mathlib. Every theorem is a finite computation checked by
  `native_decide`; the paper proves the general statements.
-/

namespace DeformedDumont

/-- Value `v` may sit at position `i` of an R-D-permutation of `[N]`. -/
def ok (R : List Nat) (i v : Nat) : Bool :=
  if i % 2 == 0 then decide (v ≤ i)
  else if i == 1 || R.contains i then true
  else decide (i ≤ v)

/-- Independent count: fill positions `i, i+1, …, N` by backtracking.
    `mask` records used values; `first = 0` means no first-letter condition. -/
def fill (N : Nat) (R : List Nat) (first : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | fuel+1, i, mask =>
    if i > N then 1 else
    (List.range N).foldl (fun acc w =>
      let v := w + 1
      if (mask >>> v) % 2 == 1 then acc
      else if !ok R i v then acc
      else if i == 1 && first != 0 && v != first then acc
      else acc + fill N R first fuel (i+1) (mask ||| (1 <<< v))) 0

def count (N : Nat) (R : List Nat) : Nat := fill N R 0 (N+1) 1 0
def countFirst (N : Nat) (R : List Nat) (r : Nat) : Nat := fill N R r (N+1) 1 0

/-- One step of the transfer of Theorem 2.1 on a weight vector indexed by h. -/
def get (u : List Int) (h : Int) : Int := if h < 0 then 0 else u.getD h.toNat 0

def stepL (u : List Int) : List Int :=
  (List.range (u.length + 1)).map fun (k : Nat) =>
    let h : Int := (k : Int)
    (h+1) * get u h + get u (h-1)
def stepU (u : List Int) : List Int :=
  (List.range (u.length)).map fun (k : Nat) =>
    let h : Int := (k : Int)
    (h+1) * get u h + (h+1)*(h+1) * get u (h+1)
def stepF (u : List Int) : List Int :=
  (List.range (u.length + 1)).map fun (k : Nat) =>
    let h : Int := (k : Int)
    (2*h+1) * get u h + (h+1)*(h+1) * get u (h+1) + get u (h-1)

/-- Theorem 2.1: the count is the h = 0 entry after scanning t = N, …, 1. -/
def transfer (N : Nat) (R : List Nat) : Int :=
  let u := (List.range N).foldl (fun u k =>
    let t := N - k
    if t % 2 == 0 then stepL u
    else if t == 1 || R.contains t then stepF u
    else stepU u) [1]
  get u 0

def Rj (n j : Nat) : List Nat := (List.range (n - j)).map (fun k => 2*k+1)

/-- G_j(x) through the operator recurrence. -/
def G : Nat → Int → Int
  | 0, _ => 1
  | 1, _ => 1
  | j+2, x => (x+1) * ((x+2) * G (j+1) (x+1) - x * G (j+1) x)

def fact : Nat → Int
  | 0 => 1
  | k+1 => (k+1) * fact k

/-- Theorem A: closed form for |D_{2n-1,j}|. -/
def aClosed (n j : Nat) : Int :=
  if j == 0 then fact n * fact n
  else fact (n-j) * fact (n-j+1) * G j (n-j)

/-- All subsets of odd numbers 3, 5, …, N as lists. -/
def oddSubsets (N : Nat) : List (List Nat) :=
  let odds := (List.range ((N - 1) / 2)).map (fun k => 2*k+3)
  odds.foldl (fun acc x => acc ++ acc.map (fun s => x :: s)) [[]]

/-- Theorem B: the first-letter recurrence, with fuel on the length. -/
def firstRec : Nat → Nat → List Nat → List Int
  | 0, _, _ => []
  | fuel+1, N, R =>
    if N ≤ 1 then [1] else
    let R0 := (R.filter (· ≥ 3)).map (· - 2)
    let b1 : Int := (firstRec fuel (N-2) R0).foldl (· + ·) 0
    let pairs := (List.range ((N-1)/2)).map (· + 1)
    let res := pairs.foldl (fun (acc : List Int × Int) k =>
      let (lst, prev) := acc
      let even := prev
      let Rp := (R.filter (· ≤ 2*k-1)) ++ ((R.filter (· ≥ 2*k+3)).map (· - 2))
      let bp := firstRec fuel (N-2) Rp
      let tot := bp.foldl (· + ·) 0
      let lo := (bp.take (2*k-1)).foldl (· + ·) 0
      let odd := if R.contains (2*k+1) then even + tot else even + (tot - lo) - lo
      (lst ++ [even, odd], odd)) ([b1], b1)
    res.1

def firstCounts (N : Nat) (R : List Nat) : List Int :=
  (List.range N).map (fun k => (countFirst N R (k+1) : Int))

theorem transfer_eq_count_N3 : (oddSubsets 3).all (fun R => transfer 3 R == count 3 R) := by native_decide
theorem transfer_eq_count_N5 : (oddSubsets 5).all (fun R => transfer 5 R == count 5 R) := by native_decide
theorem transfer_eq_count_N7 : (oddSubsets 7).all (fun R => transfer 7 R == count 7 R) := by native_decide
theorem transfer_eq_count_N9 : (oddSubsets 9).all (fun R => transfer 9 R == count 9 R) := by native_decide

theorem closed_eq_count : (List.range 5).all (fun m =>
    let n := m + 1
    (List.range (n+1)).all (fun j => aClosed n j == count (2*n-1) (Rj n j))) := by native_decide

theorem closed_eq_transfer : (List.range 20).all (fun m =>
    let n := m + 1
    (List.range (n+1)).all (fun j => aClosed n j == transfer (2*n-1) (Rj n j))) := by native_decide

theorem closed_recurrence : (List.range 20).all (fun n =>
    (List.range (n+1)).all (fun j =>
      aClosed (n+1) (j+1) == aClosed (n+1) j - ((n-j : Nat) : Int) * ((n-j+1 : Nat) : Int) * aClosed n j)) := by native_decide

theorem G_values : (List.range 7).map (fun j => G (j+1) 0) = [1, 2, 8, 56, 608, 9440, 198272] := by native_decide

theorem firstRec_N3 : (oddSubsets 3).all (fun R => firstRec 10 3 R == firstCounts 3 R) := by native_decide
theorem firstRec_N5 : (oddSubsets 5).all (fun R => firstRec 10 5 R == firstCounts 5 R) := by native_decide
theorem firstRec_N7 : (oddSubsets 7).all (fun R => firstRec 10 7 R == firstCounts 7 R) := by native_decide
theorem firstRec_N9 : (oddSubsets 9).all (fun R => firstRec 10 9 R == firstCounts 9 R) := by native_decide

/-- Lower zone: |D^r_{2n-1,j}| = ⌈r/2⌉ a(n-1,j) for r ≤ 2(n-j). -/
theorem lower_zone : (List.range 4).all (fun m =>
    let n := m + 2
    (List.range n).all (fun i =>
      let j := i + 1
      (List.range (2*(n-j))).all (fun k =>
        let r := k + 1
        (countFirst (2*n-1) (Rj n j) r : Int) == (((r+1)/2 : Nat) : Int) * aClosed (n-1) j))) := by native_decide

/-- Top pair and vanishing last letter for j ≥ 1. -/
theorem top_letters : (List.range 4).all (fun m =>
    let n := m + 2
    (List.range n).all (fun i =>
      let j := i + 1
      (countFirst (2*n-1) (Rj n j) (2*n-1) == 0) &&
      ((countFirst (2*n-1) (Rj n j) (2*n-2) : Int) == aClosed (n-1) (j-1)) &&
      ((countFirst (2*n-1) (Rj n j) (2*n-3) : Int) == aClosed (n-1) (j-1)))) := by native_decide

/-- Pairing: values 2k-1 and 2k give equal first-letter counts, every R, N ≤ 9. -/
theorem pairing : [3,5,7,9].all (fun N => (oddSubsets N).all (fun R =>
    (List.range ((N-1)/2)).all (fun k =>
      countFirst N R (2*k+1) == countFirst N R (2*k+2)))) := by native_decide

end DeformedDumont
